package org.bytefred.ksat.minisat

import org.bytefred.ksat.SatResult
import org.bytefred.ksat.SatSolver
import org.bytefred.ksat.Traceable
import kotlin.math.abs
import kotlin.math.pow

/**
 * Faithful Kotlin port of MiniSat's bare core CDCL solver (MIT, (c) 2003-2010 Niklas Een,
 * Niklas Sorensson). See ../shadow/minisat-c/ for the verbatim upstream Solver.cc
 * (minisat_orig.cc) and the self-contained instrumented reference (minisat_trace.cc).
 *
 * This is a 1:1 translation of the core algorithm so the port can be shadowed against the
 * C reference: same double-precision VSIDS activities, same activity heap with the same
 * VarOrderLt (strictly-greater) comparator and the same tie-break (heap order), same
 * watched-literal propagation, same 1-UIP conflict analysis with deep clause minimization
 * (ccmin_mode = 2), same Luby restarts, same activity-based reduceDB, and full phase
 * saving (phase_saving = 2).
 *
 * Arena translation (per the methodology): MiniSat's RegionAllocator<uint32>/CRef +
 * Clause-with-header layout is replaced by an [IntArray]-backed store [ca] with Int
 * handles (a "CRef" is an index into a parallel set of arrays). Clause literals are packed
 * MiniSat-style ([Lit.x] = var*2 + sign); a literal-indexed array (`watches`) has size 2n.
 *
 * FLOATING POINT: MiniSat's decision heuristic uses `double` activities. Kotlin/JVM `Double`
 * is IEEE-754 the same as C's `double`, and every activity update here is transcribed in the
 * exact same evaluation order as the C reference, so the trace is expected to match at L1
 * (full trace) on these instances. Where a differently-rounded activity could flip a heap
 * tie the shadow test degrades to L2 (event/decision-variable sequence); see the tests.
 *
 * Not idiomatic Kotlin on purpose -- correspondence to the C beats idiom.
 */
/**
 * Precision of the *clause* activity accumulator.
 *
 * Upstream MiniSat stores clause activity in a 32-bit `float` (`Clause::act`), while
 * `cla_inc` and the rescale thresholds are `double`/`float` literals. That 32-bit rounding
 * is part of the solver's observable behaviour: `reduceDB` sorts and prunes learnt clauses
 * by activity, so which clause survives can depend on the rounding. To shadow the C byte-for-
 * byte we must round identically (FLOAT32). For standalone use (e.g. in the game) FLOAT64
 * keeps full precision and may behave slightly differently / faster.
 */
enum class ActivityPrecision { FLOAT32, FLOAT64 }

class MiniSat(
    numVarsHint: Int,
    private val activityPrecision: ActivityPrecision = ActivityPrecision.FLOAT32,
) : SatSolver, Traceable {

    /** Round a clause-activity value to the configured precision (C's `float` vs full double). */
    private fun claRound(x: Double): Double =
        if (activityPrecision == ActivityPrecision.FLOAT32) x.toFloat().toDouble() else x

    // ---- lbool encoding (as MiniSat: 0=True, 1=False, 2=Undef) ----
    private companion object {
        const val L_TRUE: Int = 0
        const val L_FALSE: Int = 1
        const val L_UNDEF: Int = 2
        const val CREF_UNDEF: Int = -1
        const val VAR_UNDEF: Int = -1
        const val LIT_UNDEF: Int = -2   // Lit.x sentinel
    }

    // ---- options (upstream core defaults) ----
    private val varDecay = 0.95
    private val clauseDecay = 0.999
    private val ccminMode = 2
    private val phaseSaving = 2
    private val lubyRestart = true
    private val restartFirst = 100
    private val restartInc = 2.0
    private val learntsizeFactor = 1.0 / 3.0
    private val learntsizeInc = 1.1
    private val learntsizeAdjustStartConfl = 100
    private val learntsizeAdjustInc = 1.5
    private val minLearntsLim = 0

    override var numVars: Int = 0
        private set

    // ---- clause arena (IntArray-backed; CRef = index into these parallel arrays) ----
    // Each clause: literals (packed Lit.x), a size, a learnt flag, a mark, and an activity.
    private var caLits = arrayOfNulls<IntArray>(64)   // clause literals (Lit.x each)
    private var caSize = IntArray(64)
    private var caLearnt = BooleanArray(64)
    private var caMark = IntArray(64)
    private var caAct = DoubleArray(64)               // clause activity (learnts only, like upstream)
    private var caCount = 0

    private fun caEnsure(cap: Int) {
        if (cap <= caLits.size) return
        var n = caLits.size
        while (n < cap) n *= 2
        caLits = caLits.copyOf(n)
        caSize = caSize.copyOf(n)
        caLearnt = caLearnt.copyOf(n)
        caMark = caMark.copyOf(n)
        caAct = caAct.copyOf(n)
    }

    private fun caAlloc(ps: IntArray, len: Int, learnt: Boolean): Int {
        caEnsure(caCount + 1)
        val cr = caCount++
        caLits[cr] = ps.copyOf(len)
        caSize[cr] = len
        caLearnt[cr] = learnt
        caMark[cr] = 0
        caAct[cr] = 0.0
        return cr
    }

    private fun clLit(cr: Int, i: Int): Int = caLits[cr]!![i]
    private fun clSetLit(cr: Int, i: Int, v: Int) { caLits[cr]!![i] = v }
    private fun clSize(cr: Int): Int = caSize[cr]

    // ---- state ----
    private val clauses = IntArrayList()
    private val learnts = IntArrayList()
    private val trail = IntArrayList()      // Lit.x stack
    private val trailLim = IntArrayList()

    private lateinit var activity: DoubleArray
    private lateinit var assigns: IntArray   // lbool per var
    private lateinit var polarity: IntArray  // 0/1 (preferred sign)
    private lateinit var decision: IntArray  // 0/1
    private lateinit var reasonArr: IntArray // CRef per var
    private lateinit var levelArr: IntArray  // decision level per var
    private lateinit var seen: IntArray
    // watches indexed by Lit.x (size 2*numVars); each is a growable list of (cref, blocker)
    private lateinit var watchCref: Array<IntArrayList>
    private lateinit var watchBlk: Array<IntArrayList>

    private var ok = true
    private var claInc = 1.0
    private var varInc = 1.0
    private var qhead = 0
    private var nextVar = 0
    private var conflicts = 0L
    private var decVars = 0

    private var maxLearnts = 0.0
    private var learntsizeAdjustConfl = 0.0
    private var learntsizeAdjustCnt = 0

    private var simpDBAssigns = -1

    // ---- decision heap (Heap<Var,VarOrderLt>) ----
    private val heap = IntArrayList()
    private var hindices = IntArray(0)   // var -> position, -1 if absent

    // ---- trace sink ----
    private var trace: ((String) -> Unit)? = null
    override fun setTraceSink(sink: ((String) -> Unit)?) { trace = sink }
    private inline fun tr(line: String) { trace?.invoke(line) }

    init {
        // Variables are created LAZILY as clauses reference them, exactly like MiniSat's
        // DIMACS reader (Dimacs.h: `while (var >= S.nVars()) S.newVar();`). We deliberately
        // do NOT pre-create numVarsHint variables: a variable that appears in no clause is
        // never created by the C reference, so pre-creating it here would add a phantom
        // decision variable and diverge the trace. numVarsHint is only a capacity hint.
        activity = DoubleArray(0)
        assigns = IntArray(0)
        polarity = IntArray(0)
        decision = IntArray(0)
        reasonArr = IntArray(0)
        levelArr = IntArray(0)
        seen = IntArray(0)
        watchCref = Array(0) { IntArrayList() }
        watchBlk = Array(0) { IntArrayList() }
    }

    // ---- Lit helpers (Lit.x = var*2 + sign) ----
    private fun mkLit(v: Int, sign: Boolean): Int = v + v + if (sign) 1 else 0
    private fun litNeg(x: Int): Int = x xor 1
    private fun litSign(x: Int): Boolean = (x and 1) != 0
    private fun litVar(x: Int): Int = x shr 1
    // signed DIMACS literal for a true Lit.x (internal var v -> DIMACS v+1)
    private fun dimacsOf(x: Int): Int = if (litSign(x)) -(litVar(x) + 1) else (litVar(x) + 1)

    private fun valueVar(v: Int): Int = assigns[v]
    private fun valueLit(x: Int): Int {
        val a = assigns[litVar(x)]
        // lbool ^ bool: flip low bit; if Undef (2) XOR 1 = 3, but MiniSat's lbool== treats
        // any value with bit1 set as Undef, so we must preserve that. Encode via xor on bit0
        // only when defined. Mirror C: (assigns[var] ^ sign) with lbool's custom ==.
        return if (litSign(x)) lboolXor(a) else a
    }
    // lbool ^ true : True(0)->False(1), False(1)->True(0), Undef(2)->3 (still "undef" under ==)
    private fun lboolXor(a: Int): Int = a xor 1
    // equality honoring MiniSat lbool semantics: undef iff bit1 set.
    private fun lboolEq(a: Int, b: Int): Boolean {
        val au = (a and 2) != 0
        val bu = (b and 2) != 0
        return if (au || bu) (au && bu) else a == b
    }
    private fun isTrue(v: Int): Boolean = lboolEq(v, L_TRUE)
    private fun isFalse(v: Int): Boolean = lboolEq(v, L_FALSE)
    private fun isUndef(v: Int): Boolean = (v and 2) != 0

    private fun nVars(): Int = nextVar
    private fun nAssigns(): Int = trail.size
    private fun decisionLevel(): Int = trailLim.size
    private fun reason(v: Int): Int = reasonArr[v]
    private fun level(v: Int): Int = levelArr[v]
    private fun nClauses(): Int = clauses.size

    // ---- heap (Heap.h) ----
    private fun hleft(i: Int) = i * 2 + 1
    private fun hright(i: Int) = (i + 1) * 2
    private fun hparent(i: Int) = (i - 1) shr 1
    private fun lt(xv: Int, yv: Int): Boolean = activity[xv] > activity[yv]  // VarOrderLt
    private fun inHeap(k: Int): Boolean = k < hindices.size && hindices[k] >= 0
    private fun percolateUp(i0: Int) {
        var i = i0
        val x = heap[i]
        var p = hparent(i)
        while (i != 0 && lt(x, heap[p])) {
            heap[i] = heap[p]; hindices[heap[p]] = i
            i = p; p = hparent(p)
        }
        heap[i] = x; hindices[x] = i
    }
    private fun percolateDown(i0: Int) {
        var i = i0
        val x = heap[i]
        while (hleft(i) < heap.size) {
            val child = if (hright(i) < heap.size && lt(heap[hright(i)], heap[hleft(i)])) hright(i) else hleft(i)
            if (!lt(heap[child], x)) break
            heap[i] = heap[child]; hindices[heap[i]] = i
            i = child
        }
        heap[i] = x; hindices[x] = i
    }
    private fun heapDecrease(k: Int) { percolateUp(hindices[k]) }
    private fun heapInsert(k: Int) {
        if (hindices.size <= k) hindices = hindices.copyOf(k + 1).also { for (j in hindices.size until it.size) it[j] = -1 }
        hindices[k] = heap.size
        heap.add(k)
        percolateUp(hindices[k])
    }
    private fun heapRemoveMin(): Int {
        val x = heap[0]
        heap[0] = heap[heap.size - 1]; hindices[heap[0]] = 0
        hindices[x] = -1
        heap.removeLast()
        if (heap.size > 1) percolateDown(0)
        return x
    }
    private fun heapEmpty(): Boolean = heap.size == 0
    private fun insertVarOrder(x: Int) { if (!inHeap(x) && decision[x] == 1) heapInsert(x) }

    // ---- activity ----
    private fun varDecayActivity() { varInc *= (1 / varDecay) }
    private fun varBumpActivity(v: Int, inc: Double) {
        activity[v] += inc
        if (activity[v] > 1e100) {
            for (i in 0 until nVars()) activity[i] *= 1e-100
            varInc *= 1e-100
        }
        if (inHeap(v)) heapDecrease(v)
    }
    private fun varBumpActivity(v: Int) = varBumpActivity(v, varInc)
    private fun claDecayActivity() { claInc *= (1 / clauseDecay) }
    private fun claBumpActivity(cr: Int) {
        // C: c.act += (float)cla_inc  -- the result lands back in a 32-bit float.
        caAct[cr] = claRound(caAct[cr] + claInc)
        // C: if (c.act > 1e20f) { for (..) act *= 1e-20f; cla_inc *= 1e-20; }
        if (caAct[cr] > claRound(1e20)) {
            for (i in 0 until learnts.size) caAct[learnts[i]] = claRound(caAct[learnts[i]] * claRound(1e-20))
            claInc *= 1e-20
        }
    }

    // ---- new variable ----
    private fun newVar(dvar: Boolean): Int {
        val v = nextVar++
        // grow per-var arrays
        watchCref = ensureWatch(watchCref, (v + 1) * 2)
        watchBlk = ensureWatchB(watchBlk, (v + 1) * 2)
        assigns = grow(assigns, v + 1, L_UNDEF)
        reasonArr = grow(reasonArr, v + 1, CREF_UNDEF)
        levelArr = grow(levelArr, v + 1, 0)
        activity = growD(activity, v + 1)
        seen = grow(seen, v + 1, 0)
        polarity = grow(polarity, v + 1, 1)     // preferred true -> negative decision literal
        decision = grow(decision, v + 1, 0)
        numVars = nextVar
        setDecisionVar(v, dvar)
        return v
    }
    private fun setDecisionVar(v: Int, b: Boolean) {
        if (b && decision[v] == 0) decVars++
        else if (!b && decision[v] == 1) decVars--
        decision[v] = if (b) 1 else 0
        insertVarOrder(v)
    }

    private fun grow(a: IntArray, size: Int, pad: Int): IntArray {
        if (a.size >= size) return a
        val b = a.copyOf(size)
        for (i in a.size until size) b[i] = pad
        return b
    }
    private fun growD(a: DoubleArray, size: Int): DoubleArray {
        if (a.size >= size) return a
        return a.copyOf(size)
    }
    private fun ensureWatch(a: Array<IntArrayList>, size: Int): Array<IntArrayList> {
        if (a.size >= size) return a
        return Array(size) { if (it < a.size) a[it] else IntArrayList() }
    }
    private fun ensureWatchB(a: Array<IntArrayList>, size: Int): Array<IntArrayList> {
        if (a.size >= size) return a
        return Array(size) { if (it < a.size) a[it] else IntArrayList() }
    }

    // ---- clause attach/detach ----
    private fun attachClause(cr: Int) {
        val c0 = clLit(cr, 0); val c1 = clLit(cr, 1)
        watchCref[litNeg(c0)].add(cr); watchBlk[litNeg(c0)].add(c1)
        watchCref[litNeg(c1)].add(cr); watchBlk[litNeg(c1)].add(c0)
    }
    private fun detachClause(cr: Int) {
        val c0 = clLit(cr, 0); val c1 = clLit(cr, 1)
        removeWatch(litNeg(c0), cr)
        removeWatch(litNeg(c1), cr)
    }
    private fun removeWatch(litx: Int, cr: Int) {
        val wc = watchCref[litx]; val wb = watchBlk[litx]
        var i = 0
        while (i < wc.size) {
            if (wc[i] == cr) { wc.removeAt(i); wb.removeAt(i); break }
            i++
        }
    }
    private fun removeClause(cr: Int) {
        detachClause(cr)
        if (locked(cr)) reasonArr[litVar(clLit(cr, 0))] = CREF_UNDEF
        caMark[cr] = 1
    }
    private fun locked(cr: Int): Boolean {
        val c0 = clLit(cr, 0)
        return isTrue(valueLit(c0)) && reason(litVar(c0)) != CREF_UNDEF && reason(litVar(c0)) == cr
    }
    private fun satisfied(cr: Int): Boolean {
        for (i in 0 until clSize(cr)) if (isTrue(valueLit(clLit(cr, i)))) return true
        return false
    }

    // ---- enqueue ----
    private fun uncheckedEnqueue(p: Int, from: Int, rc: Char) {
        // assigns[var(p)] = lbool(!sign(p))  == l_True xor sign
        assigns[litVar(p)] = if (litSign(p)) L_FALSE else L_TRUE
        reasonArr[litVar(p)] = from
        levelArr[litVar(p)] = decisionLevel()
        trail.add(p)
        tr("ASSIGN ${dimacsOf(p)} reason=$rc")
    }

    // ---- backtrack ----
    private fun cancelUntil(lvl: Int) {
        if (decisionLevel() > lvl) {
            var c = trail.size - 1
            val limLvl = trailLim[lvl]
            val limLast = trailLim[trailLim.size - 1]
            while (c >= limLvl) {
                val x = litVar(trail[c])
                assigns[x] = L_UNDEF
                if (phaseSaving > 1 || (phaseSaving == 1 && c > limLast))
                    polarity[x] = if (litSign(trail[c])) 1 else 0
                insertVarOrder(x)
                c--
            }
            qhead = limLvl
            trail.shrinkTo(limLvl)
            trailLim.shrinkTo(lvl)
        }
    }
    private fun newDecisionLevel() { trailLim.add(trail.size) }

    // ---- pick branch ----
    private fun pickBranchLit(): Int {
        var next = VAR_UNDEF
        while (next == VAR_UNDEF || !isUndef(valueVar(next)) || decision[next] == 0) {
            if (heapEmpty()) { next = VAR_UNDEF; break }
            else next = heapRemoveMin()
        }
        if (next == VAR_UNDEF) return LIT_UNDEF
        return mkLit(next, polarity[next] == 1)
    }

    // ---- addClause ----
    private fun addClauseInternal(psIn: IntArray, lenIn: Int): Boolean {
        // sort literals ascending by Lit.x
        val ps = psIn.copyOf(lenIn)
        ps.sort()
        var p = LIT_UNDEF
        var i = 0; var j = 0
        while (i < ps.size) {
            val li = ps[i]
            if (isTrue(valueLit(li)) || li == litNeg(p)) return true
            else if (!isFalse(valueLit(li)) && li != p) { ps[j] = li; p = li; j++ }
            i++
        }
        val len = j
        if (len == 0) { ok = false; return false }
        else if (len == 1) {
            uncheckedEnqueue(ps[0], CREF_UNDEF, 'F')
            ok = (propagate() == CREF_UNDEF)
            return ok
        } else {
            val cr = caAlloc(ps, len, false)
            clauses.add(cr)
            attachClause(cr)
        }
        return true
    }

    // ---- propagate ----
    private fun propagate(): Int {
        var confl = CREF_UNDEF
        while (qhead < trail.size) {
            val p = trail[qhead++]
            val wc = watchCref[p]; val wb = watchBlk[p]
            var i = 0; var j = 0
            val end = wc.size
            while (i != end) {
                val blocker = wb[i]
                if (isTrue(valueLit(blocker))) { wc[j] = wc[i]; wb[j] = wb[i]; j++; i++; continue }

                val cr = wc[i]
                val c0 = clLit(cr, 0)
                val falseLit = litNeg(p)
                if (c0 == falseLit) { clSetLit(cr, 0, clLit(cr, 1)); clSetLit(cr, 1, falseLit) }
                i++

                val first = clLit(cr, 0)
                // Watcher w = (cr, first)
                if (first != blocker && isTrue(valueLit(first))) { wc[j] = cr; wb[j] = first; j++; continue }

                var found = false
                var k = 2
                while (k < clSize(cr)) {
                    if (!isFalse(valueLit(clLit(cr, k)))) {
                        clSetLit(cr, 1, clLit(cr, k)); clSetLit(cr, k, falseLit)
                        val nl = litNeg(clLit(cr, 1))
                        watchCref[nl].add(cr); watchBlk[nl].add(first)
                        found = true; break
                    }
                    k++
                }
                if (found) continue

                wc[j] = cr; wb[j] = first; j++
                if (isFalse(valueLit(first))) {
                    confl = cr
                    qhead = trail.size
                    while (i < end) { wc[j] = wc[i]; wb[j] = wb[i]; j++; i++ }
                } else {
                    uncheckedEnqueue(first, cr, 'C')
                }
            }
            wc.shrinkTo(j); wb.shrinkTo(j)
        }
        return confl
    }

    // ---- litRedundant (ccmin_mode 2) ----
    private val analyzeStackI = IntArrayList()
    private val analyzeStackL = IntArrayList()
    private val SEEN_UNDEF = 0
    private val SEEN_SOURCE = 1
    private val SEEN_REMOVABLE = 2
    private val SEEN_FAILED = 3
    private fun litRedundant(p0: Int): Boolean {
        // Mirrors MiniSat's `for (uint32_t i = 1; ; i++)`: the i++ fires at the end of
        // EVERY iteration (including the level-0/removable `continue`). When we descend
        // into a child reason we set i = 0 so the trailing i++ makes it 1 (start at
        // literal index 1). When we pop we restore the saved i, and the trailing i++
        // advances past the element we just finished.
        var p = p0
        var cr = reason(litVar(p))
        analyzeStackI.clear(); analyzeStackL.clear()
        var i = 1
        while (true) {
            if (i < clSize(cr)) {
                val l = clLit(cr, i)
                if (level(litVar(l)) == 0 || seen[litVar(l)] == SEEN_SOURCE || seen[litVar(l)] == SEEN_REMOVABLE) {
                    i++
                    continue
                }
                if (reason(litVar(l)) == CREF_UNDEF || seen[litVar(l)] == SEEN_FAILED) {
                    analyzeStackI.add(0); analyzeStackL.add(p)
                    var s = 0
                    while (s < analyzeStackL.size) {
                        if (seen[litVar(analyzeStackL[s])] == SEEN_UNDEF) {
                            seen[litVar(analyzeStackL[s])] = SEEN_FAILED
                            analyzeToClear.add(analyzeStackL[s])
                        }
                        s++
                    }
                    return false
                }
                analyzeStackI.add(i); analyzeStackL.add(p)
                i = 0; p = l; cr = reason(litVar(p))   // trailing i++ -> i = 1
            } else {
                if (seen[litVar(p)] == SEEN_UNDEF) {
                    seen[litVar(p)] = SEEN_REMOVABLE
                    analyzeToClear.add(p)
                }
                if (analyzeStackL.size == 0) break
                i = analyzeStackI[analyzeStackI.size - 1]
                p = analyzeStackL[analyzeStackL.size - 1]
                cr = reason(litVar(p))
                analyzeStackI.removeLast(); analyzeStackL.removeLast()   // trailing i++ advances
            }
            i++
        }
        return true
    }

    // ---- analyze ----
    private val analyzeToClear = IntArrayList()
    private var outBtlevel = 0
    private fun analyze(conflIn: Int, outLearnt: IntArrayList) {
        var confl = conflIn
        var pathC = 0
        var p = LIT_UNDEF
        outLearnt.clear()
        outLearnt.add(LIT_UNDEF) // room for asserting lit
        var index = trail.size - 1

        do {
            val cr = confl
            if (caLearnt[cr]) claBumpActivity(cr)
            var jj = if (p == LIT_UNDEF) 0 else 1
            while (jj < clSize(cr)) {
                val q = clLit(cr, jj)
                if (seen[litVar(q)] == 0 && level(litVar(q)) > 0) {
                    varBumpActivity(litVar(q))
                    seen[litVar(q)] = 1
                    if (level(litVar(q)) >= decisionLevel()) pathC++
                    else outLearnt.add(q)
                }
                jj++
            }
            while (seen[litVar(trail[index])] == 0) index--
            index--
            p = trail[index + 1]
            confl = reason(litVar(p))
            seen[litVar(p)] = 0
            pathC--
        } while (pathC > 0)
        outLearnt[0] = litNeg(p)

        // simplify
        var i: Int; var j: Int
        analyzeToClear.clear()
        for (t in 0 until outLearnt.size) analyzeToClear.add(outLearnt[t])
        if (ccminMode == 2) {
            i = 1; j = 1
            while (i < outLearnt.size) {
                if (reason(litVar(outLearnt[i])) == CREF_UNDEF || !litRedundant(outLearnt[i]))
                    { outLearnt[j] = outLearnt[i]; j++ }
                i++
            }
        } else if (ccminMode == 1) {
            i = 1; j = 1
            while (i < outLearnt.size) {
                val x = litVar(outLearnt[i])
                if (reason(x) == CREF_UNDEF) { outLearnt[j] = outLearnt[i]; j++ }
                else {
                    val cr = reason(x)
                    var k = 1
                    while (k < clSize(cr)) {
                        if (seen[litVar(clLit(cr, k))] == 0 && level(litVar(clLit(cr, k))) > 0) {
                            outLearnt[j] = outLearnt[i]; j++; break
                        }
                        k++
                    }
                }
                i++
            }
        } else { i = outLearnt.size; j = outLearnt.size }
        outLearnt.shrinkTo(outLearnt.size - (i - j))

        // backtrack level
        if (outLearnt.size == 1) outBtlevel = 0
        else {
            var maxI = 1
            var k = 2
            while (k < outLearnt.size) {
                if (level(litVar(outLearnt[k])) > level(litVar(outLearnt[maxI]))) maxI = k
                k++
            }
            val q = outLearnt[maxI]
            outLearnt[maxI] = outLearnt[1]
            outLearnt[1] = q
            outBtlevel = level(litVar(q))
        }
        for (t in 0 until analyzeToClear.size) seen[litVar(analyzeToClear[t])] = 0
    }

    // ---- reduceDB ----
    private fun reduceDB() {
        tr("REDUCE")
        val extraLim = claInc / learnts.size
        // reduceDB_lt: x precedes y iff  size(x)>2 && (size(y)==2 || act(x)<act(y)).
        // The C reference uses std::stable_sort with exactly this one-directional predicate;
        // we mirror it with a stable insertion sort using the SAME predicate so both sides
        // order "equal" (incomparable) clauses identically. Removed clauses are the first
        // half plus any with activity below extra_lim. NOTE: on very large instances the two
        // stable sorts can still differ for incomparable clauses -> an L1 divergence point at
        // reduceDB; the shadow test then relies on L2/L3 there (documented in the methodology).
        val arr = learnts.toArray()
        fun reduceLt(x: Int, y: Int): Boolean =
            clSize(x) > 2 && (clSize(y) == 2 || caAct[x] < caAct[y])
        // stable insertion sort
        for (a in 1 until arr.size) {
            val key = arr[a]
            var b = a - 1
            while (b >= 0 && reduceLt(key, arr[b])) { arr[b + 1] = arr[b]; b-- }
            arr[b + 1] = key
        }
        var i = 0; var j = 0
        while (i < arr.size) {
            val cr = arr[i]
            if (clSize(cr) > 2 && !locked(cr) && (i < arr.size / 2 || caAct[cr] < extraLim))
                removeClause(cr)
            else { arr[j] = cr; j++ }
            i++
        }
        learnts.clear()
        for (t in 0 until j) learnts.add(arr[t])
    }

    // ---- luby ----
    private fun luby(y: Double, x0: Int): Double {
        var x = x0
        var size = 1; var seq = 0
        while (size < x + 1) { seq++; size = 2 * size + 1 }
        while (size - 1 != x) { size = (size - 1) shr 1; seq--; x %= size }
        return y.pow(seq)
    }

    // ---- simplify ----
    private fun simplify(): Boolean {
        if (!ok || propagate() != CREF_UNDEF) { ok = false; return false }
        if (nAssigns() == simpDBAssigns) return true
        removeSatisfied(learnts)
        removeSatisfied(clauses)
        rebuildOrderHeap()
        simpDBAssigns = nAssigns()
        return true
    }
    private fun removeSatisfied(cs: IntArrayList) {
        var i = 0; var j = 0
        while (i < cs.size) {
            val cr = cs[i]
            if (satisfied(cr)) removeClause(cr)
            else {
                var k = 2
                while (k < clSize(cr)) {
                    if (isFalse(valueLit(clLit(cr, k)))) {
                        clSetLit(cr, k, clLit(cr, clSize(cr) - 1))
                        caSize[cr] = clSize(cr) - 1
                        k--
                    }
                    k++
                }
                cs[j] = cs[i]; j++
            }
            i++
        }
        cs.shrinkTo(j)
    }
    private fun rebuildOrderHeap() {
        val vs = IntArrayList()
        var v = 0
        while (v < nVars()) {
            if (decision[v] == 1 && isUndef(valueVar(v))) vs.add(v)
            v++
        }
        for (i in 0 until heap.size) hindices[heap[i]] = -1
        heap.clear()
        if (hindices.size < nVars()) hindices = hindices.copyOf(nVars()).also { for (j in hindices.size until it.size) it[j] = -1 }
        for (i in 0 until vs.size) { hindices[vs[i]] = i; heap.add(vs[i]) }
        var i = heap.size / 2 - 1
        while (i >= 0) { percolateDown(i); i-- }
    }

    // ---- assumptions (decision literals forced before free search) ----
    // MiniSat's incremental interface: solve_() is given a vector of assumption literals which
    // are made as forced decisions (one per decision level) at the start of search, BEFORE any
    // heuristic branching. If an assumption is already falsified we return UNSAT for this solve
    // (analyzeFinal in upstream also builds the final conflict clause; callers here only need the
    // verdict, so we skip it). After every solve the trail is rolled back to level 0
    // (cancelUntil(0) in solveInternal), so the base clauses stay loaded and the SAME instance can
    // be solved again under different assumptions -- no clause reload.
    private var assumptions: IntArray = IntArray(0)

    // ---- search ----
    private val learntClause = IntArrayList()
    private fun search(nofConflicts: Int): Int { // returns lbool
        var conflictC = 0
        while (true) {
            val confl = propagate()
            if (confl != CREF_UNDEF) {
                tr("CONFLICT")
                conflicts++; conflictC++
                if (decisionLevel() == 0) return L_FALSE
                learntClause.clear()
                analyze(confl, learntClause)
                cancelUntil(outBtlevel)
                if (learntClause.size == 1) {
                    uncheckedEnqueue(learntClause[0], CREF_UNDEF, 'C')
                } else {
                    val cr = caAlloc(learntClause.toArray(), learntClause.size, true)
                    learnts.add(cr)
                    attachClause(cr)
                    claBumpActivity(cr)
                    uncheckedEnqueue(learntClause[0], cr, 'C')
                }
                varDecayActivity()
                claDecayActivity()
                if (--learntsizeAdjustCnt == 0) {
                    learntsizeAdjustConfl *= learntsizeAdjustInc
                    learntsizeAdjustCnt = learntsizeAdjustConfl.toInt()
                    maxLearnts *= learntsizeInc
                }
            } else {
                if (nofConflicts >= 0 && conflictC >= nofConflicts) {
                    cancelUntil(0)
                    return L_UNDEF
                }
                if (decisionLevel() == 0 && !simplify()) return L_FALSE
                if (learnts.size - nAssigns() >= maxLearnts.toInt()) reduceDB()

                // Consume assumptions first (upstream Solver::search). Each becomes a forced
                // decision on its own level; an already-true one is skipped with a dummy level,
                // an already-false one makes this solve UNSAT under the given assumptions.
                var next = LIT_UNDEF
                while (decisionLevel() < assumptions.size) {
                    val p = assumptions[decisionLevel()]
                    if (isTrue(valueLit(p))) {
                        // dummy decision level (already satisfied)
                        newDecisionLevel()
                    } else if (isFalse(valueLit(p))) {
                        // conflicting assumption -> UNSAT for this solve
                        return L_FALSE
                    } else {
                        next = p
                        break
                    }
                }

                if (next == LIT_UNDEF) {
                    next = pickBranchLit()
                    if (next == LIT_UNDEF) return L_TRUE
                }
                newDecisionLevel()
                tr("DECIDE ${dimacsOf(next)}")
                uncheckedEnqueue(next, CREF_UNDEF, 'D')
            }
        }
    }

    private fun solveInternal(): Int { // 0 UNSAT, 1 SAT
        if (!ok) { tr("RESULT UNSAT"); return 0 }
        maxLearnts = nClauses() * learntsizeFactor
        if (maxLearnts < minLearntsLim) maxLearnts = minLearntsLim.toDouble()
        learntsizeAdjustConfl = learntsizeAdjustStartConfl.toDouble()
        learntsizeAdjustCnt = learntsizeAdjustConfl.toInt()
        var status = L_UNDEF
        var currRestarts = 0
        while (status == L_UNDEF) {
            val restBase = if (lubyRestart) luby(restartInc, currRestarts) else restartInc.pow(currRestarts)
            val budget = (restBase * restartFirst).toInt()
            if (currRestarts > 0) tr("RESTART")
            status = search(budget)
            currRestarts++
        }
        // Capture the model BEFORE cancelUntil(0) undoes the search assignments,
        // exactly as MiniSat's solve_ does.
        if (status == L_TRUE) captureModel()
        cancelUntil(0)
        return if (status == L_TRUE) { tr("RESULT SAT"); 1 } else { tr("RESULT UNSAT"); 0 }
    }

    // ---- model ----
    private lateinit var model: IntArray
    private fun captureModel() {
        model = IntArray(nVars())
        for (i in 0 until nVars()) model[i] = valueVar(i)
    }

    // =========================================================================
    // Public SatSolver API
    // =========================================================================
    override fun addClause(literals: IntArray) {
        if (!ok) return
        // translate DIMACS signed literals to internal Lit.x, creating variables lazily
        // (Dimacs.h: `while (var >= nVars()) newVar();`).
        val buf = IntArray(literals.size)
        for (i in literals.indices) {
            val lit = literals[i]
            val v = abs(lit) - 1
            while (v >= nVars()) newVar(true)
            buf[i] = mkLit(v, lit < 0)
        }
        addClauseInternal(buf, buf.size)
    }

    /**
     * Solve the loaded formula UNDER the given [assumptions] (signed DIMACS literals), the standard
     * MiniSat incremental interface. Each assumption is forced as a decision before free search;
     * the base clauses are NOT re-added. After this returns, the trail is rolled back to decision
     * level 0, so the SAME instance can be solved again under different assumptions (or none) on the
     * exact same clause set. On SAT, [valueOf] reflects the model of THIS solve (assumptions applied);
     * on UNSAT the assumptions were jointly inconsistent with the formula.
     *
     * Determinism: this is upstream MiniSat's assumptions mechanism (assumptions consumed in order
     * at the front of the decision stack), so a given clause set + assumptions always yields the
     * same verdict and model. The no-argument [solve] is the assumption-free case (interface default).
     */
    override fun solve(assumptions: IntArray): SatResult {
        // translate signed DIMACS assumption literals to internal Lit.x. Variables referenced only
        // by an assumption (never by a clause) are created lazily, exactly as addClause does, so the
        // assumption can be forced as a decision on a real variable.
        val internal = IntArray(assumptions.size)
        for (i in assumptions.indices) {
            val lit = assumptions[i]
            val v = abs(lit) - 1
            while (v >= nVars()) newVar(true)
            internal[i] = mkLit(v, lit < 0)
        }
        this.assumptions = internal
        val r = try {
            solveInternal()
        } finally {
            this.assumptions = IntArray(0)
        }
        return if (r == 1) SatResult.SAT else SatResult.UNSAT
    }

    override fun valueOf(v: Int): Boolean {
        // v is 1..numVars DIMACS. A variable that appeared in no clause was never created
        // (lazy, like the C reference) and is a don't-care -- report false, matching that a
        // free variable does not need to be true to satisfy the (unaffected) CNF.
        val idx = v - 1
        if (idx < 0 || idx >= model.size) return false
        return model[idx] == L_TRUE
    }
}

/** Minimal growable int list (avoids boxing; mirrors the flat-array style of the C port). */
class IntArrayList {
    private var a = IntArray(16)
    var size = 0
        private set
    fun add(x: Int) { if (size == a.size) a = a.copyOf(a.size * 2); a[size++] = x }
    operator fun get(i: Int): Int = a[i]
    operator fun set(i: Int, v: Int) { a[i] = v }
    fun removeLast() { size-- }
    fun removeAt(i: Int) { for (k in i until size - 1) a[k] = a[k + 1]; size-- }
    fun clear() { size = 0 }
    fun shrinkTo(n: Int) { size = n }
    fun toArray(): IntArray = a.copyOf(size)
}
