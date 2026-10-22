package org.bytefred.ksat.minisat

import org.bytefred.ksat.SatResult
import org.bytefred.ksat.SatSolver
import org.bytefred.ksat.Traceable
import kotlin.math.abs
import kotlin.math.pow

/**
 * Kotlin port of MiniSat's core CDCL solver (`Minisat::Solver`, core/Solver.h + core/Solver.cc)
 * by Manfred Scheucher, 2026. Upstream: github.com/meelgroup/minisat (commit 9a0382d, the
 * maintained fork; its solver code is niklasso/minisat 37dc6c6 plus compile fixes only, no
 * behaviour change); MIT, (c) 2003-2006 Niklas Een, Niklas Sorensson;
 * (c) 2007-2010 Niklas Sorensson. The preprocessing layer simp/SimpSolver is ported in
 * [MiniSatSimp], which extends this class like upstream's `SimpSolver : public Solver`.
 *
 * Translated line by line, including the clause memory layout ([ClauseAllocator] reproduces
 * RegionAllocator<uint32_t> word by word, so CRef values, wasted-memory accounting, garbage
 * collection and relocation are as upstream), the non-stable mtl `sort` in reduceDB, random
 * decisions (drand/irand), user polarities, released/free variables, budgets and interrupts.
 * Options have the upstream defaults (the `opt_*` values of Solver.cc) and are public vars.
 *
 * Static vs. virtual binding: in C++ only `garbageCollect` is virtual. SimpSolver HIDES newVar,
 * releaseVar, addClause_, removeClause, relocAll, solve_ and the solve overloads; calls made from
 * Solver's own code bind statically to the Solver version. Here every such member is `open` and
 * its Solver body lives in a `solverXxx` method; Solver-internal call sites call `solverXxx`
 * explicitly (= `Solver::xxx`), so a [MiniSatSimp] used through its own type behaves exactly as
 * the C++ class hierarchy. Kotlin has no static binding: a [MiniSatSimp] held as [MiniSat] still
 * dispatches addClause/newVar/releaseVar/solve to the SimpSolver versions (C++ would bind the
 * Solver versions through a `Solver&`). `solve_()` is not virtual (as upstream); SimpSolver's
 * `solve_(do_simp, turn_off_simp)` is a separate overload. `uncheckedEnqueue` uses a growing
 * push instead of `push_` (whose `assert(sz < cap)` holds since newVar reserves `capacity(v+1)`).
 *
 * Trace (shadow testing, [Traceable]): exactly the events of the instrumented upstream reference
 * (ksat-extra/shadow/minisat-full/trace.patch), at the same places: ADD/DEL/TRIM (clause database),
 * ASSIGN <lit> reason=F|C|D|P (top-level unit, propagation/learnt, decision, probing level of
 * implies/implied/asymm), DECIDE, CONFLICT, LEARN, RESTART, REDUCE, SIMPLIFY, GC core|simp,
 * RESULT SAT|UNSAT|UNKNOWN, and for [MiniSatSimp] STRENGTHEN, SUBSUME, ELIM and START/END phases.
 *
 * Not ported: printStats() (needs utils/System.cc cpuTime/memUsedPeak), the file-name
 * toDimacs overloads (an [Appendable] variant is provided), ClauseIterator/TrailIterator, and the
 * no-argument `solve()` (its name is taken by [SatSolver.solve]; use `solve(IntVec())`).
 */
open class MiniSat(
    @Suppress("UNUSED_PARAMETER") numVarsHint: Int = 0,
) : SatSolver, Traceable {

    // ---- Mode of operation (Solver.cc options, upstream defaults) ----
    var verbosity: Int = 0
    var varDecay: Double = 0.95
    var clauseDecay: Double = 0.999
    var randomVarFreq: Double = 0.0
    var randomSeed: Double = 91648253.0
    var lubyRestart: Boolean = true
    var ccminMode: Int = 2              // Controls conflict clause minimization (0=none, 1=basic, 2=deep).
    var phaseSaving: Int = 2            // Controls the level of phase saving (0=none, 1=limited, 2=full).
    var rndPol: Boolean = false         // Use random polarities for branching heuristics.
    var rndInitAct: Boolean = false     // Initialize variable activities with a small random value.
    var garbageFrac: Double = 0.20      // The fraction of wasted memory allowed before a garbage collection is triggered.
    var minLearntsLim: Int = 0          // Minimum number to set the learnts limit to.

    var restartFirst: Int = 100         // The initial restart limit.
    var restartInc: Double = 2.0        // The factor with which the restart limit is multiplied in each restart.
    var learntsizeFactor: Double = 1.0 / 3.0 // The intitial limit for learnt clauses is a factor of the original clauses.
    var learntsizeInc: Double = 1.1     // The limit for learnt clauses is multiplied with this factor each restart.

    var learntsizeAdjustStartConfl: Int = 100
    var learntsizeAdjustInc: Double = 1.5

    // ---- Statistics (read-only) ----
    var solves = 0L; protected set
    var starts = 0L; protected set
    var decisions = 0L; protected set
    var rndDecisions = 0L; protected set
    var propagations = 0L; protected set
    var conflicts = 0L; protected set
    var decVars = 0L; protected set
    var numClauses = 0L; protected set
    var numLearnts = 0L; protected set
    var clausesLiterals = 0L; protected set
    var learntsLiterals = 0L; protected set
    var maxLiterals = 0L; protected set
    var totLiterals = 0L; protected set

    // ---- Extra results (read-only) ----
    /** If problem is satisfiable, this vector contains the model (lbool per var). */
    val model = IntVec()
    /** If problem is unsatisfiable (possibly under assumptions), the final conflict clause
     *  expressed in the assumptions. */
    val conflict = LitSet()

    // ---- Solver state ----
    protected val ca = ClauseAllocator()
    protected val clauses = IntVec()        // List of problem clauses.
    protected val learnts = IntVec()        // List of learnt clauses.
    protected val trail = IntVec()          // Assignment stack.
    protected val trailLim = IntVec()       // Separator indices for different decision levels in 'trail'.
    protected val assumptions = IntVec()    // Current set of assumptions provided to solve by the user.

    protected val activity = DoubleVec()    // A heuristic measurement of the activity of a variable.
    protected val assigns = IntVec()        // The current assignments (lbool).
    protected val polarity = IntVec()       // The preferred polarity of each variable (char).
    protected val userPol = IntVec()        // The users preferred polarity of each variable (lbool).
    protected val decision = IntVec()       // Declares if a variable is eligible for selection in the decision heuristic.
    protected val vardataReason = IntVec()  // VarData.reason
    protected val vardataLevel = IntVec()   // VarData.level
    protected val watches = Watches(ca)     // 'watches[lit]' is a list of constraints watching 'lit'.

    protected val orderHeap = IntHeap { x, y -> activity[x] > activity[y] }   // VarOrderLt

    protected var ok = true                 // If FALSE, the constraints are already unsatisfiable.
    protected var claInc = 1.0              // Amount to bump next clause with.
    protected var varInc = 1.0              // Amount to bump next variable with.
    protected var qhead = 0                 // Head of queue (as index into the trail).
    protected var simpDBAssigns = -1        // Number of top-level assignments since last execution of 'simplify()'.
    protected var simpDBProps = 0L          // Remaining number of propagations before next execution of 'simplify()'.
    protected var progressEstimate = 0.0    // Set by 'search()'.
    protected var removeSatisfied = true    // Whether 'simplify' removes satisfied original clauses.
    protected var nextVar = 0               // Next variable to be created.

    protected val releasedVars = IntVec()
    protected val freeVars = IntVec()

    // Temporaries:
    protected val seen = IntVec()
    private val analyzeStackI = IntVec()    // ShrinkStackElem.i
    private val analyzeStackL = IntVec()    // ShrinkStackElem.l
    protected val analyzeToclear = IntVec()
    protected val addTmp = IntVec()

    protected var maxLearnts = 0.0
    protected var learntsizeAdjustConfl = 0.0
    protected var learntsizeAdjustCnt = 0

    // Resource constraints:
    protected var conflictBudget = -1L      // -1 means no budget.
    protected var propagationBudget = -1L   // -1 means no budget.
    protected var asynchInterrupt = false

    // ---- trace sink ----
    private var trace: ((String) -> Unit)? = null
    override fun setTraceSink(sink: ((String) -> Unit)?) { trace = sink }
    protected fun tr(line: String) { trace?.invoke(line) }
    protected val tracing: Boolean get() = trace != null

    /** Signed DIMACS form of a literal (internal var v -> DIMACS v+1), for the trace. */
    protected fun dimacsOf(p: Int): Int = if (litSign(p)) -(litVar(p) + 1) else (litVar(p) + 1)

    /** "<head> : l1 ... lk 0" for clause [cr] (literals in current stored order). */
    protected fun trClause(head: String, cr: Int) {
        val sb = StringBuilder(head).append(" :")
        for (i in 0 until ca.size(cr)) sb.append(' ').append(dimacsOf(ca.lit(cr, i)))
        tr(sb.append(" 0").toString())
    }

    /** "<head> : l1 ... lk 0" for a literal vector. */
    protected fun trLits(head: String, ps: IntVec) {
        val sb = StringBuilder(head).append(" :")
        for (i in 0 until ps.size) sb.append(' ').append(dimacsOf(ps[i]))
        tr(sb.append(" 0").toString())
    }

    /** "ASSIGN <lit> reason=P" for every literal enqueued on the current probing level. */
    protected fun trProbeAssigns() {
        for (k in trailLim.last() until trail.size) tr("ASSIGN ${dimacsOf(trail[k])} reason=P")
    }

    // =========================================================================================
    // Inline methods of Solver.h
    // =========================================================================================

    protected fun reason(x: Int): Int = vardataReason[x]
    protected fun level(x: Int): Int = vardataLevel[x]

    protected fun insertVarOrder(x: Int) {
        if (!orderHeap.inHeap(x) && decision[x] != 0) orderHeap.insert(x)
    }

    protected fun varDecayActivity() { varInc *= (1 / varDecay) }
    protected fun varBumpActivity(v: Int) = varBumpActivity(v, varInc)
    protected fun varBumpActivity(v: Int, inc: Double) {
        activity[v] = activity[v] + inc
        if (activity[v] > 1e100) {
            // Rescale:
            for (i in 0 until nVars()) activity[i] = activity[i] * 1e-100
            varInc *= 1e-100
        }
        // Update order_heap with respect to new activity:
        if (orderHeap.inHeap(v)) orderHeap.decrease(v)
    }

    protected fun claDecayActivity() { claInc *= (1 / clauseDecay) }
    protected fun claBumpActivity(cr: Int) {
        // (c.activity() += cla_inc) > 1e20 : float += double, then the float compared to double 1e20.
        ca.setActivity(cr, (ca.activity(cr).toDouble() + claInc).toFloat())
        if (ca.activity(cr).toDouble() > 1e20) {   // the stored 32-bit float, promoted to double
            // Rescale:
            for (i in 0 until learnts.size)
                ca.setActivity(learnts[i], (ca.activity(learnts[i]).toDouble() * 1e-20).toFloat())
            claInc *= 1e-20
        }
    }

    fun checkGarbage() = checkGarbage(garbageFrac)
    fun checkGarbage(gf: Double) {
        if (ca.wasted().toUInt().toDouble() > ca.size().toUInt().toDouble() * gf)
            garbageCollect()
    }

    // NOTE: enqueue does not set the ok flag! (only public methods do)
    protected fun enqueue(p: Int, from: Int = CREF_UNDEF): Boolean =
        if (!lbEq(valueLit(p), L_UNDEF)) !lbEq(valueLit(p), L_FALSE) else { uncheckedEnqueue(p, from); true }

    fun addClause(ps: IntVec): Boolean { ps.copyTo(addTmp); return addClause_(addTmp) }
    fun addEmptyClause(): Boolean { addTmp.clear(); return addClause_(addTmp) }
    fun addClause(p: Int): Boolean { addTmp.clear(); addTmp.push(p); return addClause_(addTmp) }
    fun addClause(p: Int, q: Int): Boolean { addTmp.clear(); addTmp.push(p); addTmp.push(q); return addClause_(addTmp) }
    fun addClause(p: Int, q: Int, r: Int): Boolean {
        addTmp.clear(); addTmp.push(p); addTmp.push(q); addTmp.push(r); return addClause_(addTmp)
    }
    fun addClause(p: Int, q: Int, r: Int, s: Int): Boolean {
        addTmp.clear(); addTmp.push(p); addTmp.push(q); addTmp.push(r); addTmp.push(s); return addClause_(addTmp)
    }
    /** `Solver::addClause(Lit p)` with static binding to `Solver::addClause_`. */
    protected fun solverAddClause(p: Int): Boolean { addTmp.clear(); addTmp.push(p); return solverAddClause_(addTmp) }

    protected fun isRemoved(cr: Int): Boolean = ca.mark(cr) == 1
    protected fun locked(cr: Int): Boolean {
        val c0 = ca.lit(cr, 0)
        return lbEq(valueLit(c0), L_TRUE) && reason(litVar(c0)) != CREF_UNDEF && reason(litVar(c0)) == cr
    }
    protected fun newDecisionLevel() { trailLim.push(trail.size) }

    protected fun decisionLevel(): Int = trailLim.size
    protected fun abstractLevel(x: Int): Int = 1 shl (level(x) and 31)
    fun valueVar(x: Int): Int = assigns[x]                                    // value(Var)
    fun valueLit(p: Int): Int = lbXor(assigns[litVar(p)], litSign(p))      // value(Lit)
    fun modelValue(x: Int): Int = model[x]                                 // modelValue(Var)
    fun modelValueLit(p: Int): Int = lbXor(model[litVar(p)], litSign(p))   // modelValue(Lit)
    fun nAssigns(): Int = trail.size
    fun nClauses(): Int = numClauses.toInt()
    fun nLearnts(): Int = numLearnts.toInt()
    fun nVars(): Int = nextVar
    // TODO (upstream): nFreeVars() is not quite correct.
    fun nFreeVars(): Int = decVars.toInt() - (if (trailLim.size == 0) trail.size else trailLim[0])
    fun setPolarity(v: Int, b: Int) { userPol[v] = b }
    fun setDecisionVar(v: Int, b: Boolean) {
        if (b && decision[v] == 0) decVars++
        else if (!b && decision[v] != 0) decVars--

        decision[v] = if (b) 1 else 0
        insertVarOrder(v)
    }
    fun setConfBudget(x: Long) { conflictBudget = conflicts + x }
    fun setPropBudget(x: Long) { propagationBudget = propagations + x }
    fun interrupt() { asynchInterrupt = true }
    fun clearInterrupt() { asynchInterrupt = false }
    fun budgetOff() { conflictBudget = -1; propagationBudget = -1 }
    protected fun withinBudget(): Boolean =
        !asynchInterrupt &&
            (conflictBudget < 0 || conflicts.toULong() < conflictBudget.toULong()) &&
            (propagationBudget < 0 || propagations.toULong() < propagationBudget.toULong())

    // FIXME (upstream): after the introduction of asynchronous interrruptions the solve-versions
    // that return a pure bool do not give a safe interface.
    open fun solve(p: Int): Boolean { budgetOff(); assumptions.clear(); assumptions.push(p); return solve_() == L_TRUE }
    open fun solve(p: Int, q: Int): Boolean {
        budgetOff(); assumptions.clear(); assumptions.push(p); assumptions.push(q); return solve_() == L_TRUE
    }
    open fun solve(p: Int, q: Int, r: Int): Boolean {
        budgetOff(); assumptions.clear(); assumptions.push(p); assumptions.push(q); assumptions.push(r)
        return solve_() == L_TRUE
    }
    open fun solve(assumps: IntVec): Boolean { budgetOff(); assumps.copyTo(assumptions); return solve_() == L_TRUE }
    open fun solveLimited(assumps: IntVec): Int { assumps.copyTo(assumptions); return solve_() }
    fun okay(): Boolean = ok

    fun toDimacs(out: Appendable) = toDimacs(out, IntVec())

    // =========================================================================================
    // Minor methods
    // =========================================================================================

    /**
     * Creates a new SAT variable in the solver. If 'decision' is cleared, variable will not be
     * used as a decision variable (NOTE! This has effects on the meaning of a SATISFIABLE result).
     */
    open fun newVar(upol: Int = L_UNDEF, dvar: Boolean = true): Int = solverNewVar(upol, dvar)

    protected fun solverNewVar(upol: Int, dvar: Boolean): Int {
        val v: Int
        if (freeVars.size > 0) {
            v = freeVars.last()
            freeVars.pop()
        } else {
            v = nextVar++
        }

        watches.init(mkLit(v, false))
        watches.init(mkLit(v, true))
        assigns.insert(v, L_UNDEF)
        vardataReason.insert(v, CREF_UNDEF)
        vardataLevel.insert(v, 0)
        activity.insert(v, if (rndInitAct) drand() * 0.00001 else 0.0)
        seen.insert(v, 0)
        polarity.insert(v, 1)
        userPol.insert(v, upol)
        decision.reserve(v)
        trail.capacity(v + 1)
        setDecisionVar(v, dvar)
        return v
    }

    /**
     * Make literal true and promise to never refer to variable again. Note: at the moment, only
     * unassigned variable will be released (this is to avoid duplicate releases of the same variable).
     */
    open fun releaseVar(l: Int) = solverReleaseVar(l)

    protected fun solverReleaseVar(l: Int) {
        if (lbEq(valueLit(l), L_UNDEF)) {
            solverAddClause(l)
            releasedVars.push(litVar(l))
        }
    }

    /** Add a clause without making a superflous internal copy. Will change the passed vector 'ps'. */
    open fun addClause_(ps: IntVec): Boolean = solverAddClause_(ps)

    protected fun solverAddClause_(ps: IntVec): Boolean {
        mAssert(decisionLevel() == 0) { "addClause_ at decision level > 0" }
        if (!ok) return false

        // Check if clause is satisfied and remove false/duplicate literals:
        sort(ps)
        var p = LIT_UNDEF
        var i = 0
        var j = 0
        while (i < ps.size) {
            if (lbEq(valueLit(ps[i]), L_TRUE) || ps[i] == litNeg(p))
                return true
            else if (!lbEq(valueLit(ps[i]), L_FALSE) && ps[i] != p) {
                p = ps[i]; ps[j++] = p
            }
            i++
        }
        ps.shrink(i - j)

        if (ps.size == 0) {
            ok = false; return false
        } else if (ps.size == 1) {
            uncheckedEnqueue(ps[0])
            if (trace != null) tr("ASSIGN ${dimacsOf(ps[0])} reason=F")
            ok = (propagate() == CREF_UNDEF)
            return ok
        } else {
            val cr = ca.alloc(ps, false)
            clauses.push(cr)
            attachClause(cr)
            if (trace != null) trClause("ADD", cr)
        }

        return true
    }

    protected fun attachClause(cr: Int) {
        val size = ca.size(cr)
        mAssert(size > 1) { "attachClause of clause with size ${size}" }
        val c0 = ca.lit(cr, 0); val c1 = ca.lit(cr, 1)
        watches[litNeg(c0)].push(cr, c1)
        watches[litNeg(c1)].push(cr, c0)
        if (ca.learnt(cr)) { numLearnts++; learntsLiterals += size }
        else { numClauses++; clausesLiterals += size }
    }

    protected fun detachClause(cr: Int, strict: Boolean = false) {
        val size = ca.size(cr)
        mAssert(size > 1) { "detachClause of clause with size $size" }

        // Strict or lazy detaching:
        if (strict) {
            watches[litNeg(ca.lit(cr, 0))].remove(cr)
            watches[litNeg(ca.lit(cr, 1))].remove(cr)
        } else {
            watches.smudge(litNeg(ca.lit(cr, 0)))
            watches.smudge(litNeg(ca.lit(cr, 1)))
        }

        if (ca.learnt(cr)) { numLearnts--; learntsLiterals -= size }
        else { numClauses--; clausesLiterals -= size }
    }

    /** Detach and free a clause. */
    protected open fun removeClause(cr: Int) = solverRemoveClause(cr)

    protected fun solverRemoveClause(cr: Int) {
        if (trace != null) trClause(if (ca.learnt(cr)) "DEL learnt" else "DEL orig", cr)
        detachClause(cr)
        // Don't leave pointers to free'd memory!
        if (locked(cr)) vardataReason[litVar(ca.lit(cr, 0))] = CREF_UNDEF
        ca.mark(cr, 1)
        ca.free(cr)
    }

    protected fun satisfied(cr: Int): Boolean {
        for (i in 0 until ca.size(cr))
            if (lbEq(valueLit(ca.lit(cr, i)), L_TRUE))
                return true
        return false
    }

    /** Revert to the state at given level (keeping all assignment at 'level' but not beyond). */
    protected fun cancelUntil(level: Int) {
        if (decisionLevel() > level) {
            var c = trail.size - 1
            while (c >= trailLim[level]) {
                val x = litVar(trail[c])
                assigns[x] = L_UNDEF
                if (phaseSaving > 1 || (phaseSaving == 1 && c > trailLim.last()))
                    polarity[x] = if (litSign(trail[c])) 1 else 0
                insertVarOrder(x)
                c--
            }
            qhead = trailLim[level]
            trail.shrink(trail.size - trailLim[level])
            trailLim.shrink(trailLim.size - level)
        }
    }

    // =========================================================================================
    // Major methods
    // =========================================================================================

    protected fun pickBranchLit(): Int {
        var next = VAR_UNDEF

        // Random decision:
        if (drand() < randomVarFreq && !orderHeap.empty()) {
            next = orderHeap[irand(orderHeap.size())]
            if (lbEq(valueVar(next), L_UNDEF) && decision[next] != 0)
                rndDecisions++
        }

        // Activity based decision:
        while (next == VAR_UNDEF || !lbEq(valueVar(next), L_UNDEF) || decision[next] == 0)
            if (orderHeap.empty()) {
                next = VAR_UNDEF
                break
            } else {
                next = orderHeap.removeMin()
            }

        // Choose polarity based on different polarity modes (global or per-variable):
        return if (next == VAR_UNDEF)
            LIT_UNDEF
        else if (!lbEq(userPol[next], L_UNDEF))
            mkLit(next, lbEq(userPol[next], L_TRUE))
        else if (rndPol)
            mkLit(next, drand() < 0.5)
        else
            mkLit(next, polarity[next] != 0)
    }

    /**
     * analyze: Analyze conflict and produce a reason clause.
     * Pre: 'outLearnt' is cleared; current decision level > root level.
     * Post: 'outLearnt[0]' is the asserting literal at level 'out_btlevel' (returned);
     * if outLearnt.size > 1 then 'outLearnt[1]' has the greatest decision level of the rest.
     */
    protected fun analyze(conflIn: Int, outLearnt: IntVec): Int {
        var confl = conflIn
        var pathC = 0
        var p = LIT_UNDEF

        // Generate conflict clause:
        outLearnt.push(0)      // (leave room for the asserting literal)
        var index = trail.size - 1

        do {
            mAssert(confl != CREF_UNDEF) { "analyze: confl undef (should be UIP)" }
            val cr = confl

            if (ca.learnt(cr))
                claBumpActivity(cr)

            var j = if (p == LIT_UNDEF) 0 else 1
            while (j < ca.size(cr)) {
                val q = ca.lit(cr, j)

                if (seen[litVar(q)] == 0 && level(litVar(q)) > 0) {
                    varBumpActivity(litVar(q))
                    seen[litVar(q)] = 1
                    if (level(litVar(q)) >= decisionLevel())
                        pathC++
                    else
                        outLearnt.push(q)
                }
                j++
            }

            // Select next clause to look at:
            while (seen[litVar(trail[index--])] == 0) { }
            p = trail[index + 1]
            confl = reason(litVar(p))
            seen[litVar(p)] = 0
            pathC--
        } while (pathC > 0)
        outLearnt[0] = litNeg(p)

        // Simplify conflict clause:
        var i: Int
        var j: Int
        outLearnt.copyTo(analyzeToclear)
        if (ccminMode == 2) {
            i = 1; j = 1
            while (i < outLearnt.size) {
                if (reason(litVar(outLearnt[i])) == CREF_UNDEF || !litRedundant(outLearnt[i]))
                    outLearnt[j++] = outLearnt[i]
                i++
            }
        } else if (ccminMode == 1) {
            i = 1; j = 1
            while (i < outLearnt.size) {
                val x = litVar(outLearnt[i])

                if (reason(x) == CREF_UNDEF) {
                    outLearnt[j++] = outLearnt[i]
                } else {
                    val c = reason(litVar(outLearnt[i]))
                    for (k in 1 until ca.size(c))
                        if (seen[litVar(ca.lit(c, k))] == 0 && level(litVar(ca.lit(c, k))) > 0) {
                            outLearnt[j++] = outLearnt[i]
                            break
                        }
                }
                i++
            }
        } else {
            i = outLearnt.size; j = outLearnt.size
        }

        maxLiterals += outLearnt.size
        outLearnt.shrink(i - j)
        totLiterals += outLearnt.size

        // Find correct backtrack level:
        val outBtlevel: Int
        if (outLearnt.size == 1) {
            outBtlevel = 0
        } else {
            var maxI = 1
            // Find the first literal assigned at the next-highest level:
            for (k in 2 until outLearnt.size)
                if (level(litVar(outLearnt[k])) > level(litVar(outLearnt[maxI])))
                    maxI = k
            // Swap-in this literal at index 1:
            val q = outLearnt[maxI]
            outLearnt[maxI] = outLearnt[1]
            outLearnt[1] = q
            outBtlevel = level(litVar(q))
        }

        for (k in 0 until analyzeToclear.size) seen[litVar(analyzeToclear[k])] = 0    // ('seen[]' is now cleared)
        return outBtlevel
    }

    /** Check if 'p' can be removed from a conflict clause. */
    protected fun litRedundant(p0: Int): Boolean {
        val seenUndef = 0; val seenSource = 1; val seenRemovable = 2; val seenFailed = 3
        var p = p0
        mAssert(seen[litVar(p)] == seenUndef || seen[litVar(p)] == seenSource) { "litRedundant seen" }
        mAssert(reason(litVar(p)) != CREF_UNDEF) { "litRedundant reason" }

        var c = reason(litVar(p))
        analyzeStackI.clear(); analyzeStackL.clear()

        var i = 1
        while (true) {
            if (i < ca.size(c)) {
                // Checking 'p'-parents 'l':
                val l = ca.lit(c, i)

                // Variable at level 0 or previously removable:
                if (level(litVar(l)) == 0 || seen[litVar(l)] == seenSource || seen[litVar(l)] == seenRemovable) {
                    i++
                    continue
                }

                // Check variable can not be removed for some local reason:
                if (reason(litVar(l)) == CREF_UNDEF || seen[litVar(l)] == seenFailed) {
                    analyzeStackI.push(0); analyzeStackL.push(p)
                    for (k in 0 until analyzeStackL.size)
                        if (seen[litVar(analyzeStackL[k])] == seenUndef) {
                            seen[litVar(analyzeStackL[k])] = seenFailed
                            analyzeToclear.push(analyzeStackL[k])
                        }

                    return false
                }

                // Recursively check 'l':
                analyzeStackI.push(i); analyzeStackL.push(p)
                i = 0
                p = l
                c = reason(litVar(p))
            } else {
                // Finished with current element 'p' and reason 'c':
                if (seen[litVar(p)] == seenUndef) {
                    seen[litVar(p)] = seenRemovable
                    analyzeToclear.push(p)
                }

                // Terminate with success if stack is empty:
                if (analyzeStackL.size == 0) break

                // Continue with top element on stack:
                i = analyzeStackI.last()
                p = analyzeStackL.last()
                c = reason(litVar(p))

                analyzeStackI.pop(); analyzeStackL.pop()
            }
            i++
        }

        return true
    }

    /**
     * analyzeFinal: Specialized analysis procedure to express the final conflict in terms of
     * assumptions. Calculates the (possibly empty) set of assumptions that led to the assignment
     * of 'p', and stores the result in 'out_conflict'.
     */
    protected fun analyzeFinal(p: Int, outConflict: LitSet) {
        outConflict.clear()
        outConflict.insert(p)

        if (decisionLevel() == 0)
            return

        seen[litVar(p)] = 1

        var i = trail.size - 1
        while (i >= trailLim[0]) {
            val x = litVar(trail[i])
            if (seen[x] != 0) {
                if (reason(x) == CREF_UNDEF) {
                    mAssert(level(x) > 0) { "analyzeFinal: decision var at level 0" }
                    outConflict.insert(litNeg(trail[i]))
                } else {
                    val c = reason(x)
                    for (j in 1 until ca.size(c))
                        if (level(litVar(ca.lit(c, j))) > 0)
                            seen[litVar(ca.lit(c, j))] = 1
                }
                seen[x] = 0
            }
            i--
        }

        seen[litVar(p)] = 0
    }

    protected fun uncheckedEnqueue(p: Int, from: Int = CREF_UNDEF) {
        mAssert(lbEq(valueLit(p), L_UNDEF)) { "uncheckedEnqueue of assigned literal" }
        assigns[litVar(p)] = lbOf(!litSign(p))
        vardataReason[litVar(p)] = from
        vardataLevel[litVar(p)] = decisionLevel()
        trail.push(p)
        if (trace != null && from != CREF_UNDEF) tr("ASSIGN ${dimacsOf(p)} reason=C")
    }

    /**
     * propagate: Propagates all enqueued facts. If a conflict arises, the conflicting clause is
     * returned, otherwise CRef_Undef. Post: the propagation queue is empty, even on conflict.
     */
    protected fun propagate(): Int {
        var confl = CREF_UNDEF
        var numProps = 0

        while (qhead < trail.size) {
            val p = trail[qhead++]     // 'p' is enqueued fact to propagate.
            val ws = watches.lookup(p)
            val wd = ws.data
            var i = 0
            var j = 0
            val end = ws.size
            numProps++

            while (i != end) {
                // Try to avoid inspecting the clause:
                val blocker = wd[2 * i + 1]
                if (lbEq(valueLit(blocker), L_TRUE)) {
                    wd[2 * j] = wd[2 * i]; wd[2 * j + 1] = wd[2 * i + 1]; j++; i++
                    continue
                }

                // Make sure the false literal is data[1]:
                val cr = wd[2 * i]
                val falseLit = litNeg(p)
                if (ca.lit(cr, 0) == falseLit) {
                    ca.setLit(cr, 0, ca.lit(cr, 1)); ca.setLit(cr, 1, falseLit)
                }
                mAssert(ca.lit(cr, 1) == falseLit) { "propagate: c[1] != false_lit" }
                i++

                // If 0th watch is true, then clause is already satisfied.
                val first = ca.lit(cr, 0)
                if (first != blocker && lbEq(valueLit(first), L_TRUE)) {
                    wd[2 * j] = cr; wd[2 * j + 1] = first; j++
                    continue
                }

                // Look for new watch:
                var found = false
                val size = ca.size(cr)
                for (k in 2 until size)
                    if (!lbEq(valueLit(ca.lit(cr, k)), L_FALSE)) {
                        ca.setLit(cr, 1, ca.lit(cr, k)); ca.setLit(cr, k, falseLit)
                        watches[litNeg(ca.lit(cr, 1))].push(cr, first)
                        found = true
                        break
                    }
                if (found) continue

                // Did not find watch -- clause is unit under assignment:
                wd[2 * j] = cr; wd[2 * j + 1] = first; j++
                if (lbEq(valueLit(first), L_FALSE)) {
                    confl = cr
                    qhead = trail.size
                    // Copy the remaining watches:
                    while (i < end) {
                        wd[2 * j] = wd[2 * i]; wd[2 * j + 1] = wd[2 * i + 1]; j++; i++
                    }
                } else {
                    uncheckedEnqueue(first, cr)
                }
            }
            ws.shrink(i - j)
        }
        propagations += numProps
        simpDBProps -= numProps

        return confl
    }

    /**
     * reduceDB: Remove half of the learnt clauses, minus the clauses locked by the current
     * assignment. Locked clauses are clauses that are reason to some assignment. Binary clauses
     * are never removed.
     */
    protected fun reduceDB() {
        tr("REDUCE")
        val extraLim = claInc / learnts.size    // Remove any clause below this activity

        // reduceDB_lt
        sort(learnts) { x, y ->
            ca.size(x) > 2 && (ca.size(y) == 2 || ca.activity(x) < ca.activity(y))
        }
        // Don't delete binary or locked clauses. From the rest, delete clauses from the first half
        // and clauses with activity smaller than 'extra_lim':
        var i = 0
        var j = 0
        while (i < learnts.size) {
            val cr = learnts[i]
            if (ca.size(cr) > 2 && !locked(cr) && (i < learnts.size / 2 || ca.activity(cr).toDouble() < extraLim))
                solverRemoveClause(learnts[i])
            else
                learnts[j++] = learnts[i]
            i++
        }
        learnts.shrink(i - j)
        checkGarbage()
    }

    /** Shrink 'cs' to contain only non-satisfied clauses. */
    protected fun removeSatisfied(cs: IntVec) {
        var i = 0
        var j = 0
        while (i < cs.size) {
            val cr = cs[i]
            if (satisfied(cr)) {
                solverRemoveClause(cs[i])
            } else {
                // Trim clause:
                mAssert(lbEq(valueLit(ca.lit(cr, 0)), L_UNDEF) && lbEq(valueLit(ca.lit(cr, 1)), L_UNDEF)) {
                    "removeSatisfied: watched literal assigned"
                }
                val traceSize = ca.size(cr)
                var k = 2
                while (k < ca.size(cr)) {
                    if (lbEq(valueLit(ca.lit(cr, k)), L_FALSE)) {
                        ca.setLit(cr, k--, ca.lit(cr, ca.size(cr) - 1))
                        ca.pop(cr)
                    }
                    k++
                }
                if (trace != null && traceSize != ca.size(cr))
                    trClause(if (ca.learnt(cr)) "TRIM learnt" else "TRIM orig", cr)
                cs[j++] = cs[i]
            }
            i++
        }
        cs.shrink(i - j)
    }

    protected fun rebuildOrderHeap() {
        val vs = IntVec()
        for (v in 0 until nVars())
            if (decision[v] != 0 && lbEq(valueVar(v), L_UNDEF))
                vs.push(v)
        orderHeap.build(vs)
    }

    /**
     * simplify: Simplify the clause database according to the current top-level assigment.
     * Currently, the only thing done here is the removal of satisfied clauses.
     */
    fun simplify(): Boolean {
        mAssert(decisionLevel() == 0) { "simplify at decision level > 0" }

        if (!ok || propagate() != CREF_UNDEF) {
            ok = false; return false
        }

        if (nAssigns() == simpDBAssigns || (simpDBProps > 0))
            return true
        tr("SIMPLIFY")

        // Remove satisfied clauses:
        removeSatisfied(learnts)
        if (removeSatisfied) {       // Can be turned off.
            removeSatisfied(clauses)

            // TODO (upstream): what todo in if 'remove_satisfied' is false?

            // Remove all released variables from the trail:
            for (i in 0 until releasedVars.size) {
                mAssert(seen[releasedVars[i]] == 0) { "simplify: released var seen" }
                seen[releasedVars[i]] = 1
            }

            var i = 0
            var j = 0
            while (i < trail.size) {
                if (seen[litVar(trail[i])] == 0)
                    trail[j++] = trail[i]
                i++
            }
            trail.shrink(i - j)
            qhead = trail.size

            for (k in 0 until releasedVars.size)
                seen[releasedVars[k]] = 0

            // Released variables are now ready to be reused:
            append(releasedVars, freeVars)
            releasedVars.clear()
        }
        checkGarbage()
        rebuildOrderHeap()

        simpDBAssigns = nAssigns()
        simpDBProps = clausesLiterals + learntsLiterals   // (shouldn't depend on stats really, but it will do for now)

        return true
    }

    /**
     * search: Search for a model the specified number of conflicts (negative = infinity).
     * Returns l_True if a partial assigment that is consistent with respect to the clauseset is
     * found, l_False if the clause set is unsatisfiable, l_Undef if the bound is reached.
     */
    protected fun search(nofConflicts: Int): Int {
        mAssert(ok) { "search with ok == false" }
        var conflictC = 0
        val learntClause = IntVec()
        starts++

        while (true) {
            val confl = propagate()
            if (confl != CREF_UNDEF) {
                // CONFLICT
                tr("CONFLICT")
                conflicts++; conflictC++
                if (decisionLevel() == 0) return L_FALSE

                learntClause.clear()
                val backtrackLevel = analyze(confl, learntClause)
                if (trace != null) trLits("LEARN level=$backtrackLevel", learntClause)
                cancelUntil(backtrackLevel)

                if (learntClause.size == 1) {
                    uncheckedEnqueue(learntClause[0])
                    if (trace != null) tr("ASSIGN ${dimacsOf(learntClause[0])} reason=C")
                } else {
                    val cr = ca.alloc(learntClause, true)
                    learnts.push(cr)
                    attachClause(cr)
                    claBumpActivity(cr)
                    uncheckedEnqueue(learntClause[0], cr)
                }

                varDecayActivity()
                claDecayActivity()

                if (--learntsizeAdjustCnt == 0) {
                    learntsizeAdjustConfl *= learntsizeAdjustInc
                    learntsizeAdjustCnt = learntsizeAdjustConfl.toInt()
                    maxLearnts *= learntsizeInc

                    if (verbosity >= 1)
                        println(
                            "| " + fmtD(conflicts.toInt(), 9) + " | " +
                                fmtD(decVars.toInt() - (if (trailLim.size == 0) trail.size else trailLim[0]), 7) + " " +
                                fmtD(nClauses(), 8) + " " + fmtD(clausesLiterals.toInt(), 8) + " | " +
                                fmtD(maxLearnts.toInt(), 8) + " " + fmtD(nLearnts(), 8) + " " +
                                fmtF(learntsLiterals.toDouble() / nLearnts(), 6, 0) + " | " +
                                fmtF(progressEstimate() * 100, 6, 3) + " % |",
                        )
                }
            } else {
                // NO CONFLICT
                if ((nofConflicts >= 0 && conflictC >= nofConflicts) || !withinBudget()) {
                    // Reached bound on number of conflicts:
                    progressEstimate = progressEstimate()
                    cancelUntil(0)
                    return L_UNDEF
                }

                // Simplify the set of problem clauses:
                if (decisionLevel() == 0 && !simplify())
                    return L_FALSE

                if ((learnts.size - nAssigns()).toDouble() >= maxLearnts)
                    // Reduce the set of learnt clauses:
                    reduceDB()

                var next = LIT_UNDEF
                while (decisionLevel() < assumptions.size) {
                    // Perform user provided assumption:
                    val p = assumptions[decisionLevel()]
                    if (lbEq(valueLit(p), L_TRUE)) {
                        // Dummy decision level:
                        newDecisionLevel()
                    } else if (lbEq(valueLit(p), L_FALSE)) {
                        analyzeFinal(litNeg(p), conflict)
                        return L_FALSE
                    } else {
                        next = p
                        break
                    }
                }

                if (next == LIT_UNDEF) {
                    // New variable decision:
                    decisions++
                    next = pickBranchLit()

                    if (next == LIT_UNDEF)
                        // Model found:
                        return L_TRUE
                }

                // Increase decision level and enqueue 'next'
                newDecisionLevel()
                uncheckedEnqueue(next)
                if (trace != null) {
                    tr("DECIDE ${dimacsOf(next)}")
                    tr("ASSIGN ${dimacsOf(next)} reason=D")
                }
            }
        }
    }

    fun progressEstimate(): Double {
        var progress = 0.0
        val f = 1.0 / nVars()

        for (i in 0..decisionLevel()) {
            val beg = if (i == 0) 0 else trailLim[i - 1]
            val end = if (i == decisionLevel()) trail.size else trailLim[i]
            progress += f.pow(i) * (end - beg)
        }

        return progress / nVars()
    }

    /*
      Finite subsequences of the Luby-sequence:

      0: 1
      1: 1 1 2
      2: 1 1 2 1 1 2 4
      3: 1 1 2 1 1 2 4 1 1 2 1 1 2 4 8
      ...
     */
    private fun luby(y: Double, x0: Int): Double {
        var x = x0
        // Find the finite subsequence that contains index 'x', and the size of that subsequence:
        var size = 1
        var seq = 0
        while (size < x + 1) { seq++; size = 2 * size + 1 }

        while (size - 1 != x) {
            size = (size - 1) shr 1
            seq--
            x %= size
        }

        return y.pow(seq)
    }

    /** Main solve method (assumptions given in 'assumptions'). */
    protected fun solve_(): Int = solverSolve_()

    protected fun solverSolve_(): Int {
        model.clear()
        conflict.clear()
        if (!ok) { tr("RESULT UNSAT"); return L_FALSE }

        solves++

        maxLearnts = nClauses() * learntsizeFactor
        if (maxLearnts < minLearntsLim)
            maxLearnts = minLearntsLim.toDouble()

        learntsizeAdjustConfl = learntsizeAdjustStartConfl.toDouble()
        learntsizeAdjustCnt = learntsizeAdjustConfl.toInt()
        var status = L_UNDEF

        if (verbosity >= 1) {
            println("============================[ Search Statistics ]==============================")
            println("| Conflicts |          ORIGINAL         |          LEARNT          | Progress |")
            println("|           |    Vars  Clauses Literals |    Limit  Clauses Lit/Cl |          |")
            println("===============================================================================")
        }

        // Search:
        var currRestarts = 0
        while (lbEq(status, L_UNDEF)) {
            val restBase = if (lubyRestart) luby(restartInc, currRestarts) else restartInc.pow(currRestarts)
            if (currRestarts > 0) tr("RESTART")
            status = search((restBase * restartFirst).toInt())
            if (!withinBudget()) break
            currRestarts++
        }

        if (verbosity >= 1)
            println("===============================================================================")

        if (lbEq(status, L_TRUE)) {
            // Extend & copy model:
            model.growTo(nVars())
            for (i in 0 until nVars()) model[i] = valueVar(i)
        } else if (lbEq(status, L_FALSE) && conflict.size() == 0) {
            ok = false
        }

        cancelUntil(0)
        tr(if (lbEq(status, L_TRUE)) "RESULT SAT" else if (lbEq(status, L_FALSE)) "RESULT UNSAT" else "RESULT UNKNOWN")
        return status
    }

    fun implies(assumps: IntVec, out: IntVec): Boolean {
        trailLim.push(trail.size)
        for (i in 0 until assumps.size) {
            val a = assumps[i]

            if (lbEq(valueLit(a), L_FALSE)) {
                cancelUntil(0)
                return false
            } else if (lbEq(valueLit(a), L_UNDEF)) {
                uncheckedEnqueue(a)
            }
        }

        if (trace != null) trProbeAssigns()
        val trailBefore = trail.size
        var ret = true
        if (propagate() == CREF_UNDEF) {
            out.clear()
            for (j in trailBefore until trail.size)
                out.push(trail[j])
        } else {
            ret = false
        }

        cancelUntil(0)
        return ret
    }

    // =========================================================================================
    // Writing CNF to DIMACS (FIXME upstream: this needs to be rewritten completely.)
    // =========================================================================================

    private fun mapVar(x: Int, map: IntVec, max: IntArray): Int {
        if (map.size <= x || map[x] == -1) {
            map.growTo(x + 1, -1)
            map[x] = max[0]++
        }
        return map[x]
    }

    private fun toDimacs(f: Appendable, cr: Int, map: IntVec, max: IntArray) {
        if (satisfied(cr)) return

        for (i in 0 until ca.size(cr))
            if (!lbEq(valueLit(ca.lit(cr, i)), L_FALSE))
                f.append(if (litSign(ca.lit(cr, i))) "-" else "").append((mapVar(litVar(ca.lit(cr, i)), map, max) + 1).toString()).append(" ")
        f.append("0\n")
    }

    /** Write CNF in DIMACS format (upstream `toDimacs(FILE*, const vec<Lit>&)`). */
    fun toDimacs(f: Appendable, assumps: IntVec) {
        // Handle case when solver is in contradictory state:
        if (!ok) {
            f.append("p cnf 1 2\n1 0\n-1 0\n")
            return
        }

        val map = IntVec()
        val max = intArrayOf(0)

        // Cannot use removeClauses here because it is not safe
        // to deallocate them at this point. Could be improved.
        var cnt = 0
        for (i in 0 until clauses.size)
            if (!satisfied(clauses[i]))
                cnt++

        for (i in 0 until clauses.size)
            if (!satisfied(clauses[i])) {
                val c = clauses[i]
                for (j in 0 until ca.size(c))
                    if (!lbEq(valueLit(ca.lit(c, j)), L_FALSE))
                        mapVar(litVar(ca.lit(c, j)), map, max)
            }

        // Assumptions are added as unit clauses:
        cnt += assumps.size

        f.append("p cnf ${max[0]} $cnt\n")

        for (i in 0 until assumps.size) {
            mAssert(!lbEq(valueLit(assumps[i]), L_FALSE)) { "toDimacs: false assumption" }
            f.append(if (litSign(assumps[i])) "-" else "").append((mapVar(litVar(assumps[i]), map, max) + 1).toString()).append(" 0\n")
        }

        for (i in 0 until clauses.size)
            toDimacs(f, clauses[i], map, max)

        if (verbosity > 0)
            println("Wrote DIMACS with ${max[0]} variables and $cnt clauses.")
    }

    // =========================================================================================
    // Garbage Collection methods
    // =========================================================================================

    protected open fun relocAll(to: ClauseAllocator) = solverRelocAll(to)

    protected fun solverRelocAll(to: ClauseAllocator) {
        // All watchers:
        watches.cleanAll()
        for (v in 0 until nVars())
            for (s in 0 until 2) {
                val p = mkLit(v, s != 0)
                val ws = watches[p]
                for (j in 0 until ws.size)
                    ws.data[2 * j] = ca.reloc(ws.data[2 * j], to)
            }

        // All reasons:
        for (i in 0 until trail.size) {
            val v = litVar(trail[i])

            // Note: it is not safe to call 'locked()' on a relocated clause. This is why we keep
            // 'dangling' reasons here. It is safe and does not hurt.
            if (reason(v) != CREF_UNDEF && (ca.reloced(reason(v)) || locked(reason(v)))) {
                mAssert(!isRemoved(reason(v))) { "relocAll: removed reason" }
                vardataReason[v] = ca.reloc(vardataReason[v], to)
            }
        }

        // All learnt:
        var i = 0
        var j = 0
        while (i < learnts.size) {
            if (!isRemoved(learnts[i])) {
                learnts[i] = ca.reloc(learnts[i], to)
                learnts[j++] = learnts[i]
            }
            i++
        }
        learnts.shrink(i - j)

        // All original:
        i = 0; j = 0
        while (i < clauses.size) {
            if (!isRemoved(clauses[i])) {
                clauses[i] = ca.reloc(clauses[i], to)
                clauses[j++] = clauses[i]
            }
            i++
        }
        clauses.shrink(i - j)
    }

    open fun garbageCollect() {
        tr("GC core")
        // Initialize the next region to a size corresponding to the estimated utilization degree.
        // This is not precise but should avoid some unnecessary reallocations for the new region:
        val to = ClauseAllocator(ca.size() - ca.wasted())

        solverRelocAll(to)
        if (verbosity >= 2)
            println(
                "|  Garbage collection:   " + fmtD(ca.size() * 4, 12) + " bytes => " +
                    fmtD(to.size() * 4, 12) + " bytes             |",
            )
        to.moveTo(ca)
    }

    // =========================================================================================
    // Static helpers
    // =========================================================================================

    /** Returns a random float 0 <= x < 1. Seed must never be 0. (drand(random_seed)) */
    protected fun drand(): Double {
        randomSeed *= 1389796
        val q = (randomSeed / 2147483647).toInt()
        randomSeed -= q.toDouble() * 2147483647
        return randomSeed / 2147483647
    }

    /** Returns a random integer 0 <= x < size. Seed must never be 0. (irand(random_seed, size)) */
    protected fun irand(size: Int): Int = (drand() * size).toInt()

    // =========================================================================================
    // SatSolver adapter (signed DIMACS literals, like core/Dimacs.h + core/Main.cc)
    // =========================================================================================

    override val numVars: Int get() = nVars()

    /** Dimacs.h readClause + `S.addClause_(lits)`: variables are created lazily
     *  (`while (var >= S.nVars()) S.newVar();`). */
    override fun addClause(literals: IntArray) {
        val lits = IntVec()
        for (parsedLit in literals) {
            val v = abs(parsedLit) - 1
            while (v >= nVars()) newVar()
            lits.push(if (parsedLit > 0) mkLit(v) else litNeg(mkLit(v)))
        }
        addClause_(lits)
    }

    /**
     * Upstream `solve(const vec<Lit>& assumps)` on signed DIMACS assumptions. Variables referenced
     * only by an assumption are created lazily, like [addClause]. On SAT [valueOf] reads the model;
     * on UNSAT [failed] reads the final conflict. The trail is back at level 0 afterwards, so the
     * same instance can be solved again. A solve that ends l_Undef (only possible after
     * [interrupt]) has no [SatResult] and throws.
     */
    override fun solve(assumptions: IntArray): SatResult {
        val assumps = IntVec()
        for (lit in assumptions) {
            val v = abs(lit) - 1
            while (v >= nVars()) newVar()
            assumps.push(mkLit(v, lit < 0))
        }
        val r = adapterSolve(assumps)
        return when {
            lbEq(r, L_TRUE) -> SatResult.SAT
            lbEq(r, L_FALSE) -> SatResult.UNSAT
            else -> throw IllegalStateException("MiniSat: solve ended INDETERMINATE (interrupted)")
        }
    }

    /** The [SatSolver] solve: upstream `solve(assumps)` (budgetOff + solve_), keeping the lbool. */
    protected open fun adapterSolve(assumps: IntVec): Int {
        budgetOff(); assumps.copyTo(this.assumptions); return solve_()
    }

    /** IPASIR failed: true iff the negation of the signed DIMACS assumption [lit] is in [conflict]. */
    override fun failed(lit: Int): Boolean = conflict.has(litNeg(mkLit(abs(lit) - 1, lit < 0)))

    /** After SAT: true iff DIMACS variable [v] is true in [model]; a variable never created is false. */
    override fun valueOf(v: Int): Boolean {
        val idx = v - 1
        if (idx < 0 || idx >= model.size) return false
        return lbEq(model[idx], L_TRUE)
    }
}

// ---- printf helpers for the verbosity output (%Nd, %N.Mf) ----

internal fun fmtD(n: Int, width: Int): String = n.toString().padStart(width)

internal fun fmtF(x: Double, width: Int, prec: Int): String {
    val s = when {
        x.isNaN() -> "nan"
        x.isInfinite() -> if (x > 0) "inf" else "-inf"
        else -> {
            var scale = 1.0
            repeat(prec) { scale *= 10 }
            val r = kotlin.math.round(abs(x) * scale).toLong()
            val ip = r / scale.toLong()
            val fp = r % scale.toLong()
            val sign = if (x < 0 && r != 0L) "-" else ""
            if (prec == 0) "$sign$ip" else "$sign$ip." + fp.toString().padStart(prec, '0')
        }
    }
    return s.padStart(width)
}
