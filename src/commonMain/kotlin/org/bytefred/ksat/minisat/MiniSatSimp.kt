package org.bytefred.ksat.minisat

import kotlin.math.abs

/**
 * Kotlin port of MiniSat's preprocessing solver `Minisat::SimpSolver` (simp/SimpSolver.h +
 * simp/SimpSolver.cc): bounded variable elimination, backward subsumption / self-subsuming
 * resolution, optional asymmetric branching and implied-clause check, elimination clauses with
 * model extension, frozen variables. Upstream: github.com/meelgroup/minisat (commit 9a0382d, the
 * maintained fork; its solver code is niklasso/minisat 37dc6c6 plus compile fixes only); MIT,
 * (c) 2006 Niklas Een, Niklas Sorensson; (c) 2007-2010 Niklas Sorensson.
 *
 * Extends [MiniSat] like `class SimpSolver : public Solver`. Members SimpSolver hides in C++
 * (newVar, releaseVar, addClause_, removeClause, relocAll, solve_ and the solve overloads) are
 * overrides here; their Solver versions are called explicitly as `solverXxx` where upstream
 * writes `Solver::xxx`. Options have the upstream defaults (the `opt_*` values of SimpSolver.cc).
 *
 * Upstream-level use: add clauses, then `eliminate(true)` and `solveLimited(IntVec())` (simp/Main.cc),
 * or `solve(IntVec())` (do_simp = true, turn_off_simp = false). The [SatSolver] adapter
 * ([solve] on DIMACS assumptions, see [adapterSolve]) is `solve(assumps, do_simp = true,
 * turn_off_simp = true)`: eliminate once, on the first solve. Variables that must survive
 * elimination (later assumptions, incremental clauses) have to be frozen ([setFrozen]/[freezeVar])
 * before the first solve; using an eliminated variable through the adapter fails loudly.
 */
open class MiniSatSimp(numVarsHint: Int = 0) : MiniSat(numVarsHint) {

    // ---- Mode of operation (SimpSolver.cc options, upstream defaults) ----
    var grow: Int = 0                   // Allow a variable elimination step to grow by a number of clauses.
    var clauseLim: Int = 20             // Variables are not eliminated if it produces a resolvent with a length above this limit. -1 means no limit.
    var subsumptionLim: Int = 1000      // Do not check if subsumption against a clause larger than this. -1 means no limit.
    var simpGarbageFrac: Double = 0.5   // A different limit for when to issue a GC during simplification.

    var useAsymm: Boolean = false       // Shrink clauses by asymmetric branching.
    var useRcheck: Boolean = false      // Check if a clause is already implied. Prett costly, and subsumes subsumptions :)
    var useElim: Boolean = true         // Perform variable elimination.
    var extendModel: Boolean = true     // Flag to indicate whether the user needs to look at the full model.

    // ---- Statistics ----
    var merges = 0; protected set
    var asymmLits = 0; protected set
    var eliminatedVars = 0; protected set

    // ---- Solver state ----
    protected var elimorder = 1
    protected var useSimplification = true
    protected var maxSimpVar = 0                 // Max variable at the point simplification was turned off.
    protected val elimclauses = IntVec()         // vec<uint32_t>
    protected val touched = IntVec()
    protected val occurs = CRefOccLists(ca)
    protected val nOcc = IntVec()                // LMap<int>
    protected val elimHeap = IntHeap { x, y -> cost(x) < cost(y) }   // ElimLt
    protected val subsumptionQueue = IntQueue()
    protected val frozen = IntVec()
    protected val frozenVars = IntVec()
    protected val eliminated = IntVec()
    protected var bwdsubAssigns = 0
    protected var nTouched = 0

    // Temporaries:
    protected var bwdsubTmpunit: Int

    /** ElimLt::cost: (uint64_t)n_occ[mkLit(x)] * (uint64_t)n_occ[~mkLit(x)]. */
    private fun cost(x: Int): ULong =
        nOcc[mkLit(x)].toLong().toULong() * nOcc[litNeg(mkLit(x))].toLong().toULong()

    init {
        val dummy = IntVec(1, LIT_UNDEF)
        ca.extraClauseField = true // NOTE: must happen before allocating the dummy clause below.
        bwdsubTmpunit = ca.alloc(dummy)
        removeSatisfied = false
    }

    // =========================================================================================
    // Inline methods of SimpSolver.h
    // =========================================================================================

    fun isEliminated(v: Int): Boolean = eliminated[v] != 0

    protected fun updateElimHeap(v: Int) {
        mAssert(useSimplification) { "updateElimHeap without simplification" }
        // if (!frozen[v] && !isEliminated(v) && value(v) == l_Undef)
        if (elimHeap.inHeap(v) || (frozen[v] == 0 && !isEliminated(v) && lbEq(valueVar(v), L_UNDEF)))
            elimHeap.update(v)
    }

    /** If a variable is frozen it will not be eliminated. */
    fun setFrozen(v: Int, b: Boolean) {
        frozen[v] = if (b) 1 else 0
        if (useSimplification && !b) { updateElimHeap(v) }
    }

    /** Freeze one variable so it will not be eliminated. */
    fun freezeVar(v: Int) {
        if (frozen[v] == 0) {
            frozen[v] = 1
            frozenVars.push(v)
        }
    }

    /** Thaw all frozen variables. */
    fun thaw() {
        for (i in 0 until frozenVars.size) {
            val v = frozenVars[i]
            frozen[v] = 0
            if (useSimplification)
                updateElimHeap(v)
        }
        frozenVars.clear()
    }

    override fun solve(p: Int): Boolean = solve(p, true, false)
    override fun solve(p: Int, q: Int): Boolean = solve(p, q, true, false)
    override fun solve(p: Int, q: Int, r: Int): Boolean = solve(p, q, r, true, false)
    override fun solve(assumps: IntVec): Boolean = solve(assumps, true, false)
    override fun solveLimited(assumps: IntVec): Int = solveLimited(assumps, true, false)

    fun solve(doSimp: Boolean, turnOffSimp: Boolean): Boolean {
        budgetOff(); assumptions.clear(); return solve_(doSimp, turnOffSimp) == L_TRUE
    }
    fun solve(p: Int, doSimp: Boolean, turnOffSimp: Boolean): Boolean {
        budgetOff(); assumptions.clear(); assumptions.push(p); return solve_(doSimp, turnOffSimp) == L_TRUE
    }
    fun solve(p: Int, q: Int, doSimp: Boolean, turnOffSimp: Boolean): Boolean {
        budgetOff(); assumptions.clear(); assumptions.push(p); assumptions.push(q)
        return solve_(doSimp, turnOffSimp) == L_TRUE
    }
    fun solve(p: Int, q: Int, r: Int, doSimp: Boolean, turnOffSimp: Boolean): Boolean {
        budgetOff(); assumptions.clear(); assumptions.push(p); assumptions.push(q); assumptions.push(r)
        return solve_(doSimp, turnOffSimp) == L_TRUE
    }
    fun solve(assumps: IntVec, doSimp: Boolean, turnOffSimp: Boolean): Boolean {
        budgetOff(); assumps.copyTo(assumptions); return solve_(doSimp, turnOffSimp) == L_TRUE
    }
    fun solveLimited(assumps: IntVec, doSimp: Boolean, turnOffSimp: Boolean): Int {
        assumps.copyTo(assumptions); return solve_(doSimp, turnOffSimp)
    }

    /**
     * The [SatSolver] solve: upstream `SimpSolver::solveLimited(assumps, do_simp = true,
     * turn_off_simp = true)` after `budgetOff()` (= `SimpSolver::solve(assumps, true, true)`,
     * keeping the lbool). So the first solve freezes the assumption variables for the duration of
     * the elimination, runs `eliminate(true)` (which turns simplification off for good, unless the
     * formula is already UNSAT at the root: then upstream returns before its cleanup, later solves
     * re-enter `eliminate` and answer UNSAT at once) and then the search; later solves run the
     * plain core search (`do_simp &= use_simplification`), and
     * every SAT result goes through `extendModel`. An eliminated variable must not be used again
     * (upstream only asserts this in debug builds and is unsound in release): an assumption on it
     * fails loudly here, and so does [addClause] with it.
     */
    override fun adapterSolve(assumps: IntVec): Int {
        for (i in 0 until assumps.size)
            if (isEliminated(litVar(assumps[i])))
                throw IllegalStateException(
                    "MiniSatSimp: assumption on variable ${litVar(assumps[i]) + 1}, which was eliminated by an " +
                        "earlier solve; freeze it (setFrozen/freezeVar) before the first solve, or use the core MiniSat (Ksat: Solver.MINISAT) for incremental use",
                )
        budgetOff()
        return solveLimited(assumps, true, true)
    }

    /**
     * The [SatSolver] addClause ([MiniSat.addClause] on signed DIMACS literals) that fails loudly
     * on a variable eliminated by an earlier solve (see [adapterSolve]).
     */
    override fun addClause(literals: IntArray) {
        for (lit in literals) {
            val v = abs(lit) - 1
            if (v < nVars() && isEliminated(v))
                throw IllegalStateException(
                    "MiniSatSimp: clause uses variable ${v + 1}, which was eliminated by an earlier solve; " +
                        "freeze it (setFrozen/freezeVar) before the first solve, or use the core MiniSat (Ksat: Solver.MINISAT) for incremental use",
                )
        }
        super.addClause(literals)
    }

    // =========================================================================================
    // SimpSolver.cc
    // =========================================================================================

    override fun newVar(upol: Int, dvar: Boolean): Int {
        val v = solverNewVar(upol, dvar)

        frozen.insert(v, 0)
        eliminated.insert(v, 0)

        if (useSimplification) {
            nOcc.insert(mkLit(v), 0)
            nOcc.insert(litNeg(mkLit(v)), 0)
            occurs.init(v)
            touched.insert(v, 0)
            elimHeap.insert(v)
        }
        return v
    }

    override fun releaseVar(l: Int) {
        mAssert(!isEliminated(litVar(l))) { "releaseVar of eliminated variable" }
        if (!useSimplification && litVar(l) >= maxSimpVar)
            // Note: Guarantees that no references to this variable is
            // left in model extension datastructure. Could be improved!
            solverReleaseVar(l)
        else
            // Otherwise, don't allow variable to be reused.
            solverAddClause(l)
    }

    protected fun solve_(doSimp0: Boolean, turnOffSimp: Boolean): Int {
        val extraFrozen = IntVec()
        var result = L_TRUE

        val doSimp = doSimp0 and useSimplification

        if (doSimp) {
            // Assumptions must be temporarily frozen to run variable elimination:
            for (i in 0 until assumptions.size) {
                val v = litVar(assumptions[i])

                // If an assumption has been eliminated, remember it.
                mAssert(!isEliminated(v)) { "assumption on eliminated variable ${v + 1}" }

                if (frozen[v] == 0) {
                    // Freeze and store.
                    setFrozen(v, true)
                    extraFrozen.push(v)
                }
            }

            result = lbOf(eliminate(turnOffSimp))
        }

        if (lbEq(result, L_TRUE)) {
            result = solverSolve_()
        } else {
            if (verbosity >= 1)
                println("===============================================================================")
        }

        if (lbEq(result, L_TRUE) && extendModel)
            extendModel()

        if (doSimp)
            // Unfreeze the assumptions that were frozen:
            for (i in 0 until extraFrozen.size)
                setFrozen(extraFrozen[i], false)

        return result
    }

    override fun addClause_(ps: IntVec): Boolean {
        // '#ifndef NDEBUG' assert(!isEliminated(var(ps[i]))) loop: not in release

        val nclauses = clauses.size

        if (useRcheck && implied(ps))
            return true

        if (!solverAddClause_(ps))
            return false

        if (useSimplification && clauses.size == nclauses + 1) {
            val cr = clauses.last()

            // NOTE: the clause is added to the queue immediately and then
            // again during 'gatherTouchedClauses()'. If nothing happens
            // in between, it will only be checked once. Otherwise, it may
            // be checked twice unnecessarily. This is an unfortunate
            // consequence of how backward subsumption is used to mimic
            // forward subsumption.
            subsumptionQueue.insert(cr)
            for (i in 0 until ca.size(cr)) {
                val ci = ca.lit(cr, i)
                occurs[litVar(ci)].push(cr)
                nOcc[ci] = nOcc[ci] + 1
                touched[litVar(ci)] = 1
                nTouched++
                if (elimHeap.inHeap(litVar(ci)))
                    elimHeap.increase(litVar(ci))
            }
        }

        return true
    }

    override fun removeClause(cr: Int) {
        if (useSimplification)
            for (i in 0 until ca.size(cr)) {
                val ci = ca.lit(cr, i)
                nOcc[ci] = nOcc[ci] - 1
                updateElimHeap(litVar(ci))
                occurs.smudge(litVar(ci))
            }

        solverRemoveClause(cr)
    }

    protected fun strengthenClause(cr: Int, l: Int): Boolean {
        if (tracing) trClause("STRENGTHEN ${dimacsOf(l)}", cr)
        mAssert(decisionLevel() == 0) { "strengthenClause at decision level > 0" }
        mAssert(useSimplification) { "strengthenClause without simplification" }

        // FIX (upstream): this is too inefficient but would be nice to have (properly implemented)
        // if (!find(subsumption_queue, &c))
        subsumptionQueue.insert(cr)

        if (ca.size(cr) == 2) {
            removeClause(cr)
            ca.strengthen(cr, l)
        } else {
            detachClause(cr, true)
            ca.strengthen(cr, l)
            attachClause(cr)
            removeFirst(occurs[litVar(l)], cr)
            nOcc[l] = nOcc[l] - 1
            updateElimHeap(litVar(l))
        }

        if (tracing && ca.size(cr) == 1 && lbEq(valueLit(ca.lit(cr, 0)), L_UNDEF))
            tr("ASSIGN ${dimacsOf(ca.lit(cr, 0))} reason=F")
        return if (ca.size(cr) == 1) enqueue(ca.lit(cr, 0)) && propagate() == CREF_UNDEF else true
    }

    /** Returns FALSE if clause is always satisfied ('out_clause' should not be used). */
    protected fun merge(ps0: Int, qs0: Int, v: Int, outClause: IntVec): Boolean {
        merges++
        outClause.clear()

        val psSmallest = ca.size(ps0) < ca.size(qs0)
        val ps = if (psSmallest) qs0 else ps0
        val qs = if (psSmallest) ps0 else qs0

        for (i in 0 until ca.size(qs)) {
            if (litVar(ca.lit(qs, i)) != v) {
                var inPs = false
                for (j in 0 until ca.size(ps))
                    if (litVar(ca.lit(ps, j)) == litVar(ca.lit(qs, i))) {
                        if (ca.lit(ps, j) == litNeg(ca.lit(qs, i)))
                            return false
                        else {
                            inPs = true
                            break
                        }
                    }
                if (!inPs) outClause.push(ca.lit(qs, i))
            }
        }

        for (i in 0 until ca.size(ps))
            if (litVar(ca.lit(ps, i)) != v)
                outClause.push(ca.lit(ps, i))

        return true
    }

    /** Returns FALSE if clause is always satisfied. The resolvent size goes to size[0]. */
    protected fun merge(ps0: Int, qs0: Int, v: Int, size: IntArray): Boolean {
        merges++

        val psSmallest = ca.size(ps0) < ca.size(qs0)
        val ps = if (psSmallest) qs0 else ps0
        val qs = if (psSmallest) ps0 else qs0

        size[0] = ca.size(ps) - 1

        for (i in 0 until ca.size(qs)) {
            val qi = ca.lit(qs, i)
            if (litVar(qi) != v) {
                var inPs = false
                for (j in 0 until ca.size(ps))
                    if (litVar(ca.lit(ps, j)) == litVar(qi)) {
                        if (ca.lit(ps, j) == litNeg(qi))
                            return false
                        else {
                            inPs = true
                            break
                        }
                    }
                if (!inPs) size[0]++
            }
        }

        return true
    }

    protected fun gatherTouchedClauses() {
        if (nTouched == 0) return

        for (i in 0 until subsumptionQueue.size())
            if (ca.mark(subsumptionQueue[i]) == 0)
                ca.mark(subsumptionQueue[i], 2)

        for (i in 0 until nVars())
            if (touched[i] != 0) {
                val cs = occurs.lookup(i)
                for (j in 0 until cs.size)
                    if (ca.mark(cs[j]) == 0) {
                        subsumptionQueue.insert(cs[j])
                        ca.mark(cs[j], 2)
                    }
                touched[i] = 0
            }

        for (i in 0 until subsumptionQueue.size())
            if (ca.mark(subsumptionQueue[i]) == 2)
                ca.mark(subsumptionQueue[i], 0)

        nTouched = 0
    }

    protected fun implied(c: IntVec): Boolean {
        mAssert(decisionLevel() == 0) { "implied at decision level > 0" }

        trailLim.push(trail.size)
        for (i in 0 until c.size)
            if (lbEq(valueLit(c[i]), L_TRUE)) {
                cancelUntil(0)
                return true
            } else if (!lbEq(valueLit(c[i]), L_FALSE)) {
                mAssert(lbEq(valueLit(c[i]), L_UNDEF)) { "implied: literal not undef" }
                uncheckedEnqueue(litNeg(c[i]))
            }

        if (tracing) trProbeAssigns()
        val result = propagate() != CREF_UNDEF
        cancelUntil(0)
        return result
    }

    /** Backward subsumption + backward subsumption resolution. */
    protected fun backwardSubsumptionCheck(verbose: Boolean = false): Boolean {
        tr("START bwdsub")
        try {
            return backwardSubsumptionCheckBody(verbose)
        } finally {
            tr("END bwdsub")
        }
    }

    private fun backwardSubsumptionCheckBody(verbose: Boolean): Boolean {
        var cnt = 0
        var subsumed = 0
        var deletedLiterals = 0
        mAssert(decisionLevel() == 0) { "backwardSubsumptionCheck at decision level > 0" }

        while (subsumptionQueue.size() > 0 || bwdsubAssigns < trail.size) {

            // Empty subsumption queue and return immediately on user-interrupt:
            if (asynchInterrupt) {
                subsumptionQueue.clear()
                bwdsubAssigns = trail.size
                break
            }

            // Check top-level assignments by creating a dummy clause and placing it in the queue:
            if (subsumptionQueue.size() == 0 && bwdsubAssigns < trail.size) {
                val l = trail[bwdsubAssigns++]
                ca.setLit(bwdsubTmpunit, 0, l)
                ca.calcAbstraction(bwdsubTmpunit)
                subsumptionQueue.insert(bwdsubTmpunit)
            }

            val cr = subsumptionQueue.peek(); subsumptionQueue.pop()

            if (ca.mark(cr) != 0) continue

            if (verbose && verbosity >= 2 && cnt++ % 1000 == 0)
                print(
                    "subsumption left: " + fmtD(subsumptionQueue.size(), 10) + " (" + fmtD(subsumed, 10) +
                        " subsumed, " + fmtD(deletedLiterals, 10) + " deleted literals)\r",
                )

            mAssert(ca.size(cr) > 1 || lbEq(valueLit(ca.lit(cr, 0)), L_TRUE)) {
                "backwardSubsumptionCheck: unit clause not propagated"
            }   // Unit-clauses should have been propagated before this point.

            // Find best variable to scan:
            var best = litVar(ca.lit(cr, 0))
            for (i in 1 until ca.size(cr))
                if (occurs[litVar(ca.lit(cr, i))].size < occurs[best].size)
                    best = litVar(ca.lit(cr, i))

            // Search all candidates:
            val cs = occurs.lookup(best)

            var j = 0
            while (j < cs.size) {
                if (ca.mark(cr) != 0) {
                    break
                } else if (ca.mark(cs[j]) == 0 && cs[j] != cr && (subsumptionLim == -1 || ca.size(cs[j]) < subsumptionLim)) {
                    val l = ca.subsumes(cr, cs[j])

                    if (l == LIT_UNDEF && tracing) trClause("SUBSUME", cr)

                    if (l == LIT_UNDEF) {
                        subsumed++; removeClause(cs[j])
                    } else if (l != LIT_ERROR) {
                        deletedLiterals++

                        if (!strengthenClause(cs[j], litNeg(l)))
                            return false

                        // Did current candidate get deleted from cs? Then check candidate at index j again:
                        if (litVar(l) == best)
                            j--
                    }
                }
                j++
            }
        }

        return true
    }

    protected fun asymm(v: Int, cr: Int): Boolean {
        mAssert(decisionLevel() == 0) { "asymm at decision level > 0" }

        if (ca.mark(cr) != 0 || satisfied(cr)) return true

        trailLim.push(trail.size)
        var l = LIT_UNDEF
        for (i in 0 until ca.size(cr))
            if (litVar(ca.lit(cr, i)) != v && !lbEq(valueLit(ca.lit(cr, i)), L_FALSE))
                uncheckedEnqueue(litNeg(ca.lit(cr, i)))
            else
                l = ca.lit(cr, i)
        if (tracing) trProbeAssigns()

        if (propagate() != CREF_UNDEF) {
            cancelUntil(0)
            asymmLits++
            if (!strengthenClause(cr, l))
                return false
        } else {
            cancelUntil(0)
        }

        return true
    }

    protected fun asymmVar(v: Int): Boolean {
        tr("START asymm")
        try {
            return asymmVarBody(v)
        } finally {
            tr("END asymm")
        }
    }

    private fun asymmVarBody(v: Int): Boolean {
        mAssert(useSimplification) { "asymmVar without simplification" }

        val cls = occurs.lookup(v)

        if (!lbEq(valueVar(v), L_UNDEF) || cls.size == 0)
            return true

        var i = 0
        while (i < cls.size) {   // cls.size() is re-read each iteration (strengthenClause may shrink cls)
            if (!asymm(v, cls[i]))
                return false
            i++
        }

        return backwardSubsumptionCheck()
    }

    private fun mkElimClause(elimclauses: IntVec, x: Int) {
        elimclauses.push(x)
        elimclauses.push(1)
    }

    private fun mkElimClause(elimclauses: IntVec, v: Int, c: Int) {
        val first = elimclauses.size
        var vPos = -1

        // Copy clause to elimclauses-vector. Remember position where the
        // variable 'v' occurs:
        for (i in 0 until ca.size(c)) {
            elimclauses.push(ca.lit(c, i))
            if (litVar(ca.lit(c, i)) == v)
                vPos = i + first
        }
        mAssert(vPos != -1) { "mkElimClause: variable not in clause" }

        // Swap the first literal with the 'v' literal, so that the literal
        // containing 'v' will occur first in the clause:
        val tmp = elimclauses[vPos]
        elimclauses[vPos] = elimclauses[first]
        elimclauses[first] = tmp

        // Store the length of the clause last:
        elimclauses.push(ca.size(c))
    }

    protected fun eliminateVar(v: Int): Boolean {
        mAssert(frozen[v] == 0) { "eliminateVar of frozen variable" }
        mAssert(!isEliminated(v)) { "eliminateVar of eliminated variable" }
        mAssert(lbEq(valueVar(v), L_UNDEF)) { "eliminateVar of assigned variable" }

        // Split the occurrences into positive and negative:
        val cls = occurs.lookup(v)
        val pos = IntVec()
        val neg = IntVec()
        for (i in 0 until cls.size)
            (if (clauseHas(cls[i], mkLit(v))) pos else neg).push(cls[i])

        // Check wether the increase in number of clauses stays within the allowed ('grow'). Moreover,
        // no clause must exceed the limit on the maximal clause size (if it is set):
        var cnt = 0
        val clauseSize = IntArray(1)

        for (i in 0 until pos.size)
            for (j in 0 until neg.size)
                if (merge(pos[i], neg[j], v, clauseSize) &&
                    (++cnt > cls.size + grow || (clauseLim != -1 && clauseSize[0] > clauseLim))
                )
                    return true

        // Delete and store old clauses:
        tr("ELIM ${v + 1} pos=${pos.size} neg=${neg.size}")
        eliminated[v] = 1
        setDecisionVar(v, false)
        eliminatedVars++

        if (pos.size > neg.size) {
            for (i in 0 until neg.size)
                mkElimClause(elimclauses, v, neg[i])
            mkElimClause(elimclauses, mkLit(v))
        } else {
            for (i in 0 until pos.size)
                mkElimClause(elimclauses, v, pos[i])
            mkElimClause(elimclauses, litNeg(mkLit(v)))
        }

        var k = 0
        while (k < cls.size) {   // cls.size() is re-read each iteration, as upstream
            removeClause(cls[k])
            k++
        }

        // Produce clauses in cross product:
        val resolvent = addTmp
        for (i in 0 until pos.size)
            for (j in 0 until neg.size)
                if (merge(pos[i], neg[j], v, resolvent) && !addClause_(resolvent))
                    return false

        // Free occurs list for this variable:
        occurs[v].clearFree()

        // Free watchers lists for this variable, if possible:
        if (watches[mkLit(v)].size == 0) watches[mkLit(v)].clearFree()
        if (watches[litNeg(mkLit(v))].size == 0) watches[litNeg(mkLit(v))].clearFree()

        return backwardSubsumptionCheck()
    }

    /** Alg.h find(ca[cr], p). */
    private fun clauseHas(cr: Int, p: Int): Boolean {
        for (j in 0 until ca.size(cr)) if (ca.lit(cr, j) == p) return true
        return false
    }

    /** Replace all occurences of v with x (may cause a contradiction). */
    fun substitute(v: Int, x: Int): Boolean {
        mAssert(frozen[v] == 0) { "substitute of frozen variable" }
        mAssert(!isEliminated(v)) { "substitute of eliminated variable" }
        mAssert(lbEq(valueVar(v), L_UNDEF)) { "substitute of assigned variable" }

        if (!ok) return false

        eliminated[v] = 1
        setDecisionVar(v, false)
        val cls = occurs.lookup(v)

        val substClause = addTmp
        var i = 0
        while (i < cls.size) {   // cls.size() is re-read each iteration, as upstream
            val c = cls[i]

            substClause.clear()
            for (j in 0 until ca.size(c)) {
                val p = ca.lit(c, j)
                substClause.push(if (litVar(p) == v) litXor(x, litSign(p)) else p)
            }

            removeClause(cls[i])

            if (!addClause_(substClause)) {
                ok = false; return false
            }
            i++
        }

        return true
    }

    protected fun extendModel() {
        var i = elimclauses.size - 1
        var j: Int

        while (i > 0) {
            j = elimclauses[i--]
            var skip = false
            while (j > 1) {
                if (!lbEq(modelValueLit(elimclauses[i]), L_FALSE)) { skip = true; break }
                j--; i--
            }

            if (!skip) {
                val x = elimclauses[i]
                model[litVar(x)] = lbOf(!litSign(x))
            }
            i -= j
        }
    }

    /** Perform variable elimination based simplification. */
    fun eliminate(turnOffElim: Boolean = false): Boolean {
        tr("START eliminate")
        try {
            return eliminateBody(turnOffElim)
        } finally {
            tr("END eliminate")
        }
    }

    private fun eliminateBody(turnOffElim: Boolean): Boolean {
        if (!simplify())
            return false
        else if (!useSimplification)
            return true

        // Main simplification loop:
        cleanup@ while (nTouched > 0 || bwdsubAssigns < trail.size || elimHeap.size() > 0) {

            gatherTouchedClauses()
            if ((subsumptionQueue.size() > 0 || bwdsubAssigns < trail.size) &&
                !backwardSubsumptionCheck(true)
            ) {
                ok = false; break@cleanup
            }

            // Empty elim_heap and return immediately on user-interrupt:
            if (asynchInterrupt) {
                mAssert(bwdsubAssigns == trail.size) { "eliminate: interrupt with pending assigns" }
                mAssert(subsumptionQueue.size() == 0) { "eliminate: interrupt with pending queue" }
                mAssert(nTouched == 0) { "eliminate: interrupt with touched vars" }
                elimHeap.clear()
                break@cleanup
            }

            var cnt = 0
            while (!elimHeap.empty()) {
                val elim = elimHeap.removeMin()

                if (asynchInterrupt) break

                if (isEliminated(elim) || !lbEq(valueVar(elim), L_UNDEF)) { cnt++; continue }

                if (verbosity >= 2 && cnt % 100 == 0)
                    print("elimination left: " + fmtD(elimHeap.size(), 10) + "\r")

                if (useAsymm) {
                    // Temporarily freeze variable. Otherwise, it would immediately end up on the queue again:
                    val wasFrozen = frozen[elim]
                    frozen[elim] = 1
                    if (!asymmVar(elim)) {
                        ok = false; break@cleanup
                    }
                    frozen[elim] = wasFrozen
                }

                // At this point, the variable may have been set by assymetric branching, so check it
                // again. Also, don't eliminate frozen variables:
                if (useElim && lbEq(valueVar(elim), L_UNDEF) && frozen[elim] == 0 && !eliminateVar(elim)) {
                    ok = false; break@cleanup
                }

                checkGarbage(simpGarbageFrac)
                cnt++
            }

            mAssert(subsumptionQueue.size() == 0) { "eliminate: subsumption queue not empty" }
        }
        // cleanup:

        // If no more simplification is needed, free all simplification-related data structures:
        if (turnOffElim) {
            touched.clearFree()
            occurs.clear()
            nOcc.clearFree()
            elimHeap.clear(true)
            subsumptionQueue.clear(true)

            useSimplification = false
            removeSatisfied = true
            ca.extraClauseField = false
            maxSimpVar = nVars()

            // Force full cleanup (this is safe and desirable since it only happens once):
            rebuildOrderHeap()
            garbageCollect()
        } else {
            // Cheaper cleanup:
            checkGarbage()
        }

        if (verbosity >= 1 && elimclauses.size > 0)
            println(
                "|  Eliminated clauses:     " + fmtF(elimclauses.size * 4.0 / (1024 * 1024), 10, 2) +
                    " Mb                                      |",
            )

        return ok
    }

    // =========================================================================================
    // Garbage Collection methods
    // =========================================================================================

    override fun relocAll(to: ClauseAllocator) {
        if (!useSimplification) return

        // All occurs lists:
        for (i in 0 until nVars()) {
            occurs.clean(i)
            val cs = occurs[i]
            for (j in 0 until cs.size)
                cs[j] = ca.reloc(cs[j], to)
        }

        // Subsumption queue:
        var i = subsumptionQueue.size()
        while (i > 0) {
            var cr = subsumptionQueue.peek(); subsumptionQueue.pop()
            i--
            if (ca.mark(cr) != 0) continue
            cr = ca.reloc(cr, to)
            subsumptionQueue.insert(cr)
        }

        // Temporary clause:
        bwdsubTmpunit = ca.reloc(bwdsubTmpunit, to)
    }

    override fun garbageCollect() {
        tr("GC simp")
        // Initialize the next region to a size corresponding to the estimated utilization degree.
        // This is not precise but should avoid some unnecessary reallocations for the new region:
        val to = ClauseAllocator(ca.size() - ca.wasted())

        to.extraClauseField = ca.extraClauseField // NOTE: this is important to keep (or lose) the extra fields.
        relocAll(to)
        solverRelocAll(to)
        if (verbosity >= 2)
            println(
                "|  Garbage collection:   " + fmtD(ca.size() * 4, 12) + " bytes => " +
                    fmtD(to.size() * 4, 12) + " bytes             |",
            )
        to.moveTo(ca)
    }
}
