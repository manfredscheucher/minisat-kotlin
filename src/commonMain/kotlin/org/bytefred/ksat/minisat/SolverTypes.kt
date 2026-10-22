package org.bytefred.ksat.minisat

/*
 * Kotlin port of MiniSat's core/SolverTypes.h and mtl/Alloc.h (RegionAllocator).
 * MiniSat (github.com/meelgroup/minisat 9a0382d; solver code identical to niklasso/minisat
 * 37dc6c6), MIT,
 * (c) 2003-2006 Niklas Een, Niklas Sorensson; (c) 2007-2010 Niklas Sorensson.
 */

// ---- Variables, literals ------------------------------------------------------------------
// Var is an Int (0..N-1). Lit is represented by its `x` field: x = var + var + sign.

const val VAR_UNDEF: Int = -1
const val LIT_UNDEF: Int = -2   // lit_Undef = { -2 }
const val LIT_ERROR: Int = -1   // lit_Error = { -1 }

fun mkLit(v: Int, sign: Boolean = false): Int = v + v + (if (sign) 1 else 0)
fun litNeg(p: Int): Int = p xor 1                              // operator ~
fun litXor(p: Int, b: Boolean): Int = p xor (if (b) 1 else 0)  // operator ^
fun litSign(p: Int): Boolean = (p and 1) != 0
fun litVar(p: Int): Int = p shr 1

// ---- Lifted booleans ----------------------------------------------------------------------
// lbool is its uint8 `value`: 0 = l_True, 1 = l_False, 2 = l_Undef (and 3 = l_Undef ^ true).

const val L_TRUE: Int = 0
const val L_FALSE: Int = 1
const val L_UNDEF: Int = 2

/** lbool::operator== : any value with bit 1 set is "undef". */
fun lbEq(a: Int, b: Int): Boolean = ((b and 2) and (a and 2)) != 0 || ((b and 2) == 0 && a == b)
fun lbXor(a: Int, b: Boolean): Int = a xor (if (b) 1 else 0)
/** `lbool(bool x)` : value = !x. */
fun lbOf(x: Boolean): Int = if (x) L_TRUE else L_FALSE

// ---- ClauseAllocator / RegionAllocator<uint32_t> -------------------------------------------

/** CRef_Undef = RegionAllocator<uint32_t>::Ref_Undef = UINT32_MAX. */
const val CREF_UNDEF: Int = -1

/**
 * mtl/Alloc.h `RegionAllocator<uint32_t>` + SolverTypes.h `ClauseAllocator` and `Clause`, with
 * the exact uint32 word layout, so CRef values, `size()`/`wasted()` (which trigger garbage
 * collection) and relocation behave exactly as upstream.
 *
 * Clause at CRef r: word r is the header bitfield (GCC little-endian bit allocation):
 * mark:2 (bits 0-1), learnt:1 (bit 2), has_extra:1 (bit 3), reloced:1 (bit 4), size:27 (bits 5-31).
 * Words r+1 .. r+size are the literals (data[i].lit); if has_extra, word r+1+size is the extra
 * field (float activity for learnts, uint32 abstraction otherwise). A relocated clause stores
 * its new CRef in data[0] (overwriting the first literal), exactly like upstream.
 */
class ClauseAllocator(startCap: Int = 1024 * 1024) {
    internal var memory = IntArray(0)
    private var sz = 0
    private var cap = 0
    private var wasted = 0

    var extraClauseField = false

    init { capacity(startCap) }

    private fun capacity(minCap: Int) {
        if (cap.toUInt() >= minCap.toUInt()) return
        val prevCap = cap
        while (cap.toUInt() < minCap.toUInt()) {
            // Multiply by a factor (13/8) without causing overflow, then add 2 and make the
            // result even by clearing the least significant bit.
            val delta = ((cap ushr 1) + (cap ushr 3) + 2) and 1.inv()
            cap += delta
            if (cap.toUInt() <= prevCap.toUInt()) throw IllegalStateException("MiniSat OutOfMemoryException")
        }
        mAssert(cap > 0) { "RegionAllocator capacity" }
        memory = memory.copyOf(cap)
    }

    private fun raAlloc(size: Int): Int {
        mAssert(size > 0) { "RegionAllocator::alloc size > 0" }
        capacity(sz + size)
        val prevSz = sz
        sz += size
        if (sz.toUInt() < prevSz.toUInt()) throw IllegalStateException("MiniSat OutOfMemoryException")
        return prevSz
    }

    fun size(): Int = sz
    fun wasted(): Int = wasted

    fun moveTo(to: ClauseAllocator) {
        to.extraClauseField = extraClauseField
        to.memory = memory
        to.sz = sz
        to.cap = cap
        to.wasted = wasted
        memory = IntArray(0)
        sz = 0; cap = 0; wasted = 0
    }

    /** ClauseAllocator::alloc(const vec<Lit>& ps, bool learnt). */
    fun alloc(ps: IntVec, learnt: Boolean = false): Int {
        val useExtra = learnt or extraClauseField
        val n = ps.size
        val cid = raAlloc(clauseWord32Size(n, useExtra))
        val m = memory
        m[cid] = header(0, learnt, useExtra, false, n)
        for (i in 0 until n) m[cid + 1 + i] = ps[i]
        if (useExtra) {
            if (learnt) m[cid + 1 + n] = 0f.toRawBits()
            else calcAbstraction(cid)
        }
        return cid
    }

    /** ClauseAllocator::alloc(const Clause& from) where `from` lives in [fromCa]. */
    private fun allocFrom(fromCa: ClauseAllocator, from: Int): Int {
        val fm = fromCa.memory
        val fromHeader = fm[fromCa.ref(from)]
        val fromLearnt = (fromHeader and 4) != 0
        val n = fromHeader ushr 5
        val useExtra = fromLearnt or extraClauseField
        val cid = raAlloc(clauseWord32Size(n, useExtra))
        val m = memory
        // header = from.header; header.has_extra = use_extra;
        m[cid] = (fromHeader and 8.inv()) or (if (useExtra) 8 else 0)
        for (i in 0 until n) m[cid + 1 + i] = fm[from + 1 + i]
        if (useExtra) {
            // data[size].act / .abs = from.data[size] (raw word copy; both are 32 bits).
            m[cid + 1 + n] = fm[from + 1 + n]
        }
        return cid
    }

    fun free(cid: Int) {
        val h = memory[cid]
        wasted += clauseWord32Size(h ushr 5, (h and 8) != 0)
    }

    /** ClauseAllocator::reloc(CRef& cr, ClauseAllocator& to): returns the new value of cr. */
    fun reloc(cr: Int, to: ClauseAllocator): Int {
        if (reloced(cr)) return relocation(cr)
        val n = to.allocFrom(this, cr)
        relocate(cr, n)
        return n
    }

    /** RegionAllocator::operator[] / lea: `assert(r < sz)` (kept as a check). */
    private fun ref(cr: Int): Int {
        if (cr.toUInt() >= sz.toUInt())
            throw IllegalStateException("MiniSat assertion failed: CRef $cr out of range (size $sz)")
        return cr
    }

    // ---- Clause accessors (Clause& c = ca[cr]) ----
    fun size(cr: Int): Int = memory[ref(cr)] ushr 5
    fun learnt(cr: Int): Boolean = (memory[ref(cr)] and 4) != 0
    fun hasExtra(cr: Int): Boolean = (memory[ref(cr)] and 8) != 0
    fun mark(cr: Int): Int = memory[ref(cr)] and 3
    fun mark(cr: Int, m: Int) { memory[ref(cr)] = (memory[cr] and 3.inv()) or (m and 3) }
    fun reloced(cr: Int): Boolean = (memory[ref(cr)] and 16) != 0
    fun relocation(cr: Int): Int = memory[ref(cr) + 1]
    fun relocate(cr: Int, c: Int) { memory[ref(cr)] = memory[cr] or 16; memory[cr + 1] = c }

    fun lit(cr: Int, i: Int): Int = memory[ref(cr) + 1 + i]
    fun setLit(cr: Int, i: Int, p: Int) { memory[ref(cr) + 1 + i] = p }
    fun last(cr: Int): Int = memory[cr + size(cr)]

    fun activity(cr: Int): Float {
        mAssert(hasExtra(cr)) { "Clause::activity without extra field" }
        return Float.fromBits(memory[cr + 1 + size(cr)])
    }
    fun setActivity(cr: Int, a: Float) {
        mAssert(hasExtra(cr)) { "Clause::activity without extra field" }
        memory[cr + 1 + size(cr)] = a.toRawBits()
    }
    fun abstraction(cr: Int): Int {
        mAssert(hasExtra(cr)) { "Clause::abstraction without extra field" }
        return memory[cr + 1 + size(cr)]
    }

    fun calcAbstraction(cr: Int) {
        mAssert(hasExtra(cr)) { "Clause::calcAbstraction without extra field" }
        var abstraction = 0
        val n = size(cr)
        for (i in 0 until n) abstraction = abstraction or (1 shl (litVar(memory[cr + 1 + i]) and 31))
        memory[cr + 1 + n] = abstraction
    }

    /** Clause::shrink(i): moves the extra field down, then reduces the size. */
    fun shrink(cr: Int, i: Int) {
        val n = size(cr)
        mAssert(i <= n) { "Clause::shrink" }
        if (hasExtra(cr)) memory[cr + 1 + n - i] = memory[cr + 1 + n]
        memory[cr] = (memory[cr] and 31) or ((n - i) shl 5)
    }
    fun pop(cr: Int) = shrink(cr, 1)

    /**
     * Clause::subsumes(other): lit_Error = no subsumption or simplification, lit_Undef = this
     * clause subsumes [other], p = the literal p can be deleted from [other].
     */
    fun subsumes(cr: Int, other: Int): Int {
        mAssert(!learnt(cr) && !learnt(other)) { "subsumes on learnt clause" }
        mAssert(hasExtra(cr) && hasExtra(other)) { "subsumes without extra field" }
        val n = size(cr)
        val on = size(other)
        if (on < n || (memory[cr + 1 + n] and memory[other + 1 + on].inv()) != 0)
            return LIT_ERROR

        var ret = LIT_UNDEF
        val m = memory
        for (i in 0 until n) {
            // search for c[i] or ~c[i]
            var found = false
            val ci = m[cr + 1 + i]
            for (j in 0 until on) {
                val dj = m[other + 1 + j]
                if (ci == dj) {
                    found = true; break
                } else if (ret == LIT_UNDEF && ci == litNeg(dj)) {
                    ret = ci
                    found = true; break
                }
            }
            // did not find it
            if (!found) return LIT_ERROR
        }
        return ret
    }

    /** Clause::strengthen(p): remove(*this, p); calcAbstraction(). */
    fun strengthen(cr: Int, p: Int) {
        val n = size(cr)
        var j = 0
        while (j < n && lit(cr, j) != p) j++
        mAssert(j < n) { "remove: element not found" }
        while (j < n - 1) { setLit(cr, j, lit(cr, j + 1)); j++ }
        pop(cr)
        calcAbstraction(cr)
    }

    companion object {
        /** (sizeof(Clause) + sizeof(Lit) * (size + has_extra)) / sizeof(uint32_t). */
        fun clauseWord32Size(size: Int, hasExtra: Boolean): Int = 1 + size + (if (hasExtra) 1 else 0)

        private fun header(mark: Int, learnt: Boolean, hasExtra: Boolean, reloced: Boolean, size: Int): Int =
            (mark and 3) or (if (learnt) 4 else 0) or (if (hasExtra) 8 else 0) or
                (if (reloced) 16 else 0) or (size shl 5)
    }
}

// ---- OccLists ---------------------------------------------------------------------------

/** `vec<Watcher>`: interleaved (cref, blocker) pairs; Watcher== compares cref only. */
class WatchVec {
    internal var data = IntArray(8)
    var size = 0
        internal set

    fun cref(i: Int): Int = data[2 * i]
    fun blocker(i: Int): Int = data[2 * i + 1]
    fun push(cref: Int, blocker: Int) {
        if (2 * size + 2 > data.size) data = data.copyOf(data.size * 2)
        data[2 * size] = cref; data[2 * size + 1] = blocker
        size++
    }
    fun shrink(n: Int) { mAssert(n <= size) { "vec::shrink" }; size -= n }
    fun clear() { size = 0 }
    fun clearFree() { size = 0; data = IntArray(8) }

    /** Alg.h remove(ws, Watcher(cr, _)): first watcher with this cref. */
    fun remove(cr: Int) {
        var j = 0
        while (j < size && data[2 * j] != cr) j++
        mAssert(j < size) { "remove: watcher not found" }
        while (j < size - 1) { data[2 * j] = data[2 * j + 2]; data[2 * j + 1] = data[2 * j + 3]; j++ }
        size--
    }
}

/**
 * SolverTypes.h `OccLists<K, Vec, Deleted>` with lazy deletion (dirty flags + dirties list).
 * [Watches] instantiates it for `OccLists<Lit, vec<Watcher>, WatcherDeleted>`; [CRefOccLists]
 * for SimpSolver's `OccLists<Var, vec<CRef>, ClauseDeleted>`. Deleted = `ca[cref].mark() == 1`.
 */
class Watches(private val ca: ClauseAllocator) {
    private var occs = arrayOfNulls<WatchVec>(0)
    private var occsSize = 0
    private val dirty = IntVec()
    private val dirties = IntVec()

    fun init(idx: Int) {
        if (occsSize < idx + 1) {
            if (occs.size < idx + 1) occs = occs.copyOf(maxOf(idx + 1, occs.size * 2))
            for (k in occsSize..idx) occs[k] = WatchVec()
            occsSize = idx + 1
        }
        occs[idx]!!.clear()
        dirty.reserve(idx, 0)
    }

    operator fun get(idx: Int): WatchVec = occs[idx]!!
    fun lookup(idx: Int): WatchVec { if (dirty[idx] != 0) clean(idx); return occs[idx]!! }

    fun cleanAll() {
        for (i in 0 until dirties.size)
            // Dirties may contain duplicates so check here if a variable is already cleaned:
            if (dirty[dirties[i]] != 0) clean(dirties[i])
        dirties.clear()
    }

    fun clean(idx: Int) {
        val vec = occs[idx]!!
        var i = 0; var j = 0
        val d = vec.data
        while (i < vec.size) {
            if (ca.mark(d[2 * i]) != 1) { d[2 * j] = d[2 * i]; d[2 * j + 1] = d[2 * i + 1]; j++ }
            i++
        }
        vec.shrink(i - j)
        dirty[idx] = 0
    }

    fun smudge(idx: Int) {
        if (dirty[idx] == 0) {
            dirty[idx] = 1
            dirties.push(idx)
        }
    }
}

class CRefOccLists(private val ca: ClauseAllocator) {
    private var occs = arrayOfNulls<IntVec>(0)
    private var occsSize = 0
    private val dirty = IntVec()
    private val dirties = IntVec()

    fun init(idx: Int) {
        if (occsSize < idx + 1) {
            if (occs.size < idx + 1) occs = occs.copyOf(maxOf(idx + 1, occs.size * 2))
            for (k in occsSize..idx) occs[k] = IntVec()
            occsSize = idx + 1
        }
        occs[idx]!!.clear()
        dirty.reserve(idx, 0)
    }

    operator fun get(idx: Int): IntVec {
        mAssert(idx < occsSize) { "IntMap: key $idx not present" }
        return occs[idx]!!
    }
    fun lookup(idx: Int): IntVec { if (dirty[idx] != 0) clean(idx); return get(idx) }

    fun cleanAll() {
        for (i in 0 until dirties.size)
            if (dirty[dirties[i]] != 0) clean(dirties[i])
        dirties.clear()
    }

    fun clean(idx: Int) {
        val vec = get(idx)
        var i = 0; var j = 0
        while (i < vec.size) {
            if (ca.mark(vec[i]) != 1) vec[j++] = vec[i]
            i++
        }
        vec.shrink(i - j)
        dirty[idx] = 0
    }

    fun smudge(idx: Int) {
        if (dirty[idx] == 0) {
            dirty[idx] = 1
            dirties.push(idx)
        }
    }

    /** OccLists::clear(free): drops all lists, dirty flags and the dirties list. */
    fun clear() {
        occs = arrayOfNulls(0)
        occsSize = 0
        dirty.clearFree()
        dirties.clearFree()
    }
}
