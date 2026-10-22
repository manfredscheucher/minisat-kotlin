package org.bytefred.ksat.minisat

/*
 * Kotlin port of MiniSat's mtl/ (Vec.h, Alg.h, Sort.h, Heap.h, Queue.h, IntMap.h) as far as
 * the solver uses it. MiniSat (github.com/meelgroup/minisat 9a0382d; solver code identical to
 * niklasso/minisat 37dc6c6), MIT,
 * (c) 2003-2006 Niklas Een, Niklas Sorensson; (c) 2007-2010 Niklas Sorensson.
 *
 * Only Int/Double element types are needed (Var, Lit.x, CRef, lbool, char and int maps are all
 * Ints here), so the templates become IntVec/DoubleVec. Growth policy (capacity) is not
 * observable and is left to the JVM-style doubling; every ORDER-relevant algorithm (sort,
 * heap, queue, remove) is translated literally.
 *
 * Element access ([IntVec.get]/[IntVec.set]) is checked against the size: IntMap::operator[]
 * asserts `has(k)` upstream (kept as a check, PORTING rule "plain assert -> check"); for a plain
 * vec, an index >= size would be undefined behaviour upstream, so the check cannot change a
 * result on any execution where the port matches upstream.
 */

/** Translation of an upstream `assert`: fail loudly exactly where upstream asserts. */
internal inline fun mAssert(cond: Boolean, msg: () -> String) {
    if (!cond) throw IllegalStateException("MiniSat assertion failed: " + msg())
}

/** mtl/Vec.h `vec<int>` (also used for IntMap<K,int/char/lbool> with an int key). */
class IntVec(initialSize: Int = 0, pad: Int = 0) {
    internal var data = IntArray(maxOf(4, initialSize))
    var size = 0
        private set

    init {
        if (initialSize > 0) growTo(initialSize, pad)
    }

    operator fun get(i: Int): Int {
        if (i >= size) indexError(i, size)
        return data[i]
    }
    operator fun set(i: Int, v: Int) {
        if (i >= size) indexError(i, size)
        data[i] = v
    }

    fun last(): Int = data[size - 1]
    fun push(x: Int) {
        if (size == data.size) data = data.copyOf(data.size * 2)
        data[size++] = x
    }
    fun pop() { mAssert(size > 0) { "vec::pop on empty vec" }; size-- }
    fun shrink(n: Int) { mAssert(n <= size) { "vec::shrink" }; size -= n }
    fun clear() { size = 0 }

    /** vec::clear(true): drop the storage as well. */
    fun clearFree() { size = 0; data = IntArray(4) }

    fun capacity(minCap: Int) {
        if (data.size < minCap) data = data.copyOf(maxOf(minCap, data.size * 2))
    }

    /** vec::growTo(size, pad): only grows; new elements are [pad]. */
    fun growTo(n: Int, pad: Int = 0) {
        if (size >= n) return
        capacity(n)
        for (i in size until n) data[i] = pad
        size = n
    }

    fun copyTo(to: IntVec) {
        to.clear()
        to.growTo(size)
        for (i in 0 until size) to.data[i] = data[i]
    }

    fun toIntArray(): IntArray = data.copyOf(size)
}

/** IntMap::operator[] `assert(has(k))` (see the file header). */
internal fun indexError(i: Int, size: Int): Nothing =
    throw IllegalStateException("MiniSat assertion failed: index $i out of range (size $size)")

/** mtl/Vec.h `vec<double>` (VMap<double> activity). */
class DoubleVec {
    internal var data = DoubleArray(4)
    var size = 0
        private set

    operator fun get(i: Int): Double {
        if (i >= size) indexError(i, size)
        return data[i]
    }
    operator fun set(i: Int, v: Double) {
        if (i >= size) indexError(i, size)
        data[i] = v
    }

    fun growTo(n: Int, pad: Double = 0.0) {
        if (size >= n) return
        if (data.size < n) data = data.copyOf(maxOf(n, data.size * 2))
        for (i in size until n) data[i] = pad
        size = n
    }

    /** IntMap::insert(key, val): reserve(key) then set. */
    fun insert(key: Int, v: Double) { growTo(key + 1); data[key] = v }
}

/** IntMap::insert(key, val) / reserve(key, pad) for an IntVec-backed map. */
internal fun IntVec.insert(key: Int, v: Int, pad: Int = 0) { growTo(key + 1, pad); this[key] = v }
internal fun IntVec.reserve(key: Int, pad: Int = 0) { growTo(key + 1, pad) }
internal fun IntVec.has(key: Int): Boolean = key < size

/** mtl/Alg.h `remove(ts, t)`: delete the FIRST occurrence of [t], shifting the tail left. */
internal fun removeFirst(ts: IntVec, t: Int) {
    var j = 0
    while (j < ts.size && ts[j] != t) j++
    mAssert(j < ts.size) { "remove: element not found" }
    while (j < ts.size - 1) { ts[j] = ts[j + 1]; j++ }
    ts.pop()
}

/** mtl/Alg.h `append(from, to)`. */
internal fun append(from: IntVec, to: IntVec) {
    for (i in 0 until from.size) to.push(from[i])
}

/** A `LessThan` functor over Int keys (mtl/Sort.h, Heap.h `Comp`). */
fun interface IntLessThan {
    fun lt(x: Int, y: Int): Boolean
}

// ---- mtl/Sort.h --------------------------------------------------------------------------

private fun selectionSort(array: IntArray, from: Int, size: Int, lt: IntLessThan) {
    var i = 0
    while (i < size - 1) {
        var bestI = i
        var j = i + 1
        while (j < size) {
            if (lt.lt(array[from + j], array[from + bestI])) bestI = j
            j++
        }
        val tmp = array[from + i]; array[from + i] = array[from + bestI]; array[from + bestI] = tmp
        i++
    }
}

private fun sortRange(array: IntArray, from: Int, size: Int, lt: IntLessThan) {
    if (size <= 15) {
        selectionSort(array, from, size, lt)
    } else {
        val pivot = array[from + size / 2]
        var i = -1
        var j = size
        while (true) {
            do i++ while (lt.lt(array[from + i], pivot))
            do j-- while (lt.lt(pivot, array[from + j]))
            if (i >= j) break
            val tmp = array[from + i]; array[from + i] = array[from + j]; array[from + j] = tmp
        }
        sortRange(array, from, i, lt)
        sortRange(array, from + i, size - i, lt)
    }
}

/** mtl/Sort.h `sort(vec, lt)` (NOT stable: selection sort <= 15, else quicksort, pivot middle). */
fun sort(v: IntVec, lt: IntLessThan) = sortRange(v.data, 0, v.size, lt)

/** mtl/Sort.h `sort(vec)` with LessThan_default (for Lit: compares Lit.x). */
fun sort(v: IntVec) = sortRange(v.data, 0, v.size) { x, y -> x < y }

// ---- mtl/Heap.h --------------------------------------------------------------------------

/** mtl/Heap.h `Heap<K, Comp>` over Int keys: a min-heap w.r.t. [lt], with decrease/increase. */
class IntHeap(private val lt: IntLessThan) {
    private val heap = IntVec()         // Heap of Keys
    private val indices = IntVec()      // Each Key's position (index) in the Heap

    private fun left(i: Int) = i * 2 + 1
    private fun right(i: Int) = (i + 1) * 2
    private fun parent(i: Int) = (i - 1) shr 1

    private fun percolateUp(i0: Int) {
        var i = i0
        val x = heap[i]
        var p = parent(i)
        while (i != 0 && lt.lt(x, heap[p])) {
            heap[i] = heap[p]
            indices[heap[p]] = i
            i = p
            p = parent(p)
        }
        heap[i] = x
        indices[x] = i
    }

    private fun percolateDown(i0: Int) {
        var i = i0
        val x = heap[i]
        while (left(i) < heap.size) {
            val child = if (right(i) < heap.size && lt.lt(heap[right(i)], heap[left(i)])) right(i) else left(i)
            if (!lt.lt(heap[child], x)) break
            heap[i] = heap[child]
            indices[heap[i]] = i
            i = child
        }
        heap[i] = x
        indices[x] = i
    }

    fun size(): Int = heap.size
    fun empty(): Boolean = heap.size == 0
    fun inHeap(k: Int): Boolean = indices.has(k) && indices[k] >= 0
    operator fun get(index: Int): Int { mAssert(index < heap.size) { "heap index" }; return heap[index] }

    fun decrease(k: Int) { mAssert(inHeap(k)) { "heap decrease" }; percolateUp(indices[k]) }
    fun increase(k: Int) { mAssert(inHeap(k)) { "heap increase" }; percolateDown(indices[k]) }

    /** Safe variant of insert/decrease/increase. */
    fun update(k: Int) {
        if (!inHeap(k)) {
            insert(k)
        } else {
            percolateUp(indices[k])
            percolateDown(indices[k])
        }
    }

    fun insert(k: Int) {
        indices.reserve(k, -1)
        mAssert(!inHeap(k)) { "heap insert of present key $k" }
        indices[k] = heap.size
        heap.push(k)
        percolateUp(indices[k])
    }

    fun remove(k: Int) {
        mAssert(inHeap(k)) { "heap remove" }
        val kPos = indices[k]
        indices[k] = -1
        if (kPos < heap.size - 1) {
            heap[kPos] = heap.last()
            indices[heap[kPos]] = kPos
            heap.pop()
            percolateDown(kPos)
        } else {
            heap.pop()
        }
    }

    fun removeMin(): Int {
        val x = heap[0]
        heap[0] = heap.last()
        indices[heap[0]] = 0
        indices[x] = -1
        heap.pop()
        if (heap.size > 1) percolateDown(0)
        return x
    }

    /** Rebuild the heap from scratch, using the elements in [ns]. */
    fun build(ns: IntVec) {
        for (i in 0 until heap.size) indices[heap[i]] = -1
        heap.clear()
        for (i in 0 until ns.size) {
            mAssert(indices.has(ns[i])) { "heap build: key not reserved" }
            indices[ns[i]] = i
            heap.push(ns[i])
        }
        var i = heap.size / 2 - 1
        while (i >= 0) { percolateDown(i); i-- }
    }

    fun clear(dispose: Boolean = false) {
        for (i in 0 until heap.size) indices[heap[i]] = -1
        if (dispose) heap.clearFree() else heap.clear()
    }
}

// ---- mtl/Queue.h -------------------------------------------------------------------------

/** mtl/Queue.h `Queue<T>` (ring buffer; resize keeps FIFO order). */
class IntQueue {
    private var buf = IntVec(1)
    private var first = 0
    private var end = 0

    fun clear(dealloc: Boolean = false) {
        if (dealloc) buf.clearFree() else buf.clear()
        buf.growTo(1)
        first = 0; end = 0
    }

    fun size(): Int = if (end >= first) end - first else end - first + buf.size

    operator fun get(index: Int): Int {
        mAssert(index >= 0 && index < size()) { "queue index" }
        return buf[(first + index) % buf.size]
    }

    fun peek(): Int { mAssert(first != end) { "queue peek on empty" }; return buf[first] }

    fun pop() {
        mAssert(first != end) { "queue pop on empty" }
        first++
        if (first == buf.size) first = 0
    }

    fun insert(elem: Int) {   // INVARIANT: buf[end] is always unused
        buf[end++] = elem
        if (end == buf.size) end = 0
        if (first == end) {   // Resize:
            val tmp = IntVec((buf.size * 3 + 1) shr 1)
            var i = 0
            for (j in first until buf.size) tmp[i++] = buf[j]
            for (j in 0 until end) tmp[i++] = buf[j]
            first = 0
            end = buf.size
            buf = tmp
        }
    }
}

// ---- mtl/IntMap.h IntSet (LSet) ----------------------------------------------------------

/** mtl/IntMap.h `IntSet<Lit>` (`LSet`): insertion-ordered set without duplicates. */
class LitSet {
    private val inSet = IntVec()
    private val xs = IntVec()

    fun size(): Int = xs.size
    fun clear() {
        for (i in 0 until xs.size) inSet[xs[i]] = 0
        xs.clear()
    }
    operator fun get(index: Int): Int = xs[index]
    fun insert(k: Int) {
        inSet.reserve(k, 0)
        if (inSet[k] == 0) { inSet[k] = 1; xs.push(k) }
    }
    fun has(k: Int): Boolean {
        inSet.reserve(k, 0)
        return inSet[k] != 0
    }
    fun toIntArray(): IntArray = xs.toIntArray()
}
