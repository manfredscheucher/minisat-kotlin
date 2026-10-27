package org.bytefred.ksat.minisat

/*
 * Port of the parts of MiniSat's utils/ParseUtils.h (meelgroup/minisat master 664490d; identical
 * in csb 9a0382d apart from formatting) that core/Dimacs.h uses. MIT, (c) 2003-2006 Niklas Een,
 * Niklas Sorensson; (c) 2007-2010 Niklas Sorensson.
 *
 * Differences from upstream:
 * - StreamBuffer reads from an in-memory byte array instead of a gzFile (gzread in 64 KB chunks);
 *   the byte sequence seen by the parser is the same. Bytes are unsigned (upstream: unsigned char).
 * - `fprintf(stderr, "PARSE ERROR! ...\n"), exit(3)` becomes a thrown [DimacsParseError] with the
 *   same message (without the newline).
 * - Not ported (unused by Dimacs.h): `StreamBuffer::position`, `isEof(const char*)`, `match`.
 */

/** EOF as returned by `StreamBuffer::operator*` (stdio's EOF). */
internal const val EOF = -1

/**
 * A DIMACS parse error. Upstream prints [message] (`PARSE ERROR! ...`) and calls `exit(3)`;
 * [toStderr] tells where upstream prints it: `parseInt` uses `fprintf(stderr, ...)`,
 * `parse_DIMACS_main` uses `printf` (stdout).
 */
class DimacsParseError(message: String, val toStderr: Boolean) : RuntimeException(message)

/** `printf("%c", ch)` of an `int` character (EOF prints as the byte 0xFF). */
internal fun pchar(ch: Int): Char = (ch and 0xFF).toChar()

/** A simple buffered character stream class (`StreamBuffer`). */
internal class StreamBuffer(private val buf: ByteArray) {
    private var pos = 0

    /** `operator*` */
    fun cur(): Int = if (pos >= buf.size) EOF else buf[pos].toInt() and 0xFF

    /** `operator++` */
    fun inc() { pos++ }
}

// End-of-file detection function for StreamBuffer:
internal fun isEof(inp: StreamBuffer): Boolean = inp.cur() == EOF

// Generic parse functions (upstream: templates over the input-stream type).

internal fun skipWhitespace(inp: StreamBuffer) {
    while ((inp.cur() >= 9 && inp.cur() <= 13) || inp.cur() == 32)
        inp.inc()
}

internal fun skipLine(inp: StreamBuffer) {
    while (true) {
        if (isEof(inp)) return
        if (inp.cur() == '\n'.code) { inp.inc(); return }
        inp.inc()
    }
}

internal fun parseInt(inp: StreamBuffer): Int {
    var v = 0
    var neg = false
    skipWhitespace(inp)
    if (inp.cur() == '-'.code) { neg = true; inp.inc() }
    else if (inp.cur() == '+'.code) inp.inc()
    if (inp.cur() < '0'.code || inp.cur() > '9'.code)
        throw DimacsParseError("PARSE ERROR! Unexpected char: ${pchar(inp.cur())}", toStderr = true)
    while (inp.cur() >= '0'.code && inp.cur() <= '9'.code) {
        v = v * 10 + (inp.cur() - '0'.code)   // wraps on overflow like the C int arithmetic
        inp.inc()
    }
    return if (neg) -v else v
}

/** String matching: consumes characters eagerly, but does not require random access iterator. */
internal fun eagerMatch(inp: StreamBuffer, str: String): Boolean {
    for (ch in str) {
        if (ch.code != inp.cur()) return false
        inp.inc()
    }
    return true
}
