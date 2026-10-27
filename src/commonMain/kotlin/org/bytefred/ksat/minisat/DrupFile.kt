package org.bytefred.ksat.minisat

/**
 * The `FILE* drup_file` of meelgroup/minisat master (commit 1d1940a "Adding DRUP"): the byte
 * level output of the DRUP/DRAT proof that [MiniSat.drupFile] writes to.
 *
 * Upstream writes the proof with `fprintf` (ASCII, one call per literal and per `0\n`) or with
 * `fwrite_unlocked` of its proof buffer (binary, `binDRUP_flush`). Only the byte stream matters,
 * so both arrive here as [write] calls; the ASCII proof is written one clause (one line) per call.
 * Buffering, flushing and closing the underlying file are the caller's business (upstream's
 * simp/Main.cc does `fclose` on its own).
 */
fun interface DrupFile {
    /** Append `buf[off until off + len]` to the proof (`fwrite (buf + off, 1, len, drup_file)`). */
    fun write(buf: ByteArray, off: Int, len: Int)
}
