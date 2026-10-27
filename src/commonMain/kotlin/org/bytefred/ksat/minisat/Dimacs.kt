package org.bytefred.ksat.minisat

import kotlin.math.abs

/*
 * Port of MiniSat's DIMACS parser, core/Dimacs.h (meelgroup/minisat master 664490d; identical in
 * csb 9a0382d apart from formatting). MIT, (c) 2003-2006 Niklas Een, Niklas Sorensson;
 * (c) 2007-2010 Niklas Sorensson.
 *
 * Upstream behaviour, kept as is:
 * - the header `p cnf <vars> <clauses>` is optional and its numbers are not used (variables are
 *   created lazily by readClause); every clause in the input is read, also beyond the header count;
 * - a line starting with `c` (after whitespace, between clauses) is a comment, also on the same line
 *   after a clause's `0`; a `c` inside a clause is a parse error;
 * - `PARSE ERROR! Unexpected char: <c>` + exit(3) (here: [DimacsParseError]) for a `p` line that is
 *   not exactly `p cnf`, and wherever a number is expected and none follows (e.g. the last clause
 *   without its `0`: EOF, printed as the byte 0xFF);
 * - strict mode only PRINTS `PARSE ERROR! DIMACS header mismatch: wrong number of clauses` (printf,
 *   no exit) and keeps the clauses; [out] receives that line (upstream: stdout).
 */

/** `readClause`: one clause up to its terminating 0; creates missing variables with newVar(). */
private fun readClause(inp: StreamBuffer, s: MiniSat, lits: IntVec) {
    lits.clear()
    while (true) {
        val parsedLit = parseInt(inp)
        if (parsedLit == 0) break
        val v = abs(parsedLit) - 1
        while (v >= s.nVars()) s.newVar()
        lits.push(if (parsedLit > 0) mkLit(v) else litNeg(mkLit(v)))
    }
}

/** `parse_DIMACS_main` */
private fun parseDimacsMain(inp: StreamBuffer, s: MiniSat, strictp: Boolean, out: (String) -> Unit) {
    val lits = IntVec()
    var vars = 0   // read, not used (as upstream)
    var clauses = 0
    var cnt = 0
    while (true) {
        skipWhitespace(inp)
        if (inp.cur() == EOF) break
        else if (inp.cur() == 'p'.code) {
            if (eagerMatch(inp, "p cnf")) {
                vars = parseInt(inp)
                clauses = parseInt(inp)
                // SATRACE'06 hack
                // if (clauses > 4000000)
                //     S.eliminate(true);
            } else {
                throw DimacsParseError("PARSE ERROR! Unexpected char: ${pchar(inp.cur())}", toStderr = false)
            }
        } else if (inp.cur() == 'c'.code || inp.cur() == 'p'.code)
            skipLine(inp)
        else {
            cnt++
            readClause(inp, s, lits)
            s.addClause_(lits)
        }
    }
    if (strictp && cnt != clauses)
        out("PARSE ERROR! DIMACS header mismatch: wrong number of clauses")
}

/**
 * `parse_DIMACS(input_stream, S, strictp)`: inserts the problem in [input] (DIMACS bytes) into [s],
 * clause by clause through `addClause_`, exactly as upstream. Throws [DimacsParseError] where
 * upstream exits with code 3; clauses read before the error are already added (as upstream).
 */
fun parseDimacs(input: ByteArray, s: MiniSat, strictp: Boolean = false, out: (String) -> Unit = { println(it) }) {
    parseDimacsMain(StreamBuffer(input), s, strictp, out)
}

/** [parseDimacs] of [text] (UTF-8 bytes). */
fun parseDimacs(text: String, s: MiniSat, strictp: Boolean = false, out: (String) -> Unit = { println(it) }) =
    parseDimacs(text.encodeToByteArray(), s, strictp, out)
