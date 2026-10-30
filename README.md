# minisat-kotlin

A [Kotlin Multiplatform](https://kotlinlang.org/docs/multiplatform.html) port of the
**MiniSat** SAT solver (Niklas Eén and Niklas Sörensson). Plain Kotlin, no FFI and no native library, so it
runs on any Kotlin target (JVM, Android, native, browser).

All of MiniSat, ported from the maintained fork [meelgroup/minisat](https://github.com/meelgroup/minisat),
branch `master` (commit 664490d: niklasso/minisat 37dc6c6 plus DRUP/DRAT proofs and the option
rdb-at), with four upstream bugs fixed. Its `csb` line (9a0382d, niklasso 37dc6c6 plus compile
fixes) is reproduced exactly with `csbCompat = true`. The port covers the core CDCL
solver `MiniSat` (core/Solver) and the preprocessing solver `MiniSatSimp` (simp/SimpSolver:
subsumption, variable elimination, asymmetric branching, model extension), including the clause
allocator and garbage collection word for word, so traces match the C on the tested instances.

It implements the `SatSolver` interface from
[ksat-common](https://github.com/manfredscheucher/ksat-common), which is pulled in as a
git submodule (mounted at `common/`). Package namespace is `org.bytefred.ksat`.

## Byte-for-byte port

This is a line-by-line port of the original C/C++ solver, checked to behave identically to
it (same decisions, propagations and conflicts, not just the final SAT/UNSAT answer). This
repo is just the solver source, usable on its own. The `Ksat` facade over all four solvers is
in the main repo **[ksat](https://github.com/manfredscheucher/ksat)**;
the verification harness, benchmarks and the multiplatform demo are in its optional
**[ksat-extra](https://github.com/manfredscheucher/ksat-extra)** submodule.

## Reading DIMACS

`parseDimacs(text, solver, strictp = false)` is MiniSat's own parser (core/Dimacs.h): clauses go
into the solver one by one through `addClause_`, variables are created as they appear, all clauses
are read (also beyond the header count), and malformed input throws `DimacsParseError` with
upstream's `PARSE ERROR! ...` message (upstream exits with 3).

## Proofs, rdb-at, csb switch

From meelgroup's `master`: DRUP/DRAT proof output and the option `rdb-at` (reduceDB every k
conflicts), both off by default.

```kotlin
val out = java.io.FileOutputStream("proof.drat")      // any byte sink
val s = MiniSatSimp()
s.drupFile = DrupFile { buf, off, len -> out.write(buf, off, len) }
s.binDrup = true            // binary DRAT (master's default); false = ASCII DRUP
s.parsing = true            // as master's simp/Main.cc: no proof lines for the input clauses
// ... add the clauses ...
s.parsing = false
s.eliminate(true)
val ret = if (s.okay()) s.solveLimited(IntVec()) else L_FALSE
s.binDRUPFlush()            // write the pending binary proof (upstream never does this here)
if (lbEq(ret, L_FALSE)) out.write(byteArrayOf('a'.code.toByte(), 0))   // final empty clause ("0\n" in ASCII)
out.close()
```

As upstream, the binary proof goes through a 2 MB buffer; call `binDRUPFlush()` before closing
the proof. `reduceDBAtConfl = k` is master's `-rdb-at=k`. `csbCompat = true` reproduces csb 9a0382d
(the only behaviour difference: master deletes an eliminated variable's clauses after adding the
resolvents, csb before). Fixed upstream bugs, the decisions and the verification:
[ksat-extra/doc/minisat-full-port.md](https://github.com/manfredscheucher/ksat-extra).

## Build

Requires a JDK and the Gradle wrapper in this repo. `ksat-common` is a git submodule
mounted at `common/`, so clone recursively (a plain `git clone` leaves it empty and the
build fails with `No matching variant of project :ksat-common`):

```bash
git clone --recursive https://github.com/manfredscheucher/minisat-kotlin.git
cd minisat-kotlin
```

Already cloned without `--recursive`? Pull the submodule in:

```bash
git submodule update --init --recursive
```

Then build:

```bash
./gradlew compileKotlinJvm   # or build for all targets
```

## License

MIT, see [LICENSE](LICENSE). This port is a derivative work of the MIT-licensed original
(Niklas Eén and Niklas Sörensson); the original license text is preserved in [LICENSE](LICENSE).
