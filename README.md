# minisat-kotlin

A [Kotlin Multiplatform](https://kotlinlang.org/docs/multiplatform.html) port of the
**MiniSat** SAT solver (Niklas Eén and Niklas Sörensson). Plain Kotlin, no FFI and no native library, so it
runs on any Kotlin target (JVM, Android, native, browser).

The MiniSat core CDCL solver. `double` VSIDS activities are computed in the same order as the C, so the trace matches on the tested instances.

It implements the `SatSolver` interface from
[ksat-common](https://github.com/manfredscheucher/ksat-common), which is pulled in as a
git submodule (mounted at `common/`). Package namespace is `org.bytefred.ksat`.

## Byte-for-byte port

This is a line-by-line port of the original C/C++ solver, checked to behave identically to
it (same decisions, propagations and conflicts, not just the final SAT/UNSAT answer). This
repo is just the solver source, usable on its own. The `Ksat` facade over all four solvers is
in the main repo **[sat-solvers-kotlin](https://github.com/manfredscheucher/sat-solvers-kotlin)**;
the verification harness, benchmarks and the multiplatform demo are in its optional
**[ksat-extra](https://github.com/manfredscheucher/ksat-extra)** submodule.

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
