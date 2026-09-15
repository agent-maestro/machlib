/-!
# `CertcomLibm` — C library functions Lean core does not bind

Lean v4.32.2 core binds `exp`, `log`, `sin` and the rest as `Float` externs its interpreter can run, and has no
`Float.expm1`. `Certcom.Prims.expm1` (`MachLib/EMLToCRuntime.lean`) needs one for `leanPrims`: forge's
`libmonogate.h` computes `mg_sinh` and `mg_tanh` from libm `expm1` since 2026-09-15, and the `native_decide`
examples there, like `tools/float_bridge/measure.py`'s cross-check, evaluate those bodies.

**Why a library of its own, compiled.** A plain `@[extern "expm1"] opaque` elaborates, but the interpreter cannot
run it: `#eval` aborts with "Could not find native implementation of external declaration". This file is its own
`lean_lib` with `precompileModules := true` (`lakefile.lean`). Lake compiles it to a shared library with the
toolchain's bundled `clang`, which the GitHub-hosted runner's toolchain also ships, and loads that library into the
Lean process for every module that imports this one, under `lake build` and under `lake lean <file>`. The call
resolves to the platform libm's `expm1`, the function the C runtime calls; `tools/float_bridge/measure.py` compares
the two bit for bit on every run.

**Trap: `lake env lean <file>` does not load the library.** A file run that way aborts when it EVALUATES a call that
reaches `floatExpm1`. Elaborating, `#print axioms`, and evaluating anything that does not reach the call still work,
because the interpreter resolves an extern only when it is called. Use `lake lean <file>`.

An `opaque` with `@[extern]` is how core declares `Float.exp` itself, so this adds no axiom. Evaluating it rests on
the compiler, as evaluating `Float.exp` does (`Lean.ofReduceBool` under `native_decide`), not on a project axiom.
-/

namespace Certcom

/-- C `expm1(x)`: `eˣ − 1`, rounded by the platform libm. Evaluated through this module's shared library. -/
@[extern "expm1"] opaque floatExpm1 : Float → Float

end Certcom
