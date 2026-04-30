-- MonogateEML/Float64.lean
--
-- Floating-point (IEEE 754 double-precision / f64) reasoning layer
-- for the EML runtime.
--
-- Purpose: this file is the planned home for libm correctness
-- postulates that translate the real-valued bounds proved in
-- `MonogateEML/Runtime.lean` and `MonogateEML/UpperBounds.lean`
-- into per-operation f64 ulp guarantees.
--
-- Status (2026-04-29): scaffolding only. The framework is laid out
-- below as `ULPBound` records; concrete axioms tying specific
-- platforms (glibc / musl / Rust libm / Apple Accelerate) to
-- specific ulp envelopes are NOT yet introduced. This file is
-- therefore sorry-free AND axiom-free. Adding concrete axioms is
-- a deliberate per-platform decision requiring offline validation
-- against the GNU libm test harness (`libm-test-ulps`).
--
-- The first real-valued precision bound this file supports is
-- `MonogateEML.Runtime.mg_softplus_route_bound_high`, which proves
-- |softplus_route(x) - softplus(x)| < exp(-20) for x > 20 in pure ℝ.
-- An f64 ulp version of that bound would compose with libm's exp/log
-- ulp guarantees through the framework introduced below.

import MonogateEML.Runtime

namespace MonogateEML.Float64

/-- An IEEE 754 double-precision float. Modelled by Lean's runtime
    `Float` type. -/
abbrev F64 := Float

/-- Embedding from `F64` into `ℝ` -- the real number a given f64
    value represents. Mathlib does not yet have a formal IEEE-754
    model, so this is declared `opaque` as a placeholder. Downstream
    theorems can still be stated abstractly via this embedding. -/
opaque F64.toReal : F64 → ℝ

/-- A "libm correctness postulate" relates an f64 implementation
    of a transcendental function to its real-valued specification
    via an absolute ulp bound on a stated domain.

    Example (intentional, not asserted here): for `mg_exp`, libm
    typically guarantees
        |F64.toReal (libm_exp v) - Real.exp (F64.toReal v)|
            ≤ 1.5 · ulp(Real.exp (F64.toReal v))
    on `v` representing values in `[-700, 700]`.

    Concrete `ULPBound` instances are left for future work.
    They are platform-dependent; introducing them as Lean axioms
    must be matched by validation against GNU libm's
    `libm-test-ulps` harness on the same target. -/
structure ULPBound where
  /-- Maximum permitted absolute error, expressed in ulps of the
      true (real-valued) result. -/
  ulps : ℝ
  /-- Domain on which the bound holds (as a predicate on the
      real-valued input). -/
  domain : ℝ → Prop

end MonogateEML.Float64
