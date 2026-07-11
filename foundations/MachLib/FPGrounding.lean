import MachLib.AbsoluteBridge

/-!
# certcom Theorem A — grounding the Float↔Real bridge (the disclosed IEEE-754 axiom)

The whole certcom-A forward-error tower is proved `∀ toR, FPBridge toR → …`. Inside Lean the *only*
inhabitant of `FPBridge` is the degenerate zero map (`FloatRealBridge`'s consistency witness): Lean's
`Float` is an opaque `@[extern]` native type, so the real denotation `Float → MachLib.Real` and the
standard model (every basic op correctly rounded, relative error ≤ unit roundoff `u`; negation exact)
**cannot be defined or proved inside Lean**. They *are* the IEEE-754 model.

This file takes that model as **one disclosed axiom** — the honest, terminal floor of the certcom-A
stack, the same trust status as `erf` (declared, structurally un-witnessable). With it, every proved
`∀ toR, FPBridge toR → P toR` certificate discharges to an **unconditional** statement about the
actual emitted-C computation, viewed through the real denotation. Grounding it *further* — deriving
`FPBridge realToR` rather than assuming it — is a Flocq-scale formalization of binary64 rounding,
outside Lean's `Float`.

The two axioms here are registered in `AxiomLedger` as disclosed-and-un-witnessable, so Theorem A's
footprint is auditable alongside the Khovanskii headlines: `pipeline_det_grounded` rests on exactly
`realToR`, `real_fpbridge`, the `MachLib.Real` axioms (witnessed against ℝ by Theorem B), and `u`.
-/

namespace Certcom

open MachLib.Real

/-- The value an IEEE-754 `Float` denotes as a `MachLib.Real`. Opaque: Lean's `Float` is a native
`@[extern]` type with no in-Lean real semantics, so the denotation is axiomatized, not defined. -/
axiom realToR : Float → MachLib.Real

/-- **The disclosed IEEE-754 model.** Under `realToR`, every basic float op is correctly rounded
(relative error ≤ `u`) and negation is exact — the standard model of floating-point arithmetic
(Higham, *Accuracy and Stability*, §2.2). Structurally un-witnessable in Lean (`Float` is opaque);
the terminal trust of certcom Theorem A, disclosed exactly like `erf`. -/
axiom real_fpbridge : FPBridge realToR

/-- **Keystone — an UNCONDITIONAL forward-error certificate on real `Float` bytes.**

The value the *emitted C* computes for the cancelling determinant `x·y − z·w` (`emitC detEML`, run by
`evalC`), read through the real denotation `realToR`, is within the absolute bound
`u·(2+u)·(|X·Y| + |Z·W|)` of the exact ℝ determinant `X·Y − Z·W` — with **no `FPBridge` hypothesis**:
the proved `pipeline_det` is discharged by `real_fpbridge`. Valid in the cancelling regime `X·Y ≈ Z·W`
(absolute bound, no sign or non-vanishing assumption). This is the first certcom-A certificate that
touches the actual artifact rather than an arbitrary `toR`.

`detEML` has no transcendental nodes, so the runtime/interpretation parameters are inert (the `hrt`
obligations close by `rfl`); the only trust beyond `MachLib.Real`'s (ℝ-witnessed) axioms is the one
disclosed IEEE-754 axiom `real_fpbridge`. -/
theorem pipeline_det_grounded (env : Env) :
    AbsEnc (u * (1 + 1 + u) * (abs (realToR (env "x").toF * realToR (env "y").toF)
                              + abs (realToR (env "z").toF * realToR (env "w").toF)))
      (realToR (evalC (fun _ _ => 0) (fun _ _ _ => 0) env (emitC detEML)).toF)
      (realToR (env "x").toF * realToR (env "y").toF
        - realToR (env "z").toF * realToR (env "w").toF) :=
  pipeline_det real_fpbridge (fun _ _ => 0) (fun _ _ _ => 0) (fun _ _ => 0) (fun _ _ _ => 0)
    (fun _ _ => rfl) (fun _ _ _ => rfl) env

end Certcom
