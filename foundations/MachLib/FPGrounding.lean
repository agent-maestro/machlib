import MachLib.AbsoluteBridge
import MachLib.AbsoluteFold

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

/-- **The whole arithmetic fragment, grounded.** For *every* `IsArith` EML tree, the value the emitted
C computes — through the real denotation `realToR` — is within the folded absolute forward error
`absErr` of the exact ℝ value, with **no `FPBridge` hypothesis** (discharged by `real_fpbridge`). The
general lever: `pipeline_det_grounded` and `pid_grounded` are both instances. -/
theorem pipeline_arith_grounded (env : Env) (e : EML) (he : IsArith e) :
    AbsEnc (absErr realToR env e)
      (realToR (evalC (fun _ _ => 0) (fun _ _ _ => 0) env (emitC e)).toF)
      (exactR realToR env e) :=
  pipeline_arith real_fpbridge (fun _ _ => 0) (fun _ _ _ => 0) (fun _ _ => 0) (fun _ _ _ => 0)
    (fun _ _ => rfl) (fun _ _ _ => rfl) env e he

/-- The raw one-step PID law `Kp·e + Ki·i + Kd·d` (before the saturating `clamp`), with the shipped
`pid.eml` gains `Kp = 1.5`, `Ki = 0.4`, `Kd = 0.05` as literal constants and the three channels
`e`/`i`/`d` as inputs — left-associated exactly as `FixedPoint.pid_fx_fwd_error` writes it. This is the
arithmetic datapath of the dual-target controller that Forge compiles to the ESP32 (C) and Arty (RTL);
`clamp = min (max · lo) hi` is a separate saturating wrapper, outside the `+/−/×` fragment. -/
def pidRawEML : EML :=
  .bin .add
    (.bin .add (.bin .mul (.lit 1.5) (.var "e"))
               (.bin .mul (.lit 0.4) (.var "i")))
    (.bin .mul (.lit 0.05) (.var "d"))

/-- `pidRawEML` is in the arithmetic fragment. -/
theorem isArith_pidRawEML : IsArith pidRawEML :=
  .add _ _ (.add _ _ (.mul _ _ (.lit 1.5) (.var "e")) (.mul _ _ (.lit 0.4) (.var "i")))
    (.mul _ _ (.lit 0.05) (.var "d"))

/-- **Keystone on a silicon kernel.** The value the *emitted C* computes for the raw PID law
`1.5·e + 0.4·i + 0.05·d` — read through the real denotation `realToR` — is within `absErr` of the
exact ℝ PID law, with **no `FPBridge` hypothesis**. The same `pid.eml` datapath Forge ships to the
ESP32, now carrying an unconditional forward-error certificate on real `Float` bytes (modulo the one
disclosed IEEE-754 axiom `real_fpbridge`). Instance of `pipeline_arith_grounded` at `pidRawEML`. -/
theorem pid_grounded (env : Env) :
    AbsEnc (absErr realToR env pidRawEML)
      (realToR (evalC (fun _ _ => 0) (fun _ _ _ => 0) env (emitC pidRawEML)).toF)
      (exactR realToR env pidRawEML) :=
  pipeline_arith_grounded env pidRawEML isArith_pidRawEML

end Certcom
