import MachLib.AbsoluteBridge
import MachLib.AbsoluteFold
import MachLib.AbsoluteFoldLocal
import MachLib.EMLToCRuntime
import MachLib.HyperbolicLipschitz

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

/-! ### Grounding a transcendental: the `tanh`-saturated PID

Arithmetic grounds on `FPBridge` alone. A transcendental node adds one thing — the libm primitive's
rounding, the "irreducible trust" the T2/T3 work isolated. `tanh` is globally `1`-Lipschitz, so it
enters the fold with no domain hypothesis; and `tanh`-saturation is a real control primitive (a smooth
alternative to the hard `clamp`, and — unlike `clamp` — inside the certified `+/−/×/tr1` fragment). -/

/-- The disclosed libm rounding bound for the runtime `tanh`. `libmonogate.h` computes `tanh` by its
exp-decomposition (`stdI1 leanPrims .tanh`), so this is the standard model: that composite, through the
real denotation `realToR`, is within a fixed `real_tanh_eps` of the exact `Real.tanh`. Un-witnessable in
Lean (opaque `Float`), disclosed like `real_fpbridge`; the residual libm trust for this primitive. -/
axiom real_tanh_eps : MachLib.Real

axiom real_tanh_rounds : ∀ a : Float,
    abs (realToR (stdI1 leanPrims .tanh a) - tanh (realToR a)) ≤ real_tanh_eps

/-- **A grounded transcendental control kernel.** The emitted C for `tanh(1.5·e + 0.4·i + 0.05·d)` — a
soft-saturated PID — read through `realToR`, is within `real_tanh_eps + absErr` of the exact ℝ value
`tanh(PID law)`, with **no `FPBridge` and no ∀-primitive rounding hypothesis**: `FPBridge` is discharged
by `real_fpbridge`, the runtime correspondence by the proven `std_hrt` at Lean's libm basis, and the one
`tanh` rounding by the disclosed `real_tanh_rounds`. First grounded certificate reaching a transcendental
layer over real `Float` bytes. `1`-Lipschitz `tanh` (`globLip_lipschitz`) amplifies the arithmetic fold's
`absErr` by `1`. -/
theorem pid_tanh_grounded (env : Env) :
    AbsEnc (real_tanh_eps + 1 * absErr realToR env pidRawEML)
      (realToR (evalC (stdR1 leanPrims) (stdR2 leanPrims) env (emitC (tr1OfEML .tanh pidRawEML))).toF)
      (tanh (exactR realToR env pidRawEML)) :=
  pipeline_tr1_of_arith real_fpbridge (stdI1 leanPrims) (stdI2 leanPrims)
    (stdR1 leanPrims) (stdR2 leanPrims) (std_hrt1 leanPrims) (std_hrt2 leanPrims)
    env .tanh tanh 1 real_tanh_eps
    (le_of_lt zero_lt_one_ax) (fun p q => by rw [one_mul_thm]; exact tanh_lipschitz p q)
    pidRawEML isArith_pidRawEML (real_tanh_rounds _)

/-! ### Grounding a second libm primitive: `exp`, LOCALLY Lipschitz

`tanh` is globally `1`-Lipschitz, so `pid_tanh_grounded` needed no domain hypothesis. `exp` is not
globally Lipschitz (unbounded growth), so grounding it goes through `pipeline_exp_of_arith`
(`AbsoluteFoldLocal.lean`) instead: `L = exp hi` on any caller-supplied `[lo,hi]`, honestly conditional
on the PID law's value actually landing in that range — the expected, correct shape for a *local*
Lipschitz primitive, not a shortcoming relative to `tanh`'s unconditional result. -/

/-- The disclosed libm rounding bound for the runtime `exp`. Same status as `real_tanh_eps`: the
composite `libmonogate.h` computes for `exp` (here just `Float.exp` itself, `leanPrims.exp`), through
the real denotation `realToR`, is within a fixed `real_exp_eps` of the exact `Real.exp`. Un-witnessable
in Lean (opaque `Float`); the residual libm trust for this primitive. -/
axiom real_exp_eps : MachLib.Real

axiom real_exp_rounds : ∀ a : Float,
    abs (realToR (stdI1 leanPrims .exp a) - exp (realToR a)) ≤ real_exp_eps

/-- **A second grounded transcendental control kernel: `exp(PID law)`.** For any `[lo,hi]` the PID law's
computed AND exact values both land in, the emitted C for `exp(1.5·e + 0.4·i + 0.05·d)` — an
exponential-gain variant of the soft-saturated controller — read through `realToR`, is within
`real_exp_eps + exp hi · absErr` of the exact ℝ value `exp(PID law)`, with **no `FPBridge` and no
∀-primitive rounding hypothesis**: `FPBridge` is discharged by `real_fpbridge`, the runtime
correspondence by `std_hrt1`/`std_hrt2` at Lean's libm basis, and the one `exp` rounding by the
disclosed `real_exp_rounds`. Second grounded certificate reaching a transcendental layer over real
`Float` bytes — the second axis of what "libm primitive grounding" (the certcom-A scoping doc's item
5) actually means: not "grounding one universally-Lipschitz function suffices," but "each primitive
needs its own disclosed rounding constant AND, unless globally Lipschitz, its own domain hypothesis."
Instance of `pipeline_exp_of_arith` at `pidRawEML`. -/
theorem pid_exp_grounded (env : Env) (lo hi : MachLib.Real)
    (hflx_lo : lo ≤ realToR (evalEML (stdI1 leanPrims) (stdI2 leanPrims) env pidRawEML).toF)
    (hflx_hi : realToR (evalEML (stdI1 leanPrims) (stdI2 leanPrims) env pidRawEML).toF ≤ hi)
    (hxe_lo : lo ≤ exactR realToR env pidRawEML) (hxe_hi : exactR realToR env pidRawEML ≤ hi) :
    AbsEnc (real_exp_eps + exp hi * absErr realToR env pidRawEML)
      (realToR (evalC (stdR1 leanPrims) (stdR2 leanPrims) env (emitC (tr1OfEML .exp pidRawEML))).toF)
      (exp (exactR realToR env pidRawEML)) :=
  pipeline_exp_of_arith real_fpbridge (stdI1 leanPrims) (stdI2 leanPrims)
    (stdR1 leanPrims) (stdR2 leanPrims) (std_hrt1 leanPrims) (std_hrt2 leanPrims)
    env .exp lo hi real_exp_eps pidRawEML isArith_pidRawEML
    hflx_lo hflx_hi hxe_lo hxe_hi (real_exp_rounds _)

end Certcom
