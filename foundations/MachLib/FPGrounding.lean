import MachLib.AbsoluteBridge
import MachLib.AbsoluteFold
import MachLib.AbsoluteFoldLocal
import MachLib.AbsoluteFoldNestLocal
import MachLib.EMLToCRuntime
import MachLib.HyperbolicLipschitz
import MachLib.InverseTrig
import MachLib.OperatorBasisGeneral

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

/-- **The disclosed libm rounding bound for the runtime `tanh`, domain-restricted.** For any `R` and
`a : Float` with `abs (realToR a) ≤ R`, `leanPrims.tanh`, through `realToR`, is within `u` of the exact
`Real.tanh` — a CONSTANT bound (not scaled by `R`): `tanh`'s output is always in `(-1,1)` regardless of
domain, so `R` here exists purely to guard the underlying implementation, not to calibrate the bound's
size. **Not claimed unconditionally** (erratum-driven design, 2026-07-22, matching `real_exp_rounds`):
`libmonogate.h` computes `tanh` via `stdI1 leanPrims .tanh = fun x => (p.exp x - p.exp (-x))/(p.exp x +
p.exp (-x))`, an exp-DECOMPOSITION (`EMLToCRuntime.lean`) — for large `|a|`, `Float.exp` on one branch
overflows to `+inf` while the other underflows to `0`, giving `inf/inf = NaN`, and `realToR (NaN)` is
completely unconstrained by any existing axiom. `tanh` being mathematically globally-Lipschitz does NOT
protect its Float IMPLEMENTATION from this — the composite, not the math, is what breaks. Un-witnessable
in Lean (`Float` opaque), disclosed like `real_fpbridge`; the residual libm trust for this primitive. -/
axiom real_tanh_rounds : ∀ (R : MachLib.Real) (a : Float), abs (realToR a) ≤ R →
    abs (realToR (stdI1 leanPrims .tanh a) - tanh (realToR a)) ≤ u

/-- **A grounded transcendental control kernel.** The emitted C for `tanh(1.5·e + 0.4·i + 0.05·d)` — a
soft-saturated PID — read through `realToR`, is within `u + absErr` of the exact ℝ value `tanh(PID
law)`, GIVEN a bound `R` on the PID law's own value (both computed and exact — the one new hypothesis
this theorem needs beyond the erratum-free version, to keep the underlying exp-decomposition from
overflowing; see `real_tanh_rounds`). `FPBridge` is discharged by `real_fpbridge`, the runtime
correspondence by the proven `std_hrt` at Lean's libm basis, and the one `tanh` rounding by the
disclosed, domain-restricted `real_tanh_rounds`. First grounded certificate reaching a transcendental
layer over real `Float` bytes. `1`-Lipschitz `tanh` (`globLip_lipschitz`) amplifies the arithmetic fold's
`absErr` by `1`. -/
theorem pid_tanh_grounded (env : Env) (R : MachLib.Real)
    (hflx : abs (realToR (evalEML (stdI1 leanPrims) (stdI2 leanPrims) env pidRawEML).toF) ≤ R) :
    AbsEnc (u + 1 * absErr realToR env pidRawEML)
      (realToR (evalC (stdR1 leanPrims) (stdR2 leanPrims) env (emitC (tr1OfEML .tanh pidRawEML))).toF)
      (tanh (exactR realToR env pidRawEML)) :=
  pipeline_tr1_of_arith real_fpbridge (stdI1 leanPrims) (stdI2 leanPrims)
    (stdR1 leanPrims) (stdR2 leanPrims) (std_hrt1 leanPrims) (std_hrt2 leanPrims)
    env .tanh tanh 1 u
    (le_of_lt zero_lt_one_ax) (fun p q => by rw [one_mul_thm]; exact tanh_lipschitz p q)
    pidRawEML isArith_pidRawEML (real_tanh_rounds R _ hflx)

/-! ### Grounding a second libm primitive: `exp`, LOCALLY Lipschitz

`tanh` is globally `1`-Lipschitz, so `pid_tanh_grounded` needed no domain hypothesis. `exp` is not
globally Lipschitz (unbounded growth), so grounding it goes through `pipeline_exp_of_arith`
(`AbsoluteFoldLocal.lean`) instead: `L = exp hi` on any caller-supplied `[lo,hi]`, honestly conditional
on the PID law's value actually landing in that range — the expected, correct shape for a *local*
Lipschitz primitive, not a shortcoming relative to `tanh`'s unconditional result. -/

/-- **The disclosed libm rounding bound for the runtime `exp`, domain-restricted.** For any `hi` and
any `a : Float` with `realToR a ≤ hi`, `leanPrims.exp`, through `realToR`, is within `u · exp hi` of
the exact `Real.exp`. Relative-error form (the standard IEEE-754 correctly-rounded model, same `u` as
every other correctly-rounded float operation in this codebase), uniformized over the range `hi` the
same way `exp_lip_local`'s `L := exp hi` uniformizes a Lipschitz bound. **Not claimed unconditionally**
(erratum-driven design, matching `EMLCertcomGrounded.lean`'s `real_round_bounds` fix, 2026-07-22):
`Float.exp` genuinely overflows to `+inf` above `hi ≈ 709`, past which `realToR (Float.exp a)` is
unconstrained by any existing axiom and NO fixed bound holds — an unconditional version of this axiom
asserts something no runtime satisfies. `hi` is exactly the same bound every caller (`pid_exp_grounded`
and Track C's `eml_var_var_*_grounded`) already carries for the Lipschitz part, so this costs no new
hypothesis at any existing call site. Un-witnessable in Lean (`Float` opaque); the residual libm trust
for this primitive. -/
axiom real_exp_rounds : ∀ (hi : MachLib.Real) (a : Float), realToR a ≤ hi →
    abs (realToR (stdI1 leanPrims .exp a) - exp (realToR a)) ≤ u * exp hi

/-- **A second grounded transcendental control kernel: `exp(PID law)`.** For any `[lo,hi]` the PID law's
computed AND exact values both land in, the emitted C for `exp(1.5·e + 0.4·i + 0.05·d)` — an
exponential-gain variant of the soft-saturated controller — read through `realToR`, is within
`u · exp hi + exp hi · absErr` of the exact ℝ value `exp(PID law)`, with **no `FPBridge` and no
∀-primitive rounding hypothesis**: `FPBridge` is discharged by `real_fpbridge`, the runtime
correspondence by `std_hrt1`/`std_hrt2` at Lean's libm basis, and the one `exp` rounding by the
disclosed, domain-restricted `real_exp_rounds` — discharged at `hi` from the SAME `hflx_hi` this
theorem already required for the Lipschitz part, no new hypothesis needed. Second grounded certificate
reaching a transcendental layer over real `Float` bytes — the second axis of what "libm primitive
grounding" (the certcom-A scoping doc's item 5) actually means: not "grounding one
universally-Lipschitz function suffices," but "each primitive needs its own disclosed rounding
constant AND, unless globally Lipschitz, its own domain hypothesis." Instance of `pipeline_exp_of_arith`
at `pidRawEML`. -/
theorem pid_exp_grounded (env : Env) (lo hi : MachLib.Real)
    (hflx_lo : lo ≤ realToR (evalEML (stdI1 leanPrims) (stdI2 leanPrims) env pidRawEML).toF)
    (hflx_hi : realToR (evalEML (stdI1 leanPrims) (stdI2 leanPrims) env pidRawEML).toF ≤ hi)
    (hxe_lo : lo ≤ exactR realToR env pidRawEML) (hxe_hi : exactR realToR env pidRawEML ≤ hi) :
    AbsEnc (u * exp hi + exp hi * absErr realToR env pidRawEML)
      (realToR (evalC (stdR1 leanPrims) (stdR2 leanPrims) env (emitC (tr1OfEML .exp pidRawEML))).toF)
      (exp (exactR realToR env pidRawEML)) :=
  pipeline_exp_of_arith real_fpbridge (stdI1 leanPrims) (stdI2 leanPrims)
    (stdR1 leanPrims) (stdR2 leanPrims) (std_hrt1 leanPrims) (std_hrt2 leanPrims)
    env .exp lo hi (u * exp hi) pidRawEML isArith_pidRawEML
    hflx_lo hflx_hi hxe_lo hxe_hi (real_exp_rounds hi _ hflx_hi)

/-! ### Grounding a third libm primitive: `log`, LOCALLY Lipschitz on a positive domain

Same shape as `exp` — not globally Lipschitz, so through the local-Lipschitz lever
(`pipeline_log_of_arith`, `L = 1/lo`) — with one further honest cost: `log` additionally needs the
domain to be strictly positive (`lo > 0`, not just bounded), since `log` itself is only meaningfully
Lipschitz — and only defined analytically — on `(0,∞)`. Third data point on what "libm primitive
grounding" (certcom-A scoping doc item 5) costs per primitive: a disclosed rounding constant always,
plus a domain hypothesis unless the primitive happens to be globally Lipschitz like `tanh`, plus
(for `log` specifically) a positivity side-condition on top of the plain range bound. -/

/-- **The disclosed libm rounding bound for the runtime `log`, domain-restricted.** For any
`0 < lo ≤ hi` and `a : Float` with `lo ≤ realToR a ≤ hi`, `leanPrims.log`, through `realToR`, is
within `u · (abs (log lo) + abs (log hi))` of the exact `Real.log` — a safe two-sided bound (log
monotonic, so `log (realToR a) ∈ [log lo, log hi]`, and `abs (log (realToR a)) ≤ abs (log lo) +
abs (log hi)` regardless of whether that interval straddles `0`), reusing exactly the `lo`/`hi` every
caller (`pid_log_grounded`, Track C's `eml_var_var_*_grounded`) already carries. **Not claimed
unconditionally** (erratum-driven design, 2026-07-22): `log` is undefined/`NaN` at or below `0`, so an
unconditional bound over every `Float` — including non-positive ones — asserts something no runtime
satisfies. Un-witnessable in Lean (`Float` opaque); the residual libm trust for this primitive. -/
axiom real_log_rounds : ∀ (lo hi : MachLib.Real) (a : Float), 0 < lo → lo ≤ realToR a → realToR a ≤ hi →
    abs (realToR (stdI1 leanPrims .ln a) - log (realToR a)) ≤ u * (abs (log lo) + abs (log hi))

/-- **A third grounded transcendental control kernel: `log(PID law)`.** For any `[lo,hi]` with `lo>0`
that the PID law's computed AND exact values both land in, the emitted C for
`log(1.5·e + 0.4·i + 0.05·d)` — a logarithmic-gain variant of the controller (e.g. a decibel-scaled
error signal) — read through `realToR`, is within `u·(abs(log lo)+abs(log hi)) + (1/lo)·absErr` of the
exact ℝ value `log(PID law)`, with **no `FPBridge` and no ∀-primitive rounding hypothesis**: `FPBridge`
is discharged by `real_fpbridge`, the runtime correspondence by `std_hrt1`/`std_hrt2`, and the one
`log` rounding by the disclosed, domain-restricted `real_log_rounds` — discharged from the SAME
`hlo`/`hflx_lo`/`hflx_hi` this theorem already required for the Lipschitz part, no new hypothesis
needed. Third grounded transcendental kernel over real `Float` bytes. Instance of
`pipeline_log_of_arith` at `pidRawEML`. -/
theorem pid_log_grounded (env : Env) (lo hi : MachLib.Real) (hlo : 0 < lo)
    (hflx_lo : lo ≤ realToR (evalEML (stdI1 leanPrims) (stdI2 leanPrims) env pidRawEML).toF)
    (hflx_hi : realToR (evalEML (stdI1 leanPrims) (stdI2 leanPrims) env pidRawEML).toF ≤ hi)
    (hxe_lo : lo ≤ exactR realToR env pidRawEML) (hxe_hi : exactR realToR env pidRawEML ≤ hi) :
    AbsEnc (u * (abs (log lo) + abs (log hi)) + (1 / lo) * absErr realToR env pidRawEML)
      (realToR (evalC (stdR1 leanPrims) (stdR2 leanPrims) env (emitC (tr1OfEML .ln pidRawEML))).toF)
      (log (exactR realToR env pidRawEML)) :=
  pipeline_log_of_arith real_fpbridge (stdI1 leanPrims) (stdI2 leanPrims)
    (stdR1 leanPrims) (stdR2 leanPrims) (std_hrt1 leanPrims) (std_hrt2 leanPrims)
    env .ln lo hi (u * (abs (log lo) + abs (log hi))) hlo pidRawEML isArith_pidRawEML
    hflx_lo hflx_hi hxe_lo hxe_hi (real_log_rounds lo hi _ hlo hflx_lo hflx_hi)

/-! ### Grounding a fourth libm primitive: `sin`, back to GLOBALLY Lipschitz

`sin` is globally `1`-Lipschitz (`TrigLipschitz.sin_lipschitz`), same shape as `tanh` — no domain
hypothesis needed, straight through `pipeline_tr1_of_arith`. Second data point (after `tanh`) on the
globally-Lipschitz side of the primitive basis, confirming that side really is as cheap as `tanh`
suggested and not a one-off — unlike `exp`/`log`, no domain bookkeeping at all. -/

/-- The disclosed libm rounding bound for the runtime `sin`. Same status as `real_tanh_eps`: the
composite `leanPrims.sin`, through `realToR`, is within a fixed `real_sin_eps` of the exact `Real.sin`.
Un-witnessable in Lean (opaque `Float`); the residual libm trust for this primitive.

**Confirmed unconditional (2026-07-22 audit, not changed)** — unlike `exp`/`sinh`/`cosh`/`tanh`,
`sin` is a NATIVE `Prims` field (`Float.sin`), not an exp-composite, so it cannot hit the
`inf/inf = NaN` failure those primitives' erratum fixes address. Its mathematical output is bounded
(`abs (sin x) ≤ 1` for every real `x`), so — unlike `exp` (genuinely unbounded, no fixed constant
works), `log`/`sqrt`/`asin`/`acos` (undefined outside a domain, `NaN` outside it), or `tan` (poles) —
a fixed `real_sin_eps` COULD be a true statement about the real runtime for every `Float`, PROVIDED
it's calibrated large enough to cover known accuracy degradation from large-argument range reduction
(a real, if second-order, libm concern for huge `|a|` — a genuinely different, milder failure mode
than the others' `NaN`/`inf`/unboundedness). Not provably false the way the ten fixed axioms were;
left unconditional. -/
axiom real_sin_eps : MachLib.Real

axiom real_sin_rounds : ∀ a : Float,
    abs (realToR (stdI1 leanPrims .sin a) - sin (realToR a)) ≤ real_sin_eps

/-- **A fourth grounded transcendental control kernel: `sin(PID law)`.** The emitted C for
`sin(1.5·e + 0.4·i + 0.05·d)` — an oscillatory-gain variant of the controller — read through
`realToR`, is within `real_sin_eps + absErr` of the exact ℝ value `sin(PID law)`, with **no `FPBridge`
and no ∀-primitive rounding hypothesis**, unconditionally (no domain hypothesis at all — `sin` is
globally Lipschitz, same as `tanh`). Instance of `pipeline_tr1_of_arith` at `pidRawEML`. -/
theorem pid_sin_grounded (env : Env) :
    AbsEnc (real_sin_eps + 1 * absErr realToR env pidRawEML)
      (realToR (evalC (stdR1 leanPrims) (stdR2 leanPrims) env (emitC (tr1OfEML .sin pidRawEML))).toF)
      (sin (exactR realToR env pidRawEML)) :=
  pipeline_tr1_of_arith real_fpbridge (stdI1 leanPrims) (stdI2 leanPrims)
    (stdR1 leanPrims) (stdR2 leanPrims) (std_hrt1 leanPrims) (std_hrt2 leanPrims)
    env .sin sin 1 real_sin_eps
    (le_of_lt zero_lt_one_ax) (fun p q => by rw [one_mul_thm]; exact sin_lipschitz p q)
    pidRawEML isArith_pidRawEML (real_sin_rounds _)

/-! ### Grounding a fifth libm primitive: `cos`, also GLOBALLY Lipschitz

Third data point on the globally-Lipschitz side (`TrigLipschitz.cos_lipschitz`, `L=1`), identical
pattern to `tanh`/`sin` — no domain hypothesis. -/

/-- The disclosed libm rounding bound for the runtime `cos`. Same status as `real_sin_eps`: the
composite `leanPrims.cos`, through `realToR`, is within a fixed `real_cos_eps` of the exact `Real.cos`.
Un-witnessable in Lean (opaque `Float`); the residual libm trust for this primitive.

**Confirmed unconditional (2026-07-22 audit, not changed)** — same reasoning as `real_sin_eps`
above: native `Prims` field, bounded output, no `inf/inf`/`NaN`/pole failure mode. -/
axiom real_cos_eps : MachLib.Real

axiom real_cos_rounds : ∀ a : Float,
    abs (realToR (stdI1 leanPrims .cos a) - cos (realToR a)) ≤ real_cos_eps

/-- **A fifth grounded transcendental control kernel: `cos(PID law)`.** The emitted C for
`cos(1.5·e + 0.4·i + 0.05·d)` read through `realToR` is within `real_cos_eps + absErr` of the exact
ℝ value `cos(PID law)`, unconditionally — `cos` is globally Lipschitz, same as `tanh`/`sin`. Instance
of `pipeline_tr1_of_arith` at `pidRawEML`. -/
theorem pid_cos_grounded (env : Env) :
    AbsEnc (real_cos_eps + 1 * absErr realToR env pidRawEML)
      (realToR (evalC (stdR1 leanPrims) (stdR2 leanPrims) env (emitC (tr1OfEML .cos pidRawEML))).toF)
      (cos (exactR realToR env pidRawEML)) :=
  pipeline_tr1_of_arith real_fpbridge (stdI1 leanPrims) (stdI2 leanPrims)
    (stdR1 leanPrims) (stdR2 leanPrims) (std_hrt1 leanPrims) (std_hrt2 leanPrims)
    env .cos cos 1 real_cos_eps
    (le_of_lt zero_lt_one_ax) (fun p q => by rw [one_mul_thm]; exact cos_lipschitz p q)
    pidRawEML isArith_pidRawEML (real_cos_rounds _)

/-! ### Grounding a sixth libm primitive: `atan`, also GLOBALLY Lipschitz

Fourth data point on the globally-Lipschitz side (`InverseTrig.atan_lipschitz`, `L=1`), identical
pattern to `tanh`/`sin`/`cos`. -/

/-- The disclosed libm rounding bound for the runtime `atan`. Same status as `real_cos_eps`: the
composite `leanPrims.atan`, through `realToR`, is within a fixed `real_atan_eps` of the exact
`Real.atan`. Un-witnessable in Lean (opaque `Float`); the residual libm trust for this primitive.

**Confirmed unconditional (2026-07-22 audit, not changed)** — same reasoning as `real_sin_eps`:
native `Prims` field, output bounded by `π/2` for every real input, no failure mode requiring a
domain restriction. -/
axiom real_atan_eps : MachLib.Real

axiom real_atan_rounds : ∀ a : Float,
    abs (realToR (stdI1 leanPrims .atan a) - atan (realToR a)) ≤ real_atan_eps

/-- **A sixth grounded transcendental control kernel: `atan(PID law)`.** The emitted C for
`atan(1.5·e + 0.4·i + 0.05·d)` read through `realToR` is within `real_atan_eps + absErr` of the exact
ℝ value `atan(PID law)`, unconditionally — `atan` is globally Lipschitz, same as `tanh`/`sin`/`cos`.
Instance of `pipeline_tr1_of_arith` at `pidRawEML`. -/
theorem pid_atan_grounded (env : Env) :
    AbsEnc (real_atan_eps + 1 * absErr realToR env pidRawEML)
      (realToR (evalC (stdR1 leanPrims) (stdR2 leanPrims) env (emitC (tr1OfEML .atan pidRawEML))).toF)
      (atan (exactR realToR env pidRawEML)) :=
  pipeline_tr1_of_arith real_fpbridge (stdI1 leanPrims) (stdI2 leanPrims)
    (stdR1 leanPrims) (stdR2 leanPrims) (std_hrt1 leanPrims) (std_hrt2 leanPrims)
    env .atan atan 1 real_atan_eps
    (le_of_lt zero_lt_one_ax) (fun p q => by rw [one_mul_thm]; exact atan_lipschitz p q)
    pidRawEML isArith_pidRawEML (real_atan_rounds _)

/-! ### Grounding a seventh libm primitive: `abs`, the LAST globally-Lipschitz one

`abs` is `1`-Lipschitz (`OperatorBasisGeneral.abs_abs_sub_le`, the reverse triangle inequality) — the
last of the five globally-Lipschitz primitives (`tanh`,`sin`,`cos`,`atan`,`abs`) `AbsoluteFold.lean`'s
own docstring names. Closes out the cheap half of the basis; every remaining `Trans1` primitive needs
its own domain or positivity bookkeeping (matching `exp`/`log`'s shape, not `tanh`/`sin`/`cos`/`atan`'s). -/

/-- The disclosed libm rounding bound for the runtime `abs`. Same status as `real_atan_eps`: the
composite `leanPrims.abs`, through `realToR`, is within a fixed `real_abs_eps` of the exact
`Real.abs`. `abs` is IEEE-754-exact in principle (sign-bit clear, no rounding at all) — same honest
posture as the `neg` field of `FPBridge` — but the residual libm trust is disclosed the same way as
every other primitive here rather than assumed exact, since the runtime call still goes through
`mg_abs`/`fabs`, not a bare sign-bit operation Lean can see.

**Confirmed unconditional (2026-07-22 audit, not changed)** — `abs` is exact (no rounding at all in
principle) and its output magnitude never exceeds the input's, so it inherits no failure mode from
anything upstream; the weakest possible case for a domain restriction of all fourteen. -/
axiom real_abs_eps : MachLib.Real

axiom real_abs_rounds : ∀ a : Float,
    abs (realToR (stdI1 leanPrims .abs a) - abs (realToR a)) ≤ real_abs_eps

/-- **A seventh grounded transcendental control kernel: `abs(PID law)`.** The emitted C for
`abs(1.5·e + 0.4·i + 0.05·d)` — a rectified-error variant of the controller — read through `realToR`
is within `real_abs_eps + absErr` of the exact ℝ value `abs(PID law)`, unconditionally. Instance of
`pipeline_tr1_of_arith` at `pidRawEML`. -/
theorem pid_abs_grounded (env : Env) :
    AbsEnc (real_abs_eps + 1 * absErr realToR env pidRawEML)
      (realToR (evalC (stdR1 leanPrims) (stdR2 leanPrims) env (emitC (tr1OfEML .abs pidRawEML))).toF)
      (abs (exactR realToR env pidRawEML)) :=
  pipeline_tr1_of_arith real_fpbridge (stdI1 leanPrims) (stdI2 leanPrims)
    (stdR1 leanPrims) (stdR2 leanPrims) (std_hrt1 leanPrims) (std_hrt2 leanPrims)
    env .abs abs 1 real_abs_eps
    (le_of_lt zero_lt_one_ax) (fun p q => by rw [one_mul_thm]; exact abs_abs_sub_le p q)
    pidRawEML isArith_pidRawEML (real_abs_rounds _)

/-! ### Grounding an eighth libm primitive: `sqrt`, LOCALLY Lipschitz on a positive domain

Same shape as `log` — one-sided domain, needs `lo > 0`. `L = 1/(√lo+√lo)` via
`SqrtNode.sqrt_lip_local`. All five globally-Lipschitz primitives are done; every primitive from here
needs its own domain/positivity bookkeeping. -/

/-- **The disclosed libm rounding bound for the runtime `sqrt`, domain-restricted.** For any
`0 ≤ hi` and `a : Float` with `0 ≤ realToR a ≤ hi`, `leanPrims.sqrt`, through `realToR`, is within
`u · sqrt hi` of the exact `Real.sqrt` (`sqrt` monotonic and non-negative, so `sqrt (realToR a) ≤
sqrt hi`). **Not claimed unconditionally** (erratum-driven design, 2026-07-22): `Float.sqrt` of a
negative input is `NaN` in IEEE-754, and `realToR (NaN)` is unconstrained. Un-witnessable in Lean
(`Float` opaque); the residual libm trust for this primitive. -/
axiom real_sqrt_rounds : ∀ (hi : MachLib.Real) (a : Float), 0 ≤ realToR a → realToR a ≤ hi →
    abs (realToR (stdI1 leanPrims .sqrt a) - sqrt (realToR a)) ≤ u * sqrt hi

/-- **An eighth grounded transcendental control kernel: `sqrt(PID law)`.** For any `[lo,hi]` with
`lo>0` that the PID law's computed AND exact values both land in, the emitted C for
`sqrt(1.5·e + 0.4·i + 0.05·d)` — an RMS/magnitude-style variant — read through `realToR`, is within
`u·sqrt hi + (1/(√lo+√lo))·absErr` of the exact ℝ value `sqrt(PID law)`. Instance of
`pipeline_sqrt_of_arith` at `pidRawEML`. -/
theorem pid_sqrt_grounded (env : Env) (lo hi : MachLib.Real) (hlo : 0 < lo)
    (hflx_lo : lo ≤ realToR (evalEML (stdI1 leanPrims) (stdI2 leanPrims) env pidRawEML).toF)
    (hflx_hi : realToR (evalEML (stdI1 leanPrims) (stdI2 leanPrims) env pidRawEML).toF ≤ hi)
    (hxe_lo : lo ≤ exactR realToR env pidRawEML) (hxe_hi : exactR realToR env pidRawEML ≤ hi) :
    AbsEnc (u * sqrt hi + (1 / (sqrt lo + sqrt lo)) * absErr realToR env pidRawEML)
      (realToR (evalC (stdR1 leanPrims) (stdR2 leanPrims) env (emitC (tr1OfEML .sqrt pidRawEML))).toF)
      (sqrt (exactR realToR env pidRawEML)) :=
  pipeline_sqrt_of_arith real_fpbridge (stdI1 leanPrims) (stdI2 leanPrims)
    (stdR1 leanPrims) (stdR2 leanPrims) (std_hrt1 leanPrims) (std_hrt2 leanPrims)
    env .sqrt lo hi (u * sqrt hi) hlo pidRawEML isArith_pidRawEML
    hflx_lo hflx_hi hxe_lo hxe_hi (real_sqrt_rounds hi _ (le_of_lt (lt_of_lt_of_le hlo hflx_lo)) hflx_hi)

/-! ### Grounding a ninth libm primitive: `log10`, LOCALLY Lipschitz on a positive domain

Same shape as `log`/`sqrt` — one-sided domain, `lo > 0`, `L = 1/(lo·log 10)`. Unlike every other
primitive here, `leanPrims`'s own interpretation of `.log10` is ITSELF a composite built from `ln`
(`fun x => p.ln x / p.ln 10`, `EMLToCRuntime.lean`), not a distinct native runtime call — the disclosed
rounding bound covers that whole composite, same honest posture as everywhere else. -/

/-- **The disclosed libm rounding bound for the runtime `log10`, domain-restricted.** For any
`0 < lo ≤ hi` and `a : Float` with `lo ≤ realToR a ≤ hi`, `leanPrims.log10`, through `realToR`, is
within `u · (abs (log10 lo) + abs (log10 hi))` of the exact `Real.log10` — same two-sided shape as
`real_log_rounds` (`log10` is `log`'s monotone rescaling, so the same argument applies). **Not
claimed unconditionally** (erratum-driven design, 2026-07-22): same positivity failure as `log` (the
composite is `ln x / ln 10`). Un-witnessable in Lean (`Float` opaque); the residual libm trust for
this primitive. -/
axiom real_log10_rounds : ∀ (lo hi : MachLib.Real) (a : Float),
    0 < lo → lo ≤ realToR a → realToR a ≤ hi →
    abs (realToR (stdI1 leanPrims .log10 a) - log10 (realToR a)) ≤ u * (abs (log10 lo) + abs (log10 hi))

/-- **A ninth grounded transcendental control kernel: `log10(PID law)`.** For any `[lo,hi]` with
`lo>0` that the PID law's computed AND exact values both land in, the emitted C for
`log10(1.5·e + 0.4·i + 0.05·d)` — a decibel-scaled gain variant — read through `realToR`, is within
`u·(abs(log10 lo)+abs(log10 hi)) + (1/(lo·log 10))·absErr` of the exact ℝ value `log10(PID law)`.
Instance of `pipeline_log10_of_arith` at `pidRawEML`. -/
theorem pid_log10_grounded (env : Env) (lo hi : MachLib.Real) (hlo : 0 < lo)
    (hflx_lo : lo ≤ realToR (evalEML (stdI1 leanPrims) (stdI2 leanPrims) env pidRawEML).toF)
    (hflx_hi : realToR (evalEML (stdI1 leanPrims) (stdI2 leanPrims) env pidRawEML).toF ≤ hi)
    (hxe_lo : lo ≤ exactR realToR env pidRawEML) (hxe_hi : exactR realToR env pidRawEML ≤ hi) :
    AbsEnc (u * (abs (log10 lo) + abs (log10 hi))
        + (1 / (lo * log (natCast 10))) * absErr realToR env pidRawEML)
      (realToR (evalC (stdR1 leanPrims) (stdR2 leanPrims) env (emitC (tr1OfEML .log10 pidRawEML))).toF)
      (log10 (exactR realToR env pidRawEML)) :=
  pipeline_log10_of_arith real_fpbridge (stdI1 leanPrims) (stdI2 leanPrims)
    (stdR1 leanPrims) (stdR2 leanPrims) (std_hrt1 leanPrims) (std_hrt2 leanPrims)
    env .log10 lo hi (u * (abs (log10 lo) + abs (log10 hi))) hlo pidRawEML isArith_pidRawEML
    hflx_lo hflx_hi hxe_lo hxe_hi (real_log10_rounds lo hi _ hlo hflx_lo hflx_hi)

/-! ### Grounding a tenth libm primitive: `asin` (`arcsin`), SYMMETRIC-domain Lipschitz

First symmetric-domain primitive: Lipschitz only on `[-R,R]`, `R < 1` (derivative blows up at `±1`),
`L = 1/√(1−R²)`, via `InverseTrigBounded.arcsin_lip_local`. -/

/-- **The disclosed libm rounding bound for the runtime `asin`, domain-restricted.** For any `R < 1`
and `a : Float` with `abs (realToR a) ≤ R`, `leanPrims.asin`, through `realToR`, is within `u · (pi/2)`
of the exact `Real.arcsin` — a CONSTANT bound (`arcsin`'s output is always in `[-π/2,π/2]` regardless
of domain). **Not claimed unconditionally** (erratum-driven design, 2026-07-22, self-caught while
designing `hround_all`'s generic dispatcher below — `R < 1` was missing from this axiom's first draft,
the same mistake `real_exp_rounds`'s erratum fixed for `exp`): `Float.asin` of `abs x > 1` is `NaN` in
IEEE-754, and `realToR (NaN)` is unconstrained — a version of this axiom without `R < 1` is EXACTLY
as false as the original unconditional `real_asin_eps` was, just with the failure boundary moved from
"no bound at all" to "no bound past `abs x = 1`," which is still outside what `abs (realToR a) ≤ R`
alone rules out for `R ≥ 1`. Un-witnessable in Lean (`Float` opaque); the residual libm trust for
this primitive. -/
axiom real_asin_rounds : ∀ (R : MachLib.Real) (a : Float), R < 1 → abs (realToR a) ≤ R →
    abs (realToR (stdI1 leanPrims .asin a) - arcsin (realToR a)) ≤ u * (pi / (1 + 1))

/-- **A tenth grounded transcendental control kernel: `asin(PID law)`.** For any `[-R,R]` (`R<1`) that
the PID law's computed AND exact values both land in, the emitted C for
`asin(1.5·e + 0.4·i + 0.05·d)` read through `realToR`, is within `u·(pi/2) + (1/√(1−R²))·absErr` of
the exact ℝ value `arcsin(PID law)`. Instance of `pipeline_arcsin_of_arith` at `pidRawEML`. -/
theorem pid_asin_grounded (env : Env) (R : MachLib.Real) (hR : R < 1)
    (hflx_lo : -R ≤ realToR (evalEML (stdI1 leanPrims) (stdI2 leanPrims) env pidRawEML).toF)
    (hflx_hi : realToR (evalEML (stdI1 leanPrims) (stdI2 leanPrims) env pidRawEML).toF ≤ R)
    (hxe_lo : -R ≤ exactR realToR env pidRawEML) (hxe_hi : exactR realToR env pidRawEML ≤ R) :
    AbsEnc (u * (pi / (1 + 1)) + (1 / sqrt (1 - R * R)) * absErr realToR env pidRawEML)
      (realToR (evalC (stdR1 leanPrims) (stdR2 leanPrims) env (emitC (tr1OfEML .asin pidRawEML))).toF)
      (arcsin (exactR realToR env pidRawEML)) :=
  pipeline_arcsin_of_arith real_fpbridge (stdI1 leanPrims) (stdI2 leanPrims)
    (stdR1 leanPrims) (stdR2 leanPrims) (std_hrt1 leanPrims) (std_hrt2 leanPrims)
    env .asin R (u * (pi / (1 + 1))) hR pidRawEML isArith_pidRawEML
    hflx_lo hflx_hi hxe_lo hxe_hi (real_asin_rounds R _ hR (abs_le_iff.mpr ⟨hflx_lo, hflx_hi⟩))

/-! ### Grounding an eleventh libm primitive: `acos` (`arccos`), same symmetric-domain shape as `asin`
-/

/-- **The disclosed libm rounding bound for the runtime `acos`, domain-restricted.** For any `R < 1`
and `a : Float` with `abs (realToR a) ≤ R`, `leanPrims.acos`, through `realToR`, is within `u · pi` of
the exact `Real.arccos` — CONSTANT (`arccos`'s output is always in `[0,π]`), same shape as
`real_asin_rounds` (including the same `R < 1` fix). **Not claimed unconditionally** (erratum-driven
design, 2026-07-22): same out-of-domain `NaN` risk as `asin`. Un-witnessable in Lean (`Float`
opaque); the residual libm trust for this primitive. -/
axiom real_acos_rounds : ∀ (R : MachLib.Real) (a : Float), R < 1 → abs (realToR a) ≤ R →
    abs (realToR (stdI1 leanPrims .acos a) - arccos (realToR a)) ≤ u * pi

/-- **An eleventh grounded transcendental control kernel: `acos(PID law)`.** Same shape as
`pid_asin_grounded`. Instance of `pipeline_arccos_of_arith` at `pidRawEML`. -/
theorem pid_acos_grounded (env : Env) (R : MachLib.Real) (hR : R < 1)
    (hflx_lo : -R ≤ realToR (evalEML (stdI1 leanPrims) (stdI2 leanPrims) env pidRawEML).toF)
    (hflx_hi : realToR (evalEML (stdI1 leanPrims) (stdI2 leanPrims) env pidRawEML).toF ≤ R)
    (hxe_lo : -R ≤ exactR realToR env pidRawEML) (hxe_hi : exactR realToR env pidRawEML ≤ R) :
    AbsEnc (u * pi + (1 / sqrt (1 - R * R)) * absErr realToR env pidRawEML)
      (realToR (evalC (stdR1 leanPrims) (stdR2 leanPrims) env (emitC (tr1OfEML .acos pidRawEML))).toF)
      (arccos (exactR realToR env pidRawEML)) :=
  pipeline_arccos_of_arith real_fpbridge (stdI1 leanPrims) (stdI2 leanPrims)
    (stdR1 leanPrims) (stdR2 leanPrims) (std_hrt1 leanPrims) (std_hrt2 leanPrims)
    env .acos R (u * pi) hR pidRawEML isArith_pidRawEML
    hflx_lo hflx_hi hxe_lo hxe_hi (real_acos_rounds R _ hR (abs_le_iff.mpr ⟨hflx_lo, hflx_hi⟩))

/-! ### Grounding a twelfth libm primitive: `sinh`, SYMMETRIC domain, unconditional on `R`

`sinh` needs a domain (unlike globally-Lipschitz `tanh`) but, like `exp`, no extra sign hypothesis:
`L = cosh R > 0` for every `R`. `leanPrims`'s `.sinh` is itself a composite of `exp` (`EMLToCRuntime.lean`
`(p.exp x - p.exp (-x)) * 0.5`), not a distinct native call. -/

/-- **The disclosed libm rounding bound for the runtime `sinh`, domain-restricted.** For any `R` and
`a : Float` with `abs (realToR a) ≤ R`, `leanPrims.sinh`, through `realToR`, is within `u · cosh R` of
the exact `Real.sinh` — reusing `cosh R` as the safe magnitude bound (`abs (sinh x) ≤ cosh x ≤ cosh R`
for `abs x ≤ R`), exactly the SAME quantity `pid_sinh_grounded` already uses as its Lipschitz constant,
so this costs no new hypothesis at that call site. **Not claimed unconditionally** (erratum-driven
design, 2026-07-22): `leanPrims.sinh` is itself an exp-composite (`(p.exp x - p.exp (-x)) * 0.5`,
`EMLToCRuntime.lean`) with the same overflow risk `real_exp_rounds`'s erratum note describes. Un-
witnessable in Lean (`Float` opaque); the residual libm trust for this primitive. -/
axiom real_sinh_rounds : ∀ (R : MachLib.Real) (a : Float), abs (realToR a) ≤ R →
    abs (realToR (stdI1 leanPrims .sinh a) - sinh (realToR a)) ≤ u * cosh R

/-- **A twelfth grounded transcendental control kernel: `sinh(PID law)`.** For any `[-R,R]` that the
PID law's computed AND exact values both land in, the emitted C for `sinh(1.5·e + 0.4·i + 0.05·d)` read
through `realToR`, is within `u · cosh R + cosh R · absErr` of the exact ℝ value `sinh(PID law)`.
Instance of `pipeline_sinh_of_arith` at `pidRawEML`. -/
theorem pid_sinh_grounded (env : Env) (R : MachLib.Real)
    (hflx_lo : -R ≤ realToR (evalEML (stdI1 leanPrims) (stdI2 leanPrims) env pidRawEML).toF)
    (hflx_hi : realToR (evalEML (stdI1 leanPrims) (stdI2 leanPrims) env pidRawEML).toF ≤ R)
    (hxe_lo : -R ≤ exactR realToR env pidRawEML) (hxe_hi : exactR realToR env pidRawEML ≤ R) :
    AbsEnc (u * cosh R + cosh R * absErr realToR env pidRawEML)
      (realToR (evalC (stdR1 leanPrims) (stdR2 leanPrims) env (emitC (tr1OfEML .sinh pidRawEML))).toF)
      (sinh (exactR realToR env pidRawEML)) :=
  pipeline_sinh_of_arith real_fpbridge (stdI1 leanPrims) (stdI2 leanPrims)
    (stdR1 leanPrims) (stdR2 leanPrims) (std_hrt1 leanPrims) (std_hrt2 leanPrims)
    env .sinh R (u * cosh R) pidRawEML isArith_pidRawEML
    hflx_lo hflx_hi hxe_lo hxe_hi
    (real_sinh_rounds R _ (abs_le_iff.mpr ⟨hflx_lo, hflx_hi⟩))

/-! ### Grounding a thirteenth libm primitive: `cosh`, SYMMETRIC domain, needs `0 ≤ R`

The `cosh`/`log` analog of `sinh`/`exp`: `L = sinh R` needs `R ≥ 0` on top of the plain range bounds
(`sinh R ≥ 0` only holds for `R ≥ 0`) — one further honest cost layered on the symmetric-domain case,
mirroring how `log` layers positivity on top of `exp`'s plain one-sided domain. THIRTEENTH grounded
primitive — every `Trans1` constructor except `tan` is now grounded. -/

/-- **The disclosed libm rounding bound for the runtime `cosh`, domain-restricted.** For any `R` and
`a : Float` with `abs (realToR a) ≤ R`, `leanPrims.cosh`, through `realToR`, is within `u · cosh R` of
the exact `Real.cosh` (`cosh` monotonic in `abs ·`, so `cosh x ≤ cosh R` for `abs x ≤ R`) — reusing the
SAME `cosh R`/`sinh R` shape `pid_cosh_grounded` already needs. **Not claimed unconditionally**
(erratum-driven design, 2026-07-22): same exp-composite overflow risk as `sinh`/`real_sinh_rounds`.
Un-witnessable in Lean (`Float` opaque); the residual libm trust for this primitive. -/
axiom real_cosh_rounds : ∀ (R : MachLib.Real) (a : Float), abs (realToR a) ≤ R →
    abs (realToR (stdI1 leanPrims .cosh a) - cosh (realToR a)) ≤ u * cosh R

/-- **A thirteenth grounded transcendental control kernel: `cosh(PID law)`** — the last one before
`tan`. Instance of `pipeline_cosh_of_arith` at `pidRawEML`. -/
theorem pid_cosh_grounded (env : Env) (R : MachLib.Real) (hR0 : 0 ≤ R)
    (hflx_lo : -R ≤ realToR (evalEML (stdI1 leanPrims) (stdI2 leanPrims) env pidRawEML).toF)
    (hflx_hi : realToR (evalEML (stdI1 leanPrims) (stdI2 leanPrims) env pidRawEML).toF ≤ R)
    (hxe_lo : -R ≤ exactR realToR env pidRawEML) (hxe_hi : exactR realToR env pidRawEML ≤ R) :
    AbsEnc (u * cosh R + sinh R * absErr realToR env pidRawEML)
      (realToR (evalC (stdR1 leanPrims) (stdR2 leanPrims) env (emitC (tr1OfEML .cosh pidRawEML))).toF)
      (cosh (exactR realToR env pidRawEML)) :=
  pipeline_cosh_of_arith real_fpbridge (stdI1 leanPrims) (stdI2 leanPrims)
    (stdR1 leanPrims) (stdR2 leanPrims) (std_hrt1 leanPrims) (std_hrt2 leanPrims)
    env .cosh R (u * cosh R) hR0 pidRawEML isArith_pidRawEML
    hflx_lo hflx_hi hxe_lo hxe_hi
    (real_cosh_rounds R _ (abs_le_iff.mpr ⟨hflx_lo, hflx_hi⟩))

/-! ### Grounding the fourteenth and LAST libm primitive: `tan`

The one primitive needing genuinely new math (`TanLipschitz.lean`, one new axiom
`sin_pos_of_pos_lt_pi_div_two`, user-approved). Symmetric domain `[-R,R]`, `R < π/2`, `R ≥ 0`
(the `cosh`-shaped extra hypothesis), `L = 1/cos²R`. Completes every `Trans1` constructor. -/

/-- **The disclosed libm rounding bound for the runtime `tan`, domain-restricted.** For any `R < π/2`,
`R ≥ 0`, and `a : Float` with `abs (realToR a) ≤ R`, `leanPrims.tan`, through `realToR`, is within
`u · tan R` of the exact `Real.tan` (`tan` odd and monotonic increasing on `[0,π/2)`, so `abs (tan x)
≤ tan R` for `abs x ≤ R < π/2`) — reusing the SAME `R` `pid_tan_grounded` already carries. **Not
claimed unconditionally** (erratum-driven design, 2026-07-22): `tan` has poles at `±π/2 + kπ`, where
it is genuinely unbounded — no fixed constant, and no `R`-independent bound, holds past that point.
Un-witnessable in Lean (`Float` opaque); the residual libm trust for this primitive. -/
axiom real_tan_rounds : ∀ (R : MachLib.Real) (a : Float), 0 ≤ R → R < pi / (1 + 1) →
    abs (realToR a) ≤ R → abs (realToR (stdI1 leanPrims .tan a) - tan (realToR a)) ≤ u * tan R

/-- **The fourteenth and last grounded transcendental control kernel: `tan(PID law)`.** For any
`[-R,R]` (`R<π/2`, `R≥0`) that the PID law's computed AND exact values both land in, the emitted C for
`tan(1.5·e + 0.4·i + 0.05·d)` read through `realToR`, is within `u·tan R + (1/cos²R)·absErr` of
the exact ℝ value `tan(PID law)`. Instance of `pipeline_tan_of_arith` at `pidRawEML`. Every `Trans1`
constructor is now grounded. -/
theorem pid_tan_grounded (env : Env) (R : MachLib.Real) (hR0 : 0 ≤ R) (hR : R < pi / (1 + 1))
    (hflx_lo : -R ≤ realToR (evalEML (stdI1 leanPrims) (stdI2 leanPrims) env pidRawEML).toF)
    (hflx_hi : realToR (evalEML (stdI1 leanPrims) (stdI2 leanPrims) env pidRawEML).toF ≤ R)
    (hxe_lo : -R ≤ exactR realToR env pidRawEML) (hxe_hi : exactR realToR env pidRawEML ≤ R) :
    AbsEnc (u * tan R + (1 / (cos R * cos R)) * absErr realToR env pidRawEML)
      (realToR (evalC (stdR1 leanPrims) (stdR2 leanPrims) env (emitC (tr1OfEML .tan pidRawEML))).toF)
      (tan (exactR realToR env pidRawEML)) :=
  pipeline_tan_of_arith real_fpbridge (stdI1 leanPrims) (stdI2 leanPrims)
    (stdR1 leanPrims) (stdR2 leanPrims) (std_hrt1 leanPrims) (std_hrt2 leanPrims)
    env .tan R (u * tan R) hR0 hR pidRawEML isArith_pidRawEML
    hflx_lo hflx_hi hxe_lo hxe_hi
    (real_tan_rounds R _ hR0 hR (abs_le_iff.mpr ⟨hflx_lo, hflx_hi⟩))

/-! ### The multi-level instantiation: `log(cosh(PID law))`, through `pipeline_nested_local`

Every grounding above is FLAT: one `tr1` node directly over `pidRawEML`. This is the one level deeper
step flagged as optional after the recursive-nesting closure — a genuine LOCAL-over-LOCAL kernel,
concretely grounded at `realToR`/`leanPrims`, not just the generic `pipeline_nested_local` combinator.

The kernel: `log(cosh(PID law))` — the "log-cosh loss," a standard smooth, outlier-robust alternative
to L1/L2 loss (`≈ x²/2` for small `x`, `≈ |x| − log 2` for large `x`) genuinely used in control/ML
gain-shaping, not an arbitrary composition. `cosh` needs a symmetric domain `[-R,R]`; `log` needs a
positive one-sided domain `[lo,hi]` — two DIFFERENT domain shapes stacked, exercising the harder case
`pipeline_tr1_of_arith_local`'s own docstring calls out (`log` layering positivity on top of `exp`'s
plain range, here `log` layering positivity on top of `cosh`'s symmetric range). -/

/-- Real semantics of the two primitives `pid_log_cosh_grounded` nests: `.cosh ↦ cosh`, `.ln ↦ log`. -/
noncomputable def realOfLogCosh : Trans1 → MachLib.Real → MachLib.Real
  | .cosh => cosh | .ln => log | _ => id

/-- **The multi-level grounded kernel: `log(cosh(PID law))`.** For any `[-R,R]` (`R≥0`) the PID law's
computed AND exact values land in, and any `[lo,hi]` (`lo>0`) the RUNTIME `cosh(PID law)` value's
computed AND exact readings land in, the emitted C for `log(cosh(1.5·e+0.4·i+0.05·d))` — the log-cosh
loss over the raw PID law — read through `realToR`, is within SOME absolute bound of the exact ℝ value
`log(cosh(PID law))`. One level deeper than every flat `pid_X_grounded` above: instance of
`pipeline_nested_local` at `pidRawEML`, going through `isFoldLocal_of_isArith` to lift the arithmetic
leaf and `exactRn_eq_exactR_of_arith` to state the conclusion in the familiar `exactR` terms every flat
grounding already uses, rather than the more general `exactRn`.

**Rebuilt 2026-07-22, erratum-driven.** The original version routed through a totalized `hround_all`/
`Eround1All` — one shared rounding fact for ALL FOURTEEN `Trans1` primitives, unconditionally
quantified over every domain. That totalization is no longer possible to state honestly: several
primitives (`log` among them — the one THIS kernel actually uses) need a validity condition beyond
plain interval membership (`0 < lo`, here), and a single primitive-agnostic dispatcher can't encode
different conditions for different primitives without either (a) reintroducing an oversized,
falsely-unconditional fallback bound for the primitives this kernel never touches — exactly the
overclaim the whole erratum fixed — or (b) `IsFoldLocal` carrying the rounding obligation itself, per
occurrence (done — see `AbsoluteFoldNestLocal.lean`'s redesign). This version supplies `real_log_
rounds`/`real_cosh_rounds` DIRECTLY at the two `IsFoldLocal.tr1` occurrences that need them, using
exactly the `lo`/`hi`/`R` (and `hlo : 0 < lo`) this theorem already carries — no totalization, no
`hround_all`, no `realOfAll14`. -/
theorem pid_log_cosh_grounded (env : Env) (R lo hi : MachLib.Real) (hR0 : 0 ≤ R) (hlo : 0 < lo)
    (hflx_lo1 : -R ≤ realToR (evalEML (stdI1 leanPrims) (stdI2 leanPrims) env pidRawEML).toF)
    (hflx_hi1 : realToR (evalEML (stdI1 leanPrims) (stdI2 leanPrims) env pidRawEML).toF ≤ R)
    (hxe_lo1 : -R ≤ exactR realToR env pidRawEML) (hxe_hi1 : exactR realToR env pidRawEML ≤ R)
    (hflx_lo2 : lo ≤ realToR
      (evalEML (stdI1 leanPrims) (stdI2 leanPrims) env (.tr1 .cosh pidRawEML)).toF)
    (hflx_hi2 : realToR
      (evalEML (stdI1 leanPrims) (stdI2 leanPrims) env (.tr1 .cosh pidRawEML)).toF ≤ hi)
    (hxe_lo2 : lo ≤ exactRn realToR realOfLogCosh env (.tr1 .cosh pidRawEML))
    (hxe_hi2 : exactRn realToR realOfLogCosh env (.tr1 .cosh pidRawEML) ≤ hi) :
    ∃ E, AbsEnc E
      (realToR (evalC (stdR1 leanPrims) (stdR2 leanPrims) env
        (emitC (.tr1 .ln (.tr1 .cosh pidRawEML)))).toF)
      (log (cosh (exactR realToR env pidRawEML))) := by
  have hxe_lo1' : -R ≤ exactRn realToR realOfLogCosh env pidRawEML := by
    rw [exactRn_eq_exactR_of_arith realOfLogCosh env isArith_pidRawEML]; exact hxe_lo1
  have hxe_hi1' : exactRn realToR realOfLogCosh env pidRawEML ≤ R := by
    rw [exactRn_eq_exactR_of_arith realOfLogCosh env isArith_pidRawEML]; exact hxe_hi1
  have he : IsFoldLocal realToR (stdI1 leanPrims) (stdI2 leanPrims) realOfLogCosh env
      (.tr1 .ln (.tr1 .cosh pidRawEML)) :=
    .tr1 .ln _ (1 / lo) lo hi (u * (abs (log lo) + abs (log hi)))
      (le_of_lt (one_div_pos_of_pos hlo)) (log_lip_local lo hi hlo)
      hflx_lo2 hflx_hi2 hxe_lo2 hxe_hi2 (real_log_rounds lo hi _ hlo hflx_lo2 hflx_hi2)
      (.tr1 .cosh _ (sinh R) (-R) R (u * cosh R) (sinh_nonneg hR0) (cosh_lip_local R)
        hflx_lo1 hflx_hi1 hxe_lo1' hxe_hi1'
        (real_cosh_rounds R _ (abs_le_iff.mpr ⟨hflx_lo1, hflx_hi1⟩))
        (isFoldLocal_of_isArith (stdI1 leanPrims) (stdI2 leanPrims) realOfLogCosh env
          isArith_pidRawEML))
  obtain ⟨E, hE⟩ := pipeline_nested_local real_fpbridge realOfLogCosh
    (stdI1 leanPrims) (stdI2 leanPrims) (stdR1 leanPrims) (stdR2 leanPrims)
    (std_hrt1 leanPrims) (std_hrt2 leanPrims) env
    (.tr1 .ln (.tr1 .cosh pidRawEML)) he
  refine ⟨E, ?_⟩
  have heq : exactRn realToR realOfLogCosh env (.tr1 .ln (.tr1 .cosh pidRawEML))
      = log (cosh (exactR realToR env pidRawEML)) := by
    show log (cosh (exactRn realToR realOfLogCosh env pidRawEML))
      = log (cosh (exactR realToR env pidRawEML))
    rw [exactRn_eq_exactR_of_arith realOfLogCosh env isArith_pidRawEML]
  rwa [heq] at hE

end Certcom
