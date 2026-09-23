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
`∀ toR, FPBridge toR → P toR` certificate discharges to a statement about the
actual emitted-C computation, viewed through the real denotation, conditional only on that computation's float side
conditions (`FloatSafe`, since 2026-09-14). Grounding it *further* — deriving
`FPBridge realToR` rather than assuming it — is a Flocq-scale formalization of binary64 rounding,
outside Lean's `Float`.

The two axioms here are registered in `AxiomLedger` as disclosed-and-un-witnessable, so Theorem A's
footprint is auditable alongside the Khovanskii headlines: `pipeline_det_grounded` rests on exactly
`realToR`, `real_fpbridge`, the `MachLib.Real` axioms (witnessed against ℝ by Theorem B), and `u`.

**Restated 2026-09-14 from a measurement.** `tools/float_bridge/measure.py` found seven float-bridge axioms that this
file and `EMLCertcomGrounded.lean` rely on false as stated. Each is restated to what the measurement and an error
analysis (IEEE-754 rounding, and glibc's own bounds where it is not correctly rounded) both support, and every
theorem that rests on one carries the difference in its statement:

  * `real_fpbridge` is `FPBridgeFinite realToR` (`FloatRealBridge.lean`), so every grounded theorem below takes
    `hsafe : FloatSafe realToR … env e` (`AbsoluteFold.lean`): at each node of the kernel's evaluation a finite
    float result and, for a product, an exact product that is `0` or at least `DBL_MIN`. `hsafe` contains the
    root's finiteness, which `pid_tanh_grounded` took separately as `hfin` until this restatement.
  * `real_exp_rounds` needs a finite input, a finite result and an exact result of at least `DBL_MIN`, at `2u`;
    `real_sinh_rounds` and `real_cosh_rounds` a finite result, at `4u`; `real_log10_rounds` a finite input, at
    `3u`; `real_tan_rounds` a finite input, at `2u`. The kernels take the result conditions as hypotheses
    (`hexp` and `hnorm`, `hsinh`, `hcosh`); a finite input is inside `hsafe`.

Lean itself proves none of these for a concrete input, because `Float` is opaque. They are conditions a caller checks at
run time or guarantees by bounding its inputs, like the range hypotheses these theorems already took. Since 2026-09-14
two disclosed axioms turn such a bound into the finiteness conditions of `+`, `−`, `×`, negation and `floatOfR`:
`real_fpfinite` below and `real_round_finite` (`EMLCertcomGrounded.lean`). `FloatSafeInstances.lean` uses them. Later the
same day four more turn a bound on an argument into a finite `exp`, `sinh`, `cosh` or `log` result (`real_exp_finite` and
its siblings, below), and three say what the PID gains' `Float` literals are (`float_lit_1_5` and its siblings,
`EMLCertcomGrounded.lean`). With `u_le_half` they let `GroundedPIDInstances.lean` and `GroundedEMLInstances.lean`
instantiate most of the certificates below; those modules' docstrings name the ones that are still not instantiated.

## Non-finite inputs (2026-09-14)

`realToR` is the real value of a FINITE double. Nothing axiomatises it at `±∞` or NaN, so an axiom quantifying over every
`a : Float` constrains it there only through the axioms themselves. Until 2026-09-14 eight did: `real_log_rounds`,
`real_sqrt_rounds`, `real_asin_rounds`, `real_acos_rounds`, `real_sin_rounds`, `real_cos_rounds`, `real_atan_rounds` and
`real_abs_rounds`. Measured on glibc 2.39, aarch64 (and checked against Lean's own `#eval` wherever the bits are not a
NaN's, which `Float.toBits` does not expose): `fabs (+∞) = +∞`, `log (+∞) = sqrt (+∞) = +∞`, `atan (+∞)` is the finite
`π/2`, and `asin (+∞)`, `acos (+∞)`, `sin (+∞)`, `cos (+∞)` are one quiet NaN, which `log`, `sqrt`, `asin` and `acos`
return unchanged. On those values:

  * `real_log_rounds` at `a = +∞`, with `lo = hi = realToR (+∞)`, rules out `realToR (+∞) > 0` for any `u ≤ 1/2`, since
    `|v − log v| > 2u·|log v|` for every `v > 0`; `real_asin_rounds` and `real_acos_rounds` at `+∞` rule out
    `(−1, 0]` once `u < 1/3`, since `arcsin` and `arccos` differ by at least `π/2` there. So the eight read `+∞` as at most
    `−1`, and then `fabs (+∞) = +∞` forces `real_abs_eps ≥ 2`, and `atan (+∞) = π/2` forces `real_atan_eps` to about
    `3π/4` or more, where the measurement puts those constants at `0` and `1.11·10⁻¹⁶`.
  * At non-finite inputs the eight still had a common reading (every non-finite float read as `−1`, those two
    constants large), so none was false THERE (`real_log_rounds` was false at finite inputs, which its docstring records).
    `real_abs_eps = 0`, approved the same day, has no such reading: `fabs (+∞) = +∞` makes `realToR (+∞) ≥ 0`, `log` makes
    it `0`, and `asin`/`acos` at `0` then need `π/2 ≤ 3uπ/2`, which `u ≤ 2⁻⁵²` refutes. Lean cannot derive `False` from
    it, because it proves no equation between `Float` values; the axioms would have described no runtime at all.
    `FloatBridgeNonFinite.lean` checks that argument from the three measured equations.

So each of the eight now takes `a.isFinite = true`. That only narrows them and adds no trust; every caller already had
the finiteness (`FloatSafe.add_isFinite`, or a finite-input hypothesis). `real_sinh_rounds` and `real_cosh_rounds` take a
finite RESULT instead, which excludes non-finite inputs because the runtime `sinh` and `cosh` of `±∞` or NaN are not
finite; `tools/float_bridge/measure.py` checks that, and refuses to read any statement that admits a non-finite input.
-/

namespace Certcom

open MachLib.Real

/-- The value an IEEE-754 `Float` denotes as a `MachLib.Real`. Opaque: Lean's `Float` is a native
`@[extern]` type with no in-Lean real semantics, so the denotation is axiomatized, not defined. -/
axiom realToR : Float → MachLib.Real

/-- **The disclosed IEEE-754 model, as binary64 satisfies it.** Under `realToR`, `+`, `−` and `×` round the exact
real result to within `u` (`RoundsW u`) wherever the float result is finite and, for `×`, the exact product is `0`
or at least `DBL_MIN` in magnitude; negating a finite float is exact (`FPBridgeFinite`, whose docstring says why
each condition is what round-to-nearest needs). Structurally un-witnessable in Lean (`Float` is opaque); the
terminal trust of certcom Theorem A, disclosed exactly like `erf`.

**Restated 2026-09-14 from a measurement, because the statement before it was false.** It read
`axiom real_fpbridge : FPBridge realToR`, every pair of floats. A product whose exact value is a nonzero real below
`DBL_MIN` lands on the subnormal grid and misses `u`, by up to `2⁵³` times (the two smallest subnormals multiply to
`0`), and no single real value is within `u` of an overflowed result for every pair that overflows to it.
`tools/float_bridge/measure.py` over 615 001 pairs (random bits; products straddling `DBL_MIN`, including the exact
midpoint below it, which rounds up to it; sums landing on either side of `DBL_MIN`; sums and products near
overflow; subnormal operands): the old statement fails at 87 160 of the 1 647 378 operations with a finite result,
every one a product below `DBL_MIN`. The restated one holds at all 1 419 906 operations its hypotheses admit
(425 097 excluded), at most `0.9999989u`, as correct rounding allows. Command, from `foundations/`:
`python3 tools/float_bridge/measure.py`; `tools/float_bridge/registry.json` pins these numbers and keeps the old
statement as a control that must still fail. -/
axiom real_fpbridge : FPBridgeFinite realToR

/-- **Round-to-nearest's overflow rule, at `realToR`** (added 2026-09-14, owner-approved). For finite floats `a` and `b`,
the float `a + b`, `a − b` or `a * b` is finite whenever the EXACT real result of the operation on their real values is
at most `DBL_MAX` in magnitude, and negating a finite float gives a finite float (`FPFiniteOfRange`,
`FloatRealBridge.lean`, which says why this is what round-to-nearest-even does). Un-witnessable in Lean (`Float` is
opaque); disclosed like `real_fpbridge`. It is what lets `FloatSafe`'s finiteness half, `FloatFinite`, be discharged from
a bound on the inputs (`FloatSafeInstances.lean`).

**Measured before it was added.** `tools/float_bridge/measure.py` over 629 091 pairs of finite doubles (the pairs that
measure `real_fpbridge`, plus sums, differences and products exactly at `DBL_MAX`, exactly at the overflow tie
`DBL_MAX + 2^970`, and between the two): no violation at the 2 299 615 operations its hypotheses admit (216 749 excluded),
the largest exact result examined being `DBL_MAX` itself. Two controls must fail, and do: the range widened to include
the tie fails at 6 046 operations, every one exactly at the tie, and the rule with no range fails at 211 671. A sample of
the floats and of their finiteness is checked bit for bit against Lean's own `#eval`, the tie included.
`tools/float_bridge/registry.json` pins these numbers. -/
axiom real_fpfinite : FPFiniteOfRange realToR

/-- **The runtime `exp` of a finite float at most `709` is finite** (added 2026-09-14, owner-approved). `stdI1 leanPrims
.exp` is glibc's `exp`, whose result overflows only for inputs above `709.782712893384`, the largest double whose `exp` is
finite; `709` sits `0.78` inside that. Below, `exp` of a very negative input underflows to a subnormal or to `0`, which is
finite. Un-witnessable in Lean (`Float` is opaque). It is what lets a certificate's `hexp` hypothesis be discharged from a
bound on the argument.

**Measured before it was added.** `tools/float_bridge/measure.py` computes `leanPrims`'s `exp` as the runtime does (glibc
2.39 on aarch64, through ctypes, checked against Lean's own `#eval`, `Float.isFinite` included) over 941 513 doubles: dense
steps on `[−750, 710]`, results just above every power of two, the whole subnormal range, and 5 000 consecutive doubles on
each side of `709`, of `709.782712893384` and of `710`. No non-finite result at the 901 678 its hypotheses admit (39 835
excluded), the largest being `709` itself. The control with the bound widened to `710` fails at 11 037 inputs, every one at
or above `709.7827128933841`, so the bound sits `0.7827` inside the measured boundary. `tools/float_bridge/registry.json`
pins these numbers. -/
axiom real_exp_finite : ∀ a : Float, a.isFinite = true → realToR a ≤ natCast 709 →
    (stdI1 leanPrims .exp a).isFinite = true

/-- **The runtime `sinh` of a finite float at most `710` in magnitude is finite** (added 2026-09-14, owner-approved).
`stdI1 leanPrims .sinh` is the runtime's composite (`EMLToCRuntime.lean`): `x` itself below `MG_SINH_X_MAX`; with `a = |x|`
and `t = expm1 a`, `½(2t − t·t/(t+1))` below `1` and `½(t + t/(t+1))` below `22` (since 2026-09-15), `½·exp a` up to
`709.78`, and `(½·w)·w` with `w = exp(a/2)` above; then `x`'s sign. Its result overflows only for `|x|` above
`710.4758600739439`, the largest double whose `sinh` is finite; `710` sits `0.47` inside that. Un-witnessable in Lean
(`Float` is opaque).

**Measured before it was added, and again on 2026-09-15 on the `expm1` body.** `tools/float_bridge/measure.py` computes the
composite as `leanPrims` does, over 796 928 doubles: dense steps on `[−712, 712]`, the large branch densely, results just
above every power of two, both sides of the splits at `1` and `22`, and 3 000 consecutive doubles on each side of `±710`,
`±710.4758600739439` and `±711`. No non-finite result at the 670 935 its hypotheses admit (125 993 excluded), the largest
being `710` itself. The control with the bound widened to `711` fails at 12 172 inputs, every one at
`|x| ≥ 710.475860073944`, so the bound sits `0.4758` inside the measured boundary. `tools/float_bridge/registry.json` pins
these numbers. -/
axiom real_sinh_finite : ∀ a : Float, a.isFinite = true → abs (realToR a) ≤ natCast 710 →
    (stdI1 leanPrims .sinh a).isFinite = true

/-- **The runtime `cosh` of a finite float at most `710` in magnitude is finite** (added 2026-09-14, owner-approved).
`stdI1 leanPrims .cosh` is `(eᵃ + e⁻ᵃ)·½` for `a = |x| ≤ 709.78` and `(½·w)·w` with `w = exp(a/2)` above. Its result
overflows only for `|x|` above `710.4758600739439`, as `sinh`'s does; `710` sits `0.47` inside that. Un-witnessable in Lean
(`Float` is opaque).

**Measured before it was added**, over the same 779 473 doubles as `real_sinh_finite`: no non-finite result at the
653 480 its hypotheses admit (125 993 excluded), the largest being `710` itself; the control widened to `711` fails at 12 172
inputs, every one at `|x| ≥ 710.475860073944`. `tools/float_bridge/registry.json` pins these numbers. -/
axiom real_cosh_finite : ∀ a : Float, a.isFinite = true → abs (realToR a) ≤ natCast 710 →
    (stdI1 leanPrims .cosh a).isFinite = true

/-- **The runtime `log` of a finite positive float is finite** (added 2026-09-14, owner-approved). `stdI1 leanPrims .ln`
is glibc's `log`. For a positive finite double its result lies between `log (2⁻¹⁰⁷⁴) ≈ −744.44` and
`log DBL_MAX ≈ 709.78`; at `0` it is `−∞` and below `0` it is NaN, which is why the hypothesis is strict. Un-witnessable in
Lean (`Float` is opaque).

**Measured before it was added.** `tools/float_bridge/measure.py` over 428 492 doubles: log-spaced over the whole
positive range, the denormals, powers of ten and of two, random positive bit patterns, and negatives and zeros. No non-finite
result at the 378 478 its hypotheses admit (50 014 excluded), the smallest being `5e-324`. The control with `0 ≤ realToR a`
in place of `0 < realToR a` fails at 4 inputs, every one a zero. `tools/float_bridge/registry.json` pins these numbers. -/
axiom real_log_finite : ∀ a : Float, a.isFinite = true → 0 < realToR a →
    (stdI1 leanPrims .ln a).isFinite = true

/-- **Keystone — a forward-error certificate on real `Float` bytes.**

The value the *emitted C* computes for the cancelling determinant `x·y − z·w` (`emitC detEML`, run by
`evalC`), read through the real denotation `realToR`, is within the absolute bound
`u·(2+u)·(|X·Y| + |Z·W|)` of the exact ℝ determinant `X·Y − Z·W` — with **no `FPBridge` hypothesis**:
the proved `pipeline_det` is discharged by `real_fpbridge`. Valid in the cancelling regime `X·Y ≈ Z·W`
(absolute bound, no sign or non-vanishing assumption). This is the first certcom-A certificate that
touches the actual artifact rather than an arbitrary `toR`.

`detEML` has no transcendental nodes, so the runtime/interpretation parameters are inert (the `hrt`
obligations close by `rfl`); the only trust beyond `MachLib.Real`'s (ℝ-witnessed) axioms is the one
disclosed IEEE-754 axiom `real_fpbridge`.

**Takes `hsafe` since 2026-09-14**: the float side conditions of the kernel's evaluation (`FloatSafe`), which the
restated `real_fpbridge` (`FPBridgeFinite`) needs. Until then this theorem rested on `FPBridge realToR`, which
binary64 does not satisfy. -/
theorem pipeline_det_grounded (env : Env)
    (hsafe : FloatSafe realToR (fun _ _ => 0) (fun _ _ _ => 0) env detEML) :
    AbsEnc (u * (1 + 1 + u) * (abs (realToR (env "x").toF * realToR (env "y").toF)
                              + abs (realToR (env "z").toF * realToR (env "w").toF)))
      (realToR (evalC (fun _ _ => 0) (fun _ _ _ => 0) env (emitC detEML)).toF)
      (realToR (env "x").toF * realToR (env "y").toF
        - realToR (env "z").toF * realToR (env "w").toF) :=
  pipeline_det_finite real_fpbridge (fun _ _ => 0) (fun _ _ _ => 0) (fun _ _ => 0) (fun _ _ _ => 0)
    (fun _ _ => rfl) (fun _ _ _ => rfl) env hsafe

/-- **The whole arithmetic fragment, grounded.** For *every* `IsArith` EML tree, the value the emitted
C computes — through the real denotation `realToR` — is within the folded absolute forward error
`absErr` of the exact ℝ value, with **no `FPBridge` hypothesis** (discharged by `real_fpbridge`). The
general lever: `pipeline_det_grounded` and `pid_grounded` are both instances.

**Takes `hsafe` since 2026-09-14**: the float side conditions of the kernel's evaluation (`FloatSafe`), which the
restated `real_fpbridge` (`FPBridgeFinite`) needs. Until then this theorem rested on `FPBridge realToR`, which
binary64 does not satisfy. -/
theorem pipeline_arith_grounded (env : Env) (e : EML) (he : IsArith e)
    (hsafe : FloatSafe realToR (fun _ _ => 0) (fun _ _ _ => 0) env e) :
    AbsEnc (absErr realToR env e)
      (realToR (evalC (fun _ _ => 0) (fun _ _ _ => 0) env (emitC e)).toF)
      (exactR realToR env e) :=
  pipeline_arith_finite real_fpbridge (fun _ _ => 0) (fun _ _ _ => 0) (fun _ _ => 0) (fun _ _ _ => 0)
    (fun _ _ => rfl) (fun _ _ _ => rfl) env e he hsafe

/-- The raw one-step PID law `Kp·e + Ki·i + Kd·d` (before the saturating `clamp`), with the shipped
`pid.eml` gains `Kp = 1.5`, `Ki = 0.4`, `Kd = 0.05` as literal constants and the three channels
`e`/`i`/`d` as inputs — left-associated exactly as `FixedPoint.pid_fx_fwd_error` writes it. This is the
arithmetic datapath of the dual-target controller that Forge compiles to the ESP32 (C) and Arty (RTL);
`clamp = max lo (min · hi)` is a separate saturating wrapper, outside the `+/−/×` fragment. -/
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
ESP32, now carrying a forward-error certificate on real `Float` bytes (modulo the one
disclosed IEEE-754 axiom `real_fpbridge`). Instance of `pipeline_arith_grounded` at `pidRawEML`.

**Takes `hsafe` since 2026-09-14**: the float side conditions of the kernel's evaluation (`FloatSafe`), which the
restated `real_fpbridge` (`FPBridgeFinite`) needs. Until then this theorem rested on `FPBridge realToR`, which
binary64 does not satisfy. -/
theorem pid_grounded (env : Env)
    (hsafe : FloatSafe realToR (fun _ _ => 0) (fun _ _ _ => 0) env pidRawEML) :
    AbsEnc (absErr realToR env pidRawEML)
      (realToR (evalC (fun _ _ => 0) (fun _ _ _ => 0) env (emitC pidRawEML)).toF)
      (exactR realToR env pidRawEML) :=
  pipeline_arith_grounded env pidRawEML isArith_pidRawEML hsafe

/-! ### Grounding a transcendental: the `tanh`-saturated PID

Arithmetic grounds on `FPBridge` alone. A transcendental node adds one thing — the libm primitive's
rounding, the "irreducible trust" the T2/T3 work isolated. `tanh` is globally `1`-Lipschitz, so it
enters the fold with no domain hypothesis; and `tanh`-saturation is a real control primitive (a smooth
alternative to the hard `clamp`, and — unlike `clamp` — inside the certified `+/−/×/tr1` fragment). -/

/-- **The disclosed libm rounding bound for the runtime `tanh`: within `2u` of `Real.tanh` at every FINITE
`a`.** `stdI1 leanPrims .tanh` is the runtime's own composition (`EMLToCRuntime.lean`): `x` itself for
`|x| ≤ 1.3538603431225864e-8`; else, with `a = |x|`, `copysign(−t/(t+2), x)` with `t = expm1(−2a)` below `0.5` and
`copysign(1 − 2/(t+2), x)` with `t = expm1(2a)` from `0.5` (since 2026-09-15; until then `copysign((1−t)/(1+t), x)`
with `t = exp(−2a)`, which cancelled below `1`). Un-witnessable in Lean (`Float` opaque), disclosed like
`real_fpbridge`; the residual libm trust for this primitive.

**Restated 2026-09-14 from a measurement, because the statement before it was false.** It read
`∀ (R : MachLib.Real) (a : Float), abs (realToR a) ≤ R → … ≤ u`. The hypothesis constrained nothing (every
`a` has some `R`), and the bound does not hold. `tools/float_bridge/measure.py` computes the composite exactly
as `leanPrims` does (glibc 2.39's `exp` and `expm1` on aarch64 through ctypes, IEEE doubles, `floatCopySign`'s
bits), checks a sample of those floats against Lean's own `#eval` bit for bit, and compares with mpmath's `tanh` at
256 bits. On the body before 2026-09-15 the error exceeded `u` at 25 535 of 470 235 finite inputs, at most `1.4996u`
(`x = −7.834942349654755`), and stayed within `2u`, at most `0.7498` of the bound.

**Re-measured 2026-09-15 on the `expm1` body.** Its inputs: `[-30, 30]` in steps of `10⁻³` and `[-1, 1]` in steps of
`10⁻⁵`; `|x|` log-spaced down to the smallest subnormal; 2 000 consecutive doubles on each side of the small-argument
threshold, of the split at `0.5` and of `1`, and runs around `18.715`, `19.06` and `20`; `[0.3, 1)` densely; points
where `t` crosses a power of two; the largest absolute errors forge's `tools/scripts/measure_runtime_hyperbolics.py`
found against binary128 `tanhl`; magnitudes up to `DBL_MAX`; random finite bit patterns; and a local search around the
25 worst points: 647 367 finite inputs. Against `u` the error exceeds the bound at 3 519 of them. Against `2u` there is
no violation; the largest error is `0.7160` of the bound (`1.4319u`, at `x = 0.550098328643078`).

**Why `2u`, not tighter, and why the split is at `0.5`.** A first-order error estimate, every operation at its worst
at once with glibc's measured `expm1` error, stays under `1.499u` for the small form below `0.5` and `1.631u` for the
large form from `0.5`. Kept up to glibc's own split at `1`, the small form's estimate reaches `2.335u` as `a → 1`, past
the bound, and forge's harness measures that split at `1.739u`. That is an estimate, not a proof; `2u` is `0.369u`
above it and `0.568u` above the measured maximum.

**The domain is the honest one: finite `a`.** `realToR` of `±inf` or `NaN` has no real value to compare,
so nothing was measured there and nothing is claimed; the old `R` excluded neither.

Command, from `foundations/`: `python3 tools/float_bridge/measure.py`. Its registry pins these numbers, and
`tools/check_all.sh` fails if they move. -/
axiom real_tanh_rounds : ∀ (a : Float), a.isFinite = true →
    abs (realToR (stdI1 leanPrims .tanh a) - tanh (realToR a)) ≤ u + u

/-- **A grounded transcendental control kernel.** The emitted C for `tanh(1.5·e + 0.4·i + 0.05·d)` — a
soft-saturated PID — read through `realToR`, is within `2u + absErr` of the exact ℝ value `tanh(PID law)`,
GIVEN `hsafe`, the float side conditions of the PID law's evaluation (`FloatSafe`), which include that its
computed value is a finite float: `real_tanh_rounds`'s hypothesis (`FloatSafe.add_isFinite`), with its constant,
since 2026-09-14. Until then this theorem took a bound `R` on that value, which every value
satisfies, and concluded `u + absErr` from an axiom measured false. `FPBridge` is discharged by
`real_fpbridge` given the same `hsafe` (restated that day to `FPBridgeFinite`; the theorem took `hfin`, the
finiteness alone, in between), the runtime correspondence by the proven `std_hrt` at Lean's libm basis, and
the one `tanh` rounding by the disclosed `real_tanh_rounds`. First grounded certificate reaching a transcendental
layer over real `Float` bytes. `1`-Lipschitz `tanh` (`globLip_lipschitz`) amplifies the arithmetic fold's `absErr` by
`1`. -/
theorem pid_tanh_grounded (env : Env)
    (hsafe : FloatSafe realToR (stdI1 leanPrims) (stdI2 leanPrims) env pidRawEML) :
    AbsEnc ((u + u) + 1 * absErr realToR env pidRawEML)
      (realToR (evalC (stdR1 leanPrims) (stdR2 leanPrims) env (emitC (tr1OfEML .tanh pidRawEML))).toF)
      (tanh (exactR realToR env pidRawEML)) :=
  pipeline_tr1_of_arith_finite real_fpbridge (stdI1 leanPrims) (stdI2 leanPrims)
    (stdR1 leanPrims) (stdR2 leanPrims) (std_hrt1 leanPrims) (std_hrt2 leanPrims)
    env .tanh tanh 1 (u + u)
    (le_of_lt zero_lt_one_ax) (fun p q => by rw [one_mul_thm]; exact tanh_lipschitz p q)
    pidRawEML isArith_pidRawEML hsafe (real_tanh_rounds _ (FloatSafe.add_isFinite hsafe))

/-! ### Grounding a second libm primitive: `exp`, LOCALLY Lipschitz

`tanh` is globally `1`-Lipschitz, so `pid_tanh_grounded` needed no domain hypothesis. `exp` is not
globally Lipschitz (unbounded growth), so grounding it goes through `pipeline_exp_of_arith`
(`AbsoluteFoldLocal.lean`) instead: `L = exp hi` on any caller-supplied `[lo,hi]`, honestly conditional
on the PID law's value actually landing in that range — the expected, correct shape for a *local*
Lipschitz primitive, not a shortcoming relative to `tanh`'s unconditional result. -/

/-- **The disclosed libm rounding bound for the runtime `exp`, domain-restricted.** For a finite `a` whose float
`exp` is finite and whose exact `exp` is at least `DBL_MIN`, and any `hi ≥ realToR a`, `leanPrims.exp`, through
`realToR`, is within `2u · exp hi` of the exact `Real.exp` (relative error, uniformized over the range `hi` the way
`exp_lip_local`'s `L := exp hi` uniformizes a Lipschitz bound). Un-witnessable in Lean (`Float` opaque); the
residual libm trust for this primitive.

**Restated 2026-09-14 from a measurement, because the statement before it was false.** It read
`∀ (hi : MachLib.Real) (a : Float), realToR a ≤ hi → … ≤ u * exp hi`, and three things break it:

  * a subnormal or zero result cannot be within `u` of its exact value, relative to it (up to `2⁵³` times over);
  * an overflowed result, or an input `±∞` or NaN, has no real value to be near, and `hi` excluded none of them;
  * glibc's `exp` is not correctly rounded. Its source (glibc 2.39 `sysdeps/ieee754/dbl-64/e_exp.c`) bounds the
    error by `0.5 + 1.11/N` ulp plus a polynomial term, with `N = 2⁷ = 128`: about `0.509` ulp, which is up to
    about `1.018u` relative to a result just above a power of two, where one ulp is `2u`.

`tools/float_bridge/measure.py` over 927 010 inputs, including doubles whose result lies just above `2ᵏ` for every
`k` and the whole subnormal range: the old statement fails at 135 179 of them, and even with subnormal and
non-finite results excluded, `u` fails at 5 (at most `1.002752u`, at `x = −343.10586764112986`). The restated
statement holds at all 780 992 inputs its hypotheses admit (146 018 excluded), at most `0.501376` of `2u`, which
is `1.002752u`. `2u` is above the analysis bound and about twice the measured maximum.
`tools/float_bridge/registry.json` pins these numbers and keeps both failing forms as controls. -/
axiom real_exp_rounds : ∀ (hi : MachLib.Real) (a : Float), a.isFinite = true →
    (stdI1 leanPrims .exp a).isFinite = true → dblMin ≤ exp (realToR a) → realToR a ≤ hi →
    abs (realToR (stdI1 leanPrims .exp a) - exp (realToR a)) ≤ (u + u) * exp hi

/-- **A second grounded transcendental control kernel: `exp(PID law)`.** For any `[lo,hi]` the PID law's computed
AND exact values both land in, the emitted C for `exp(1.5·e + 0.4·i + 0.05·d)` — an exponential-gain variant of the
soft-saturated controller — read through `realToR`, is within `2u · exp hi + exp hi · absErr` of the exact ℝ value
`exp(PID law)`. `FPBridge` is discharged by `real_fpbridge` given `hsafe`, the runtime correspondence by
`std_hrt1`/`std_hrt2` at Lean's libm basis, and the one `exp` rounding by the disclosed, domain-restricted
`real_exp_rounds`, at `hi` from the SAME `hflx_hi` the Lipschitz part uses. Since 2026-09-14 that axiom also needs
its input finite (inside `hsafe`), its float result finite (`hexp`) and its exact result at least `DBL_MIN`, which
`hnorm : dblMin ≤ exp lo` gives through `hflx_lo`; its constant is `2u` where it was `u`, and `hsafe` is new too.
Second grounded certificate reaching a transcendental layer over real `Float` bytes. Instance of
`pipeline_exp_of_arith_finite` at `pidRawEML`. -/
theorem pid_exp_grounded (env : Env) (lo hi : MachLib.Real)
    (hsafe : FloatSafe realToR (stdI1 leanPrims) (stdI2 leanPrims) env pidRawEML)
    (hexp : (stdI1 leanPrims .exp (evalEML (stdI1 leanPrims) (stdI2 leanPrims) env pidRawEML).toF).isFinite = true)
    (hnorm : dblMin ≤ exp lo)
    (hflx_lo : lo ≤ realToR (evalEML (stdI1 leanPrims) (stdI2 leanPrims) env pidRawEML).toF)
    (hflx_hi : realToR (evalEML (stdI1 leanPrims) (stdI2 leanPrims) env pidRawEML).toF ≤ hi)
    (hxe_lo : lo ≤ exactR realToR env pidRawEML) (hxe_hi : exactR realToR env pidRawEML ≤ hi) :
    AbsEnc ((u + u) * exp hi + exp hi * absErr realToR env pidRawEML)
      (realToR (evalC (stdR1 leanPrims) (stdR2 leanPrims) env (emitC (tr1OfEML .exp pidRawEML))).toF)
      (exp (exactR realToR env pidRawEML)) :=
  pipeline_exp_of_arith_finite real_fpbridge (stdI1 leanPrims) (stdI2 leanPrims)
    (stdR1 leanPrims) (stdR2 leanPrims) (std_hrt1 leanPrims) (std_hrt2 leanPrims)
    env .exp lo hi ((u + u) * exp hi) pidRawEML isArith_pidRawEML hsafe
    hflx_lo hflx_hi hxe_lo hxe_hi
    (real_exp_rounds hi _ (FloatSafe.add_isFinite hsafe) hexp (le_trans hnorm (exp_monotone hflx_lo)) hflx_hi)

/-! ### Grounding a third libm primitive: `log`, LOCALLY Lipschitz on a positive domain

Same shape as `exp` — not globally Lipschitz, so through the local-Lipschitz lever
(`pipeline_log_of_arith`, `L = 1/lo`) — with one further honest cost: `log` additionally needs the
domain to be strictly positive (`lo > 0`, not just bounded), since `log` itself is only meaningfully
Lipschitz — and only defined analytically — on `(0,∞)`. Third data point on what "libm primitive
grounding" (certcom-A scoping doc item 5) costs per primitive: a disclosed rounding constant always,
plus a domain hypothesis unless the primitive happens to be globally Lipschitz like `tanh`, plus
(for `log` specifically) a positivity side-condition on top of the plain range bound. -/

/-- **The disclosed libm rounding bound for the runtime `log`, domain-restricted.** For any finite `a` and
`0 < lo ≤ realToR a ≤ hi`, `leanPrims.log`, through `realToR`, is within `2u · (abs (log lo) + abs (log hi))` of the
exact `Real.log` — a safe two-sided bound (log monotonic, so `log (realToR a) ∈ [log lo, log hi]`, and
`abs (log (realToR a)) ≤ abs (log lo) + abs (log hi)` regardless of whether that interval straddles `0`), reusing exactly
the `lo`/`hi` every caller (`pid_log_grounded`, Track C's `eml_var_var_*_grounded`) already carries. `log` is
undefined/`NaN` at or below `0`, so no bound is claimed there (2026-07-22). Un-witnessable in Lean (`Float` opaque); the
residual libm trust for this primitive.

**Restated 2026-09-14 from a measurement, because the statement before it was false.** It read
`∀ (lo hi : MachLib.Real) (a : Float), 0 < lo → lo ≤ realToR a → realToR a ≤ hi → … ≤ u * (abs (log lo) + abs (log hi))`.
Two things break it:

  * glibc's `log` is not correctly rounded. Its source (glibc 2.39 `sysdeps/ieee754/dbl-64/e_log.c`) bounds the error by
    about `0.52` ulp, which is up to about `1.04u` relative to a result just above a power of two. The harness's inputs had
    no such result until this restatement, and it pinned a maximum of `u` itself (`1.000000`) with no violation.
    `tools/float_bridge/measure.py`, with inputs `x = e^(±2ʲ)` packed on both sides added: the old statement fails at 20
    inputs, at most `1.0162u`, at `x = 1.1331484531994689`, where `log x` is just above `2⁻³` (take `lo = 1`, `hi = x`).
    The restated one holds at every input its hypotheses admit, at most about `0.51` of `2u`.
  * nothing excluded an input `±∞` or NaN, where `realToR` has no real value; `FPGrounding`'s section
    "Non-finite inputs" says why that is not harmless. `a.isFinite = true` narrows it.

`tools/float_bridge/registry.json` pins the numbers and keeps the old statement as a control that must still fail. -/
axiom real_log_rounds : ∀ (lo hi : MachLib.Real) (a : Float), a.isFinite = true → 0 < lo → lo ≤ realToR a →
    realToR a ≤ hi → abs (realToR (stdI1 leanPrims .ln a) - log (realToR a)) ≤ (u + u) * (abs (log lo) + abs (log hi))

/-- **A third grounded transcendental control kernel: `log(PID law)`.** For any `[lo,hi]` with `lo>0`
that the PID law's computed AND exact values both land in, the emitted C for
`log(1.5·e + 0.4·i + 0.05·d)` — a logarithmic-gain variant of the controller (e.g. a decibel-scaled
error signal) — read through `realToR`, is within `2u·(abs(log lo)+abs(log hi)) + (1/lo)·absErr` of the
exact ℝ value `log(PID law)`, with **no `FPBridge` and no ∀-primitive rounding hypothesis**: `FPBridge`
is discharged by `real_fpbridge`, the runtime correspondence by `std_hrt1`/`std_hrt2`, and the one
`log` rounding by the disclosed, domain-restricted `real_log_rounds` — discharged from the SAME
`hlo`/`hflx_lo`/`hflx_hi` this theorem already required for the Lipschitz part, and from `hsafe` for its finite
input. Third grounded transcendental kernel over real `Float` bytes. Instance of
`pipeline_log_of_arith_finite` at `pidRawEML`.

**Takes `hsafe` since 2026-09-14**: the float side conditions of the kernel's evaluation (`FloatSafe`), which the
restated `real_fpbridge` (`FPBridgeFinite`) needs. Until then this theorem rested on `FPBridge realToR`, which
binary64 does not satisfy. Later that day `real_log_rounds` was restated from a measurement too, and the rounding
constant here is `2u` where it was `u`. -/
theorem pid_log_grounded (env : Env) (lo hi : MachLib.Real) (hlo : 0 < lo)
    (hsafe : FloatSafe realToR (stdI1 leanPrims) (stdI2 leanPrims) env pidRawEML)
    (hflx_lo : lo ≤ realToR (evalEML (stdI1 leanPrims) (stdI2 leanPrims) env pidRawEML).toF)
    (hflx_hi : realToR (evalEML (stdI1 leanPrims) (stdI2 leanPrims) env pidRawEML).toF ≤ hi)
    (hxe_lo : lo ≤ exactR realToR env pidRawEML) (hxe_hi : exactR realToR env pidRawEML ≤ hi) :
    AbsEnc ((u + u) * (abs (log lo) + abs (log hi)) + (1 / lo) * absErr realToR env pidRawEML)
      (realToR (evalC (stdR1 leanPrims) (stdR2 leanPrims) env (emitC (tr1OfEML .ln pidRawEML))).toF)
      (log (exactR realToR env pidRawEML)) :=
  pipeline_log_of_arith_finite real_fpbridge (stdI1 leanPrims) (stdI2 leanPrims)
    (stdR1 leanPrims) (stdR2 leanPrims) (std_hrt1 leanPrims) (std_hrt2 leanPrims)
    env .ln lo hi ((u + u) * (abs (log lo) + abs (log hi))) hlo pidRawEML isArith_pidRawEML hsafe
    hflx_lo hflx_hi hxe_lo hxe_hi (real_log_rounds lo hi _ (FloatSafe.add_isFinite hsafe) hlo hflx_lo hflx_hi)

/-! ### Grounding a fourth libm primitive: `sin`, back to GLOBALLY Lipschitz

`sin` is globally `1`-Lipschitz (`TrigLipschitz.sin_lipschitz`), same shape as `tanh` — no domain
hypothesis needed, straight through `pipeline_tr1_of_arith`. Second data point (after `tanh`) on the
globally-Lipschitz side of the primitive basis, confirming that side really is as cheap as `tanh`
suggested and not a one-off — unlike `exp`/`log`, no domain bookkeeping at all. -/

/-- The disclosed libm rounding bound for the runtime `sin`. Same status as `real_tanh_eps`: the
composite `leanPrims.sin`, through `realToR`, is within a fixed `real_sin_eps` of the exact `Real.sin`.
Un-witnessable in Lean (opaque `Float`); the residual libm trust for this primitive.

**Confirmed unconditional (2026-07-22 audit, not changed)** — unlike `exp`/`sinh`/`cosh`/`tanh`,
`sin` is a NATIVE `Prims` field (`Float.sin`), not an exp-composite, so it cannot hit the overflow
failures those primitives' erratum fixes address (`inf`, and, for the `tanh` quotient used before
forge `51337a3`, `inf/inf = NaN`). Its mathematical output is bounded
(`abs (sin x) ≤ 1` for every real `x`), so — unlike `exp` (genuinely unbounded, no fixed constant
works), `log`/`sqrt`/`asin`/`acos` (undefined outside a domain, `NaN` outside it), or `tan` (poles) —
a fixed `real_sin_eps` COULD be a true statement about the real runtime for every `Float`, PROVIDED
it's calibrated large enough to cover known accuracy degradation from large-argument range reduction
(a real, if second-order, libm concern for huge `|a|` — a genuinely different, milder failure mode
than the others' `NaN`/`inf`/unboundedness). Not provably false the way the ten fixed axioms were;
left unconditional.

**Narrowed to finite inputs on 2026-09-14.** The unconditional form still quantified over `±∞` and NaN, where `realToR`
has no real value, and together with its neighbours it pinned what those floats read back as; this file's section
"Non-finite inputs" says what that forced. `a.isFinite = true` only narrows it. -/
axiom real_sin_eps : MachLib.Real

axiom real_sin_rounds : ∀ a : Float, a.isFinite = true →
    abs (realToR (stdI1 leanPrims .sin a) - sin (realToR a)) ≤ real_sin_eps

/-- **A fourth grounded transcendental control kernel: `sin(PID law)`.** The emitted C for
`sin(1.5·e + 0.4·i + 0.05·d)` — an oscillatory-gain variant of the controller — read through
`realToR`, is within `real_sin_eps + absErr` of the exact ℝ value `sin(PID law)`, with **no `FPBridge`
and no ∀-primitive rounding hypothesis** and no domain hypothesis (`sin` is
globally Lipschitz, same as `tanh`). Instance of `pipeline_tr1_of_arith_finite` at `pidRawEML`.

**Takes `hsafe` since 2026-09-14**: the float side conditions of the kernel's evaluation (`FloatSafe`), which the
restated `real_fpbridge` (`FPBridgeFinite`) needs. Until then this theorem rested on `FPBridge realToR`, which
binary64 does not satisfy. -/
theorem pid_sin_grounded (env : Env)
    (hsafe : FloatSafe realToR (stdI1 leanPrims) (stdI2 leanPrims) env pidRawEML) :
    AbsEnc (real_sin_eps + 1 * absErr realToR env pidRawEML)
      (realToR (evalC (stdR1 leanPrims) (stdR2 leanPrims) env (emitC (tr1OfEML .sin pidRawEML))).toF)
      (sin (exactR realToR env pidRawEML)) :=
  pipeline_tr1_of_arith_finite real_fpbridge (stdI1 leanPrims) (stdI2 leanPrims)
    (stdR1 leanPrims) (stdR2 leanPrims) (std_hrt1 leanPrims) (std_hrt2 leanPrims)
    env .sin sin 1 real_sin_eps
    (le_of_lt zero_lt_one_ax) (fun p q => by rw [one_mul_thm]; exact sin_lipschitz p q)
    pidRawEML isArith_pidRawEML hsafe (real_sin_rounds _ (FloatSafe.add_isFinite hsafe))

/-! ### Grounding a fifth libm primitive: `cos`, also GLOBALLY Lipschitz

Third data point on the globally-Lipschitz side (`TrigLipschitz.cos_lipschitz`, `L=1`), identical
pattern to `tanh`/`sin` — no domain hypothesis. -/

/-- The disclosed libm rounding bound for the runtime `cos`. Same status as `real_sin_eps`: the
composite `leanPrims.cos`, through `realToR`, is within a fixed `real_cos_eps` of the exact `Real.cos`.
Un-witnessable in Lean (opaque `Float`); the residual libm trust for this primitive.

**Confirmed unconditional (2026-07-22 audit, not changed)** — same reasoning as `real_sin_eps`
above: native `Prims` field, bounded output, no `inf/inf`/`NaN`/pole failure mode. **Narrowed to finite inputs on
2026-09-14**, for the reason `real_sin_eps` gives. -/
axiom real_cos_eps : MachLib.Real

axiom real_cos_rounds : ∀ a : Float, a.isFinite = true →
    abs (realToR (stdI1 leanPrims .cos a) - cos (realToR a)) ≤ real_cos_eps

/-- **A fifth grounded transcendental control kernel: `cos(PID law)`.** The emitted C for
`cos(1.5·e + 0.4·i + 0.05·d)` read through `realToR` is within `real_cos_eps + absErr` of the exact
ℝ value `cos(PID law)`, with no domain hypothesis — `cos` is globally Lipschitz, same as `tanh`/`sin`. Instance
of `pipeline_tr1_of_arith_finite` at `pidRawEML`.

**Takes `hsafe` since 2026-09-14**: the float side conditions of the kernel's evaluation (`FloatSafe`), which the
restated `real_fpbridge` (`FPBridgeFinite`) needs. Until then this theorem rested on `FPBridge realToR`, which
binary64 does not satisfy. -/
theorem pid_cos_grounded (env : Env)
    (hsafe : FloatSafe realToR (stdI1 leanPrims) (stdI2 leanPrims) env pidRawEML) :
    AbsEnc (real_cos_eps + 1 * absErr realToR env pidRawEML)
      (realToR (evalC (stdR1 leanPrims) (stdR2 leanPrims) env (emitC (tr1OfEML .cos pidRawEML))).toF)
      (cos (exactR realToR env pidRawEML)) :=
  pipeline_tr1_of_arith_finite real_fpbridge (stdI1 leanPrims) (stdI2 leanPrims)
    (stdR1 leanPrims) (stdR2 leanPrims) (std_hrt1 leanPrims) (std_hrt2 leanPrims)
    env .cos cos 1 real_cos_eps
    (le_of_lt zero_lt_one_ax) (fun p q => by rw [one_mul_thm]; exact cos_lipschitz p q)
    pidRawEML isArith_pidRawEML hsafe (real_cos_rounds _ (FloatSafe.add_isFinite hsafe))

/-! ### Grounding a sixth libm primitive: `atan`, also GLOBALLY Lipschitz

Fourth data point on the globally-Lipschitz side (`InverseTrig.atan_lipschitz`, `L=1`), identical
pattern to `tanh`/`sin`/`cos`. -/

/-- The disclosed libm rounding bound for the runtime `atan`. Same status as `real_cos_eps`: the
composite `leanPrims.atan`, through `realToR`, is within a fixed `real_atan_eps` of the exact
`Real.atan`. Un-witnessable in Lean (opaque `Float`); the residual libm trust for this primitive.

**Confirmed unconditional (2026-07-22 audit, not changed)** — same reasoning as `real_sin_eps`:
native `Prims` field, output bounded by `π/2` for every real input, no failure mode requiring a
domain restriction. **Narrowed to finite inputs on 2026-09-14**, for the reason `real_sin_eps` gives: `atan (+∞)` is the
finite `π/2`, and read against `realToR (+∞) ≤ −1`, which the unrestricted neighbours forced, it made this constant at
least about `3π/4`. -/
axiom real_atan_eps : MachLib.Real

axiom real_atan_rounds : ∀ a : Float, a.isFinite = true →
    abs (realToR (stdI1 leanPrims .atan a) - atan (realToR a)) ≤ real_atan_eps

/-- **A sixth grounded transcendental control kernel: `atan(PID law)`.** The emitted C for
`atan(1.5·e + 0.4·i + 0.05·d)` read through `realToR` is within `real_atan_eps + absErr` of the exact
ℝ value `atan(PID law)`, with no domain hypothesis — `atan` is globally Lipschitz, same as `tanh`/`sin`/`cos`.
Instance of `pipeline_tr1_of_arith_finite` at `pidRawEML`.

**Takes `hsafe` since 2026-09-14**: the float side conditions of the kernel's evaluation (`FloatSafe`), which the
restated `real_fpbridge` (`FPBridgeFinite`) needs. Until then this theorem rested on `FPBridge realToR`, which
binary64 does not satisfy. -/
theorem pid_atan_grounded (env : Env)
    (hsafe : FloatSafe realToR (stdI1 leanPrims) (stdI2 leanPrims) env pidRawEML) :
    AbsEnc (real_atan_eps + 1 * absErr realToR env pidRawEML)
      (realToR (evalC (stdR1 leanPrims) (stdR2 leanPrims) env (emitC (tr1OfEML .atan pidRawEML))).toF)
      (atan (exactR realToR env pidRawEML)) :=
  pipeline_tr1_of_arith_finite real_fpbridge (stdI1 leanPrims) (stdI2 leanPrims)
    (stdR1 leanPrims) (stdR2 leanPrims) (std_hrt1 leanPrims) (std_hrt2 leanPrims)
    env .atan atan 1 real_atan_eps
    (le_of_lt zero_lt_one_ax) (fun p q => by rw [one_mul_thm]; exact atan_lipschitz p q)
    pidRawEML isArith_pidRawEML hsafe (real_atan_rounds _ (FloatSafe.add_isFinite hsafe))

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
anything upstream; the weakest possible case for a domain restriction of all fourteen. **Narrowed to finite inputs on
2026-09-14**, for the reason `real_sin_eps` gives, and it had to be before `real_abs_eps_eq_zero` below could be added:
unrestricted, `fabs (+∞) = +∞` read against its neighbours forced this constant to be at least `2`. -/
axiom real_abs_eps : MachLib.Real

axiom real_abs_rounds : ∀ a : Float, a.isFinite = true →
    abs (realToR (stdI1 leanPrims .abs a) - abs (realToR a)) ≤ real_abs_eps

/-- **The runtime `abs` is exact: `real_abs_eps = 0`** (added 2026-09-14, owner-approved). `stdI1 leanPrims .abs` is
`Float.abs`, glibc's `fabs`, which clears the sign bit and changes nothing else (IEEE-754 §5.5.1, a quiet-computational
operation beside `negate` and `copySign`), so a finite float's absolute value is represented exactly and reads back as
the absolute value of its real value. With `real_abs_rounds` this says so, and it is what `LibmBudget`'s `abs_exact`
field asks for. Un-witnessable in Lean (`Float` is opaque); disclosed like `real_fpbridge`.

**Measured before it was added.** `tools/float_bridge/measure.py` computes `fabs` through ctypes, checks it bit for bit
against Lean's own `#eval` of `stdI1 leanPrims .abs`, and compares with the exact absolute value over the same finite
doubles as `real_abs_rounds` (random bit patterns, the subnormals, `±0`, `±DBL_MIN`, `±DBL_MAX`): the largest error is
exactly `0`, and every result is its input with the sign bit cleared. A control asks the same `= 0` of the runtime `sin`
and must fail, and does. The row also fails if `real_abs_rounds` ever again admits a non-finite input, since the two
together then describe no runtime: this file's section "Non-finite inputs" says why. -/
axiom real_abs_eps_eq_zero : real_abs_eps = 0

/-- **A seventh grounded transcendental control kernel: `abs(PID law)`.** The emitted C for
`abs(1.5·e + 0.4·i + 0.05·d)` — a rectified-error variant of the controller — read through `realToR`
is within `real_abs_eps + absErr` of the exact ℝ value `abs(PID law)`, with no domain hypothesis. Instance of
`pipeline_tr1_of_arith_finite` at `pidRawEML`.

**Takes `hsafe` since 2026-09-14**: the float side conditions of the kernel's evaluation (`FloatSafe`), which the
restated `real_fpbridge` (`FPBridgeFinite`) needs. Until then this theorem rested on `FPBridge realToR`, which
binary64 does not satisfy. -/
theorem pid_abs_grounded (env : Env)
    (hsafe : FloatSafe realToR (stdI1 leanPrims) (stdI2 leanPrims) env pidRawEML) :
    AbsEnc (real_abs_eps + 1 * absErr realToR env pidRawEML)
      (realToR (evalC (stdR1 leanPrims) (stdR2 leanPrims) env (emitC (tr1OfEML .abs pidRawEML))).toF)
      (abs (exactR realToR env pidRawEML)) :=
  pipeline_tr1_of_arith_finite real_fpbridge (stdI1 leanPrims) (stdI2 leanPrims)
    (stdR1 leanPrims) (stdR2 leanPrims) (std_hrt1 leanPrims) (std_hrt2 leanPrims)
    env .abs abs 1 real_abs_eps
    (le_of_lt zero_lt_one_ax) (fun p q => by rw [one_mul_thm]; exact abs_abs_sub_le p q)
    pidRawEML isArith_pidRawEML hsafe (real_abs_rounds _ (FloatSafe.add_isFinite hsafe))

/-! ### Grounding an eighth libm primitive: `sqrt`, LOCALLY Lipschitz on a positive domain

Same shape as `log` — one-sided domain, needs `lo > 0`. `L = 1/(√lo+√lo)` via
`SqrtNode.sqrt_lip_local`. All five globally-Lipschitz primitives are done; every primitive from here
needs its own domain/positivity bookkeeping. -/

/-- **The disclosed libm rounding bound for the runtime `sqrt`, domain-restricted.** For any
`0 ≤ hi` and `a : Float` with `0 ≤ realToR a ≤ hi`, `leanPrims.sqrt`, through `realToR`, is within
`u · sqrt hi` of the exact `Real.sqrt` (`sqrt` monotonic and non-negative, so `sqrt (realToR a) ≤
sqrt hi`). **Not claimed unconditionally** (erratum-driven design, 2026-07-22): `Float.sqrt` of a
negative input is `NaN` in IEEE-754, and `realToR (NaN)` is unconstrained. Un-witnessable in Lean
(`Float` opaque); the residual libm trust for this primitive. **Narrowed to finite inputs on 2026-09-14**: `0 ≤ realToR a`
did not exclude `+∞` or a NaN, since `realToR` of either is some unconstrained real; this file's section "Non-finite
inputs" says what that forced. -/
axiom real_sqrt_rounds : ∀ (hi : MachLib.Real) (a : Float), a.isFinite = true → 0 ≤ realToR a → realToR a ≤ hi →
    abs (realToR (stdI1 leanPrims .sqrt a) - sqrt (realToR a)) ≤ u * sqrt hi

/-- **An eighth grounded transcendental control kernel: `sqrt(PID law)`.** For any `[lo,hi]` with
`lo>0` that the PID law's computed AND exact values both land in, the emitted C for
`sqrt(1.5·e + 0.4·i + 0.05·d)` — an RMS/magnitude-style variant — read through `realToR`, is within
`u·sqrt hi + (1/(√lo+√lo))·absErr` of the exact ℝ value `sqrt(PID law)`. Instance of
`pipeline_sqrt_of_arith_finite` at `pidRawEML`.

**Takes `hsafe` since 2026-09-14**: the float side conditions of the kernel's evaluation (`FloatSafe`), which the
restated `real_fpbridge` (`FPBridgeFinite`) needs. Until then this theorem rested on `FPBridge realToR`, which
binary64 does not satisfy. -/
theorem pid_sqrt_grounded (env : Env) (lo hi : MachLib.Real) (hlo : 0 < lo)
    (hsafe : FloatSafe realToR (stdI1 leanPrims) (stdI2 leanPrims) env pidRawEML)
    (hflx_lo : lo ≤ realToR (evalEML (stdI1 leanPrims) (stdI2 leanPrims) env pidRawEML).toF)
    (hflx_hi : realToR (evalEML (stdI1 leanPrims) (stdI2 leanPrims) env pidRawEML).toF ≤ hi)
    (hxe_lo : lo ≤ exactR realToR env pidRawEML) (hxe_hi : exactR realToR env pidRawEML ≤ hi) :
    AbsEnc (u * sqrt hi + (1 / (sqrt lo + sqrt lo)) * absErr realToR env pidRawEML)
      (realToR (evalC (stdR1 leanPrims) (stdR2 leanPrims) env (emitC (tr1OfEML .sqrt pidRawEML))).toF)
      (sqrt (exactR realToR env pidRawEML)) :=
  pipeline_sqrt_of_arith_finite real_fpbridge (stdI1 leanPrims) (stdI2 leanPrims)
    (stdR1 leanPrims) (stdR2 leanPrims) (std_hrt1 leanPrims) (std_hrt2 leanPrims)
    env .sqrt lo hi (u * sqrt hi) hlo pidRawEML isArith_pidRawEML hsafe
    hflx_lo hflx_hi hxe_lo hxe_hi
    (real_sqrt_rounds hi _ (FloatSafe.add_isFinite hsafe) (le_of_lt (lt_of_lt_of_le hlo hflx_lo)) hflx_hi)

/-! ### Grounding a ninth libm primitive: `log10`, LOCALLY Lipschitz on a positive domain

Same shape as `log`/`sqrt` — one-sided domain, `lo > 0`, `L = 1/(lo·log 10)`. Until 2026-09-13
`leanPrims`'s interpretation of `.log10` was a composite built from `ln` (`fun x => p.ln x / p.ln 10`); it is
now the `Prims` field `log10`, libm's `log10`, because that is the call emitted C makes
(`EMLToCRuntime.lean`, `stdI1`). -/

/-- **The disclosed libm rounding bound for the runtime `log10`, domain-restricted.** For any finite `a` and
`0 < lo ≤ realToR a ≤ hi`, `leanPrims.log10`, through `realToR`, is within `3u · (abs (log10 lo) + abs (log10 hi))`
of the exact `Real.log10` — the same two-sided shape as `real_log_rounds`. Since 2026-09-13 the runtime `log10` is
libm `log10`, not `ln x / ln 10` (`EMLToCRuntime.lean`: emitted C calls libm `log10`). Un-witnessable in Lean
(`Float` opaque); the residual libm trust for this primitive.

**Restated 2026-09-14 from a measurement, because the statement before it was false.** It read
`∀ (lo hi : MachLib.Real) (a : Float), 0 < lo → lo ≤ realToR a → realToR a ≤ hi → … ≤ u * (abs (log10 lo) +
abs (log10 hi))`. glibc's `log10` is not correctly rounded, so `u · |log10 x|`, the tightest `lo`/`hi`, fails on
ordinary inputs, most often near `x = 1`; and nothing excluded an input `+∞` or NaN. glibc 2.39's `log10`
(`sysdeps/ieee754/dbl-64/e_log10.c`, from fdlibm) computes `n·log10_2hi + (n·log10_2lo + ivln10·log x')` with `x'`
in `[0.5, 2)`. For `x` itself in `[0.5, 2)`, `n = 0` and the result is `ivln10·log x` rounded once: `ivln10`'s own
error is `0.198` ulp (about `0.23u`), glibc's `log` at most `0.52` ulp (about `1.04u`), and the product's rounding
`u`, about `2.27u` in all. Otherwise the two parts share a sign, so nothing cancels; the inner and the final sum
each round once more, and the worst case, `|n| = 1` with `|log10 x'| = log10 2`, is about `2.63u`.
`tools/float_bridge/measure.py` over 644 015 inputs (log-spaced over the whole range, `[0.5, 2)` densely, 20 000
doubles on each side of `1`, powers of ten and of two, and `10^(±2ʲ)`, where the result is just above a power of
two): the old statement fails at 42 194 of 644 003. The restated one holds at all 644 003, at most `0.692` of `3u`
(`2.076u`, at `x = 1.0000005489792292`). `3u` is above the analysis bound and about half again the measured
maximum. `tools/float_bridge/registry.json` pins these numbers and keeps the old statement as a control. -/
axiom real_log10_rounds : ∀ (lo hi : MachLib.Real) (a : Float), a.isFinite = true →
    0 < lo → lo ≤ realToR a → realToR a ≤ hi →
    abs (realToR (stdI1 leanPrims .log10 a) - log10 (realToR a))
      ≤ (u + u + u) * (abs (log10 lo) + abs (log10 hi))

/-- **A ninth grounded transcendental control kernel: `log10(PID law)`.** For any `[lo,hi]` with `lo>0` that the
PID law's computed AND exact values both land in, the emitted C for `log10(1.5·e + 0.4·i + 0.05·d)` — a
decibel-scaled gain variant — read through `realToR`, is within `3u·(abs(log10 lo)+abs(log10 hi)) +
(1/(lo·log 10))·absErr` of the exact ℝ value `log10(PID law)`, given `hsafe` (the PID law's float side conditions,
`FloatSafe`). Since 2026-09-14 the rounding constant is `3u` where it was `u`, `hsafe` is a hypothesis, and
`real_log10_rounds`'s new finite-input condition comes from it (`FloatSafe.add_isFinite`). Instance of
`pipeline_log10_of_arith_finite` at `pidRawEML`. -/
theorem pid_log10_grounded (env : Env) (lo hi : MachLib.Real) (hlo : 0 < lo)
    (hsafe : FloatSafe realToR (stdI1 leanPrims) (stdI2 leanPrims) env pidRawEML)
    (hflx_lo : lo ≤ realToR (evalEML (stdI1 leanPrims) (stdI2 leanPrims) env pidRawEML).toF)
    (hflx_hi : realToR (evalEML (stdI1 leanPrims) (stdI2 leanPrims) env pidRawEML).toF ≤ hi)
    (hxe_lo : lo ≤ exactR realToR env pidRawEML) (hxe_hi : exactR realToR env pidRawEML ≤ hi) :
    AbsEnc ((u + u + u) * (abs (log10 lo) + abs (log10 hi))
        + (1 / (lo * log (natCast 10))) * absErr realToR env pidRawEML)
      (realToR (evalC (stdR1 leanPrims) (stdR2 leanPrims) env (emitC (tr1OfEML .log10 pidRawEML))).toF)
      (log10 (exactR realToR env pidRawEML)) :=
  pipeline_log10_of_arith_finite real_fpbridge (stdI1 leanPrims) (stdI2 leanPrims)
    (stdR1 leanPrims) (stdR2 leanPrims) (std_hrt1 leanPrims) (std_hrt2 leanPrims)
    env .log10 lo hi ((u + u + u) * (abs (log10 lo) + abs (log10 hi))) hlo pidRawEML isArith_pidRawEML hsafe
    hflx_lo hflx_hi hxe_lo hxe_hi
    (real_log10_rounds lo hi _ (FloatSafe.add_isFinite hsafe) hlo hflx_lo hflx_hi)

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
this primitive. **Narrowed to finite inputs on 2026-09-14**: `abs (realToR a) ≤ R < 1` did not exclude `±∞` or a NaN,
whose `realToR` is some unconstrained real; this file's section "Non-finite inputs" says what that forced. -/
axiom real_asin_rounds : ∀ (R : MachLib.Real) (a : Float), a.isFinite = true → R < 1 → abs (realToR a) ≤ R →
    abs (realToR (stdI1 leanPrims .asin a) - arcsin (realToR a)) ≤ u * (pi / (1 + 1))

/-- **A tenth grounded transcendental control kernel: `asin(PID law)`.** For any `[-R,R]` (`R<1`) that
the PID law's computed AND exact values both land in, the emitted C for
`asin(1.5·e + 0.4·i + 0.05·d)` read through `realToR`, is within `u·(pi/2) + (1/√(1−R²))·absErr` of
the exact ℝ value `arcsin(PID law)`. Instance of `pipeline_arcsin_of_arith_finite` at `pidRawEML`.

**Takes `hsafe` since 2026-09-14**: the float side conditions of the kernel's evaluation (`FloatSafe`), which the
restated `real_fpbridge` (`FPBridgeFinite`) needs. Until then this theorem rested on `FPBridge realToR`, which
binary64 does not satisfy. -/
theorem pid_asin_grounded (env : Env) (R : MachLib.Real) (hR : R < 1)
    (hsafe : FloatSafe realToR (stdI1 leanPrims) (stdI2 leanPrims) env pidRawEML)
    (hflx_lo : -R ≤ realToR (evalEML (stdI1 leanPrims) (stdI2 leanPrims) env pidRawEML).toF)
    (hflx_hi : realToR (evalEML (stdI1 leanPrims) (stdI2 leanPrims) env pidRawEML).toF ≤ R)
    (hxe_lo : -R ≤ exactR realToR env pidRawEML) (hxe_hi : exactR realToR env pidRawEML ≤ R) :
    AbsEnc (u * (pi / (1 + 1)) + (1 / sqrt (1 - R * R)) * absErr realToR env pidRawEML)
      (realToR (evalC (stdR1 leanPrims) (stdR2 leanPrims) env (emitC (tr1OfEML .asin pidRawEML))).toF)
      (arcsin (exactR realToR env pidRawEML)) :=
  pipeline_arcsin_of_arith_finite real_fpbridge (stdI1 leanPrims) (stdI2 leanPrims)
    (stdR1 leanPrims) (stdR2 leanPrims) (std_hrt1 leanPrims) (std_hrt2 leanPrims)
    env .asin R (u * (pi / (1 + 1))) hR pidRawEML isArith_pidRawEML hsafe
    hflx_lo hflx_hi hxe_lo hxe_hi
    (real_asin_rounds R _ (FloatSafe.add_isFinite hsafe) hR (abs_le_iff.mpr ⟨hflx_lo, hflx_hi⟩))

/-! ### Grounding an eleventh libm primitive: `acos` (`arccos`), same symmetric-domain shape as `asin`
-/

/-- **The disclosed libm rounding bound for the runtime `acos`, domain-restricted.** For any `R < 1`
and `a : Float` with `abs (realToR a) ≤ R`, `leanPrims.acos`, through `realToR`, is within `u · pi` of
the exact `Real.arccos` — CONSTANT (`arccos`'s output is always in `[0,π]`), same shape as
`real_asin_rounds` (including the same `R < 1` fix). **Not claimed unconditionally** (erratum-driven
design, 2026-07-22): same out-of-domain `NaN` risk as `asin`. Un-witnessable in Lean (`Float`
opaque); the residual libm trust for this primitive. **Narrowed to finite inputs on 2026-09-14**, as `real_asin_rounds`
was: at `+∞` the two send the same NaN, and their bounds against `arcsin` and `arccos` are what pinned `realToR (+∞)`. -/
axiom real_acos_rounds : ∀ (R : MachLib.Real) (a : Float), a.isFinite = true → R < 1 → abs (realToR a) ≤ R →
    abs (realToR (stdI1 leanPrims .acos a) - arccos (realToR a)) ≤ u * pi

/-- **An eleventh grounded transcendental control kernel: `acos(PID law)`.** Same shape as
`pid_asin_grounded`. Instance of `pipeline_arccos_of_arith_finite` at `pidRawEML`.

**Takes `hsafe` since 2026-09-14**: the float side conditions of the kernel's evaluation (`FloatSafe`), which the
restated `real_fpbridge` (`FPBridgeFinite`) needs. Until then this theorem rested on `FPBridge realToR`, which
binary64 does not satisfy. -/
theorem pid_acos_grounded (env : Env) (R : MachLib.Real) (hR : R < 1)
    (hsafe : FloatSafe realToR (stdI1 leanPrims) (stdI2 leanPrims) env pidRawEML)
    (hflx_lo : -R ≤ realToR (evalEML (stdI1 leanPrims) (stdI2 leanPrims) env pidRawEML).toF)
    (hflx_hi : realToR (evalEML (stdI1 leanPrims) (stdI2 leanPrims) env pidRawEML).toF ≤ R)
    (hxe_lo : -R ≤ exactR realToR env pidRawEML) (hxe_hi : exactR realToR env pidRawEML ≤ R) :
    AbsEnc (u * pi + (1 / sqrt (1 - R * R)) * absErr realToR env pidRawEML)
      (realToR (evalC (stdR1 leanPrims) (stdR2 leanPrims) env (emitC (tr1OfEML .acos pidRawEML))).toF)
      (arccos (exactR realToR env pidRawEML)) :=
  pipeline_arccos_of_arith_finite real_fpbridge (stdI1 leanPrims) (stdI2 leanPrims)
    (stdR1 leanPrims) (stdR2 leanPrims) (std_hrt1 leanPrims) (std_hrt2 leanPrims)
    env .acos R (u * pi) hR pidRawEML isArith_pidRawEML hsafe
    hflx_lo hflx_hi hxe_lo hxe_hi
    (real_acos_rounds R _ (FloatSafe.add_isFinite hsafe) hR (abs_le_iff.mpr ⟨hflx_lo, hflx_hi⟩))

/-! ### Grounding a twelfth libm primitive: `sinh`, SYMMETRIC domain, unconditional on `R`

`sinh` needs a domain (unlike globally-Lipschitz `tanh`) but, like `exp`, no extra sign hypothesis:
`L = cosh R > 0` for every `R`. `stdI1 leanPrims .sinh` is itself a composite of `expm1` and `exp`, not a
distinct native call (`EMLToCRuntime.lean`; `real_sinh_rounds` below lists its branches). -/

/-- **The disclosed libm rounding bound for the runtime `sinh`, domain-restricted.** For any `R` and `a : Float` with
`abs (realToR a) ≤ R` whose float `sinh` is finite, `leanPrims.sinh`, through `realToR`, is within `4u · cosh R` of
the exact `Real.sinh`, with `cosh R` as the magnitude bound (`abs (sinh x) ≤ cosh x ≤ cosh R`), the SAME quantity
`pid_sinh_grounded` uses as its Lipschitz constant. `stdI1 leanPrims .sinh` is a composite of `expm1` and `exp`
(`EMLToCRuntime.lean`): `x` itself for `|x| ≤ 2.149119332890821e-8` (forge's `MG_SINH_X_MAX`, since 2026-09-14); with
`a = |x|` and `t = expm1 a`, `½(2t − t·t/(t+1))` below `1` and `½(t + t/(t+1))` below `22` (since 2026-09-15; the exp
difference `(eᵃ − e⁻ᵃ)·½` until then, which cancelled below `1`), `½·exp a` up to `709.78`, `(½·w)·w` with
`w = exp(a/2)` above that; then `x`'s sign. Un-witnessable in Lean (`Float` opaque); the residual libm trust for this
primitive.

**Restated 2026-09-14 from a measurement, because the statement before it was false.** It read
`∀ (R : MachLib.Real) (a : Float), abs (realToR a) ≤ R → … ≤ u * cosh R`. Each branch rounds more than once:
in `(eᵃ ∓ e⁻ᵃ)·½` the two `exp` errors and the sum or difference add up to
about `2.02u · cosh x`, and in `(½·w)·w` the `exp` error counts twice before the product rounds, about `3.04u`,
taking glibc's `exp` bound of about `0.509` ulp (`real_exp_rounds` says where that comes from). A result that
overflows, from `|x| = 710.4758` on, has no real value to be near, and `R` excluded none.
`tools/float_bridge/measure.py` over 776 071 inputs (dense on `[−712, 712]`, the large branch densely, doubles
packed at `709.78`, `710.4758` and the small-argument threshold, and doubles whose result lies just above `2ᵏ`):
the old statement fails at 63 940 of 750 768. The restated one holds at all 750 768 its hypothesis admits (25 303
non-finite results excluded), at most `0.744` of `4u` (`2.975u`, at `x = 709.7844159037164`). `4u` is above the
analysis bound and a third above the measured maximum. `tools/float_bridge/registry.json` pins these numbers and
keeps the old statement as a control. **Re-measured 2026-09-15 on the `expm1` body**, with both sides of its splits at
`1` and `22` and the points where `t` crosses a power of two added: 793 526 inputs; all 768 223 its hypothesis admits
hold, at most `0.744` of `4u`, still at `x = 709.7844159037164` in the large branch, which that change left alone; the old
statement fails at 65 329 of them. -/
axiom real_sinh_rounds : ∀ (R : MachLib.Real) (a : Float), (stdI1 leanPrims .sinh a).isFinite = true →
    abs (realToR a) ≤ R → abs (realToR (stdI1 leanPrims .sinh a) - sinh (realToR a)) ≤ (u + u + u + u) * cosh R

/-- **A twelfth grounded transcendental control kernel: `sinh(PID law)`.** For any `[-R,R]` that the PID law's
computed AND exact values both land in, the emitted C for `sinh(1.5·e + 0.4·i + 0.05·d)` read through `realToR`, is
within `4u · cosh R + cosh R · absErr` of the exact ℝ value `sinh(PID law)`, given `hsafe` (the PID law's float side
conditions, `FloatSafe`) and `hsinh` (the runtime `sinh` of it is a finite float). Both hypotheses, and the
constant `4u` where it was `u`, date from 2026-09-14, when `real_fpbridge` and `real_sinh_rounds` were restated from
a measurement. Instance of `pipeline_sinh_of_arith_finite` at `pidRawEML`. -/
theorem pid_sinh_grounded (env : Env) (R : MachLib.Real)
    (hsafe : FloatSafe realToR (stdI1 leanPrims) (stdI2 leanPrims) env pidRawEML)
    (hsinh : (stdI1 leanPrims .sinh (evalEML (stdI1 leanPrims) (stdI2 leanPrims) env pidRawEML).toF).isFinite = true)
    (hflx_lo : -R ≤ realToR (evalEML (stdI1 leanPrims) (stdI2 leanPrims) env pidRawEML).toF)
    (hflx_hi : realToR (evalEML (stdI1 leanPrims) (stdI2 leanPrims) env pidRawEML).toF ≤ R)
    (hxe_lo : -R ≤ exactR realToR env pidRawEML) (hxe_hi : exactR realToR env pidRawEML ≤ R) :
    AbsEnc ((u + u + u + u) * cosh R + cosh R * absErr realToR env pidRawEML)
      (realToR (evalC (stdR1 leanPrims) (stdR2 leanPrims) env (emitC (tr1OfEML .sinh pidRawEML))).toF)
      (sinh (exactR realToR env pidRawEML)) :=
  pipeline_sinh_of_arith_finite real_fpbridge (stdI1 leanPrims) (stdI2 leanPrims)
    (stdR1 leanPrims) (stdR2 leanPrims) (std_hrt1 leanPrims) (std_hrt2 leanPrims)
    env .sinh R ((u + u + u + u) * cosh R) pidRawEML isArith_pidRawEML hsafe
    hflx_lo hflx_hi hxe_lo hxe_hi
    (real_sinh_rounds R _ hsinh (abs_le_iff.mpr ⟨hflx_lo, hflx_hi⟩))

/-! ### Grounding a thirteenth libm primitive: `cosh`, SYMMETRIC domain, needs `0 ≤ R`

The `cosh`/`log` analog of `sinh`/`exp`: `L = sinh R` needs `R ≥ 0` on top of the plain range bounds
(`sinh R ≥ 0` only holds for `R ≥ 0`) — one further honest cost layered on the symmetric-domain case,
mirroring how `log` layers positivity on top of `exp`'s plain one-sided domain. THIRTEENTH grounded
primitive — every `Trans1` constructor except `tan` is now grounded. -/

/-- **The disclosed libm rounding bound for the runtime `cosh`, domain-restricted.** For any `R` and `a : Float` with
`abs (realToR a) ≤ R` whose float `cosh` is finite, `leanPrims.cosh`, through `realToR`, is within `4u · cosh R` of
the exact `Real.cosh` (`cosh` is monotone in `abs ·`, so `cosh x ≤ cosh R`), the SAME `cosh R`/`sinh R` shape
`pid_cosh_grounded` needs. `stdI1 leanPrims .cosh` is `(eᵃ + e⁻ᵃ)·½` for `a = |x| ≤ 709.78` and `(½·w)·w` with
`w = exp(a/2)` above (`EMLToCRuntime.lean`). Un-witnessable in Lean (`Float` opaque); the residual libm trust for
this primitive.

**Restated 2026-09-14 from a measurement, because the statement before it was false.** It read
`∀ (R : MachLib.Real) (a : Float), abs (realToR a) ≤ R → … ≤ u * cosh R`. Each branch rounds more than once:
in `(eᵃ ∓ e⁻ᵃ)·½` the two `exp` errors and the sum or difference add up to
about `2.02u · cosh x`, and in `(½·w)·w` the `exp` error counts twice before the product rounds, about `3.04u`,
taking glibc's `exp` bound of about `0.509` ulp (`real_exp_rounds` says where that comes from). A result that
overflows, from `|x| = 710.4758` on, has no real value to be near, and `R` excluded none.
`tools/float_bridge/measure.py` over the same 776 071 inputs as `real_sinh_rounds`: the old statement fails at
86 920 of 750 768, in both branches. The restated one holds at all 750 768 its hypothesis admits (25 303 non-finite
results excluded), at most `0.744` of `4u` (`2.975u`, at `x = 709.7844159037164`). `tools/float_bridge/registry.json`
pins these numbers and keeps the old statement as a control. -/
axiom real_cosh_rounds : ∀ (R : MachLib.Real) (a : Float), (stdI1 leanPrims .cosh a).isFinite = true →
    abs (realToR a) ≤ R → abs (realToR (stdI1 leanPrims .cosh a) - cosh (realToR a)) ≤ (u + u + u + u) * cosh R

/-- **A thirteenth grounded transcendental control kernel: `cosh(PID law)`** — the last one before `tan`. Within
`4u · cosh R + sinh R · absErr`, given `hsafe` (the PID law's float side conditions) and `hcosh` (the runtime `cosh`
of it is finite). Both hypotheses, and the constant `4u` where it was `u`, date from 2026-09-14. Instance of
`pipeline_cosh_of_arith_finite` at `pidRawEML`. -/
theorem pid_cosh_grounded (env : Env) (R : MachLib.Real) (hR0 : 0 ≤ R)
    (hsafe : FloatSafe realToR (stdI1 leanPrims) (stdI2 leanPrims) env pidRawEML)
    (hcosh : (stdI1 leanPrims .cosh (evalEML (stdI1 leanPrims) (stdI2 leanPrims) env pidRawEML).toF).isFinite = true)
    (hflx_lo : -R ≤ realToR (evalEML (stdI1 leanPrims) (stdI2 leanPrims) env pidRawEML).toF)
    (hflx_hi : realToR (evalEML (stdI1 leanPrims) (stdI2 leanPrims) env pidRawEML).toF ≤ R)
    (hxe_lo : -R ≤ exactR realToR env pidRawEML) (hxe_hi : exactR realToR env pidRawEML ≤ R) :
    AbsEnc ((u + u + u + u) * cosh R + sinh R * absErr realToR env pidRawEML)
      (realToR (evalC (stdR1 leanPrims) (stdR2 leanPrims) env (emitC (tr1OfEML .cosh pidRawEML))).toF)
      (cosh (exactR realToR env pidRawEML)) :=
  pipeline_cosh_of_arith_finite real_fpbridge (stdI1 leanPrims) (stdI2 leanPrims)
    (stdR1 leanPrims) (stdR2 leanPrims) (std_hrt1 leanPrims) (std_hrt2 leanPrims)
    env .cosh R ((u + u + u + u) * cosh R) hR0 pidRawEML isArith_pidRawEML hsafe
    hflx_lo hflx_hi hxe_lo hxe_hi
    (real_cosh_rounds R _ hcosh (abs_le_iff.mpr ⟨hflx_lo, hflx_hi⟩))

/-! ### Grounding the fourteenth and LAST libm primitive: `tan`

The one primitive needing genuinely new math (`TanLipschitz.lean`, one new axiom
`sin_pos_of_pos_lt_pi_div_two`, user-approved). Symmetric domain `[-R,R]`, `R < π/2`, `R ≥ 0`
(the `cosh`-shaped extra hypothesis), `L = 1/cos²R`. Completes every `Trans1` constructor. -/

/-- **The disclosed libm rounding bound for the runtime `tan`, domain-restricted.** For any finite `a` and
`0 ≤ R < π/2` with `abs (realToR a) ≤ R`, `leanPrims.tan`, through `realToR`, is within `2u · tan R` of the exact
`Real.tan` (`tan` is odd and increasing on `[0,π/2)`, so `abs (tan x) ≤ tan R`), the SAME `R` `pid_tan_grounded`
carries. `tan` has poles at `±π/2 + kπ`, so no `R`-independent bound holds. Un-witnessable in Lean (`Float`
opaque); the residual libm trust for this primitive.

**Restated 2026-09-14 from a measurement, because the statement before it was false.** It read
`∀ (R : MachLib.Real) (a : Float), 0 ≤ R → R < pi / (1 + 1) → abs (realToR a) ≤ R → … ≤ u * tan R`. glibc's `tan` is
not correctly rounded: its source (glibc 2.39 `sysdeps/ieee754/dbl-64/s_tan.c`) reports a maximum error of about
`0.62` ulp from random sampling, up to about `1.24u` relative to a result just above a power of two. Nothing
excluded an input `±∞` or NaN either. `tools/float_bridge/measure.py` over 560 284 inputs (dense on `(−π/2, π/2)`,
doubles packed at `±π/2` and geometrically close to `π/2`, and doubles whose result lies just above `2ᵏ`): the
old statement fails at 138 of 550 203. The restated one holds at all 550 203, at most `0.521` of `2u` (`1.0426u`, at
`x = 1.5095155244315357`). `2u` is above the sampled bound and almost twice the measured maximum.
`tools/float_bridge/registry.json` pins these numbers and keeps the old statement as a control. -/
axiom real_tan_rounds : ∀ (R : MachLib.Real) (a : Float), a.isFinite = true → 0 ≤ R → R < pi / (1 + 1) →
    abs (realToR a) ≤ R → abs (realToR (stdI1 leanPrims .tan a) - tan (realToR a)) ≤ (u + u) * tan R

/-- **The fourteenth and last grounded transcendental control kernel: `tan(PID law)`.** For any `[-R,R]`
(`R<π/2`, `R≥0`) that the PID law's computed AND exact values both land in, the emitted C for
`tan(1.5·e + 0.4·i + 0.05·d)` read through `realToR`, is within `2u·tan R + (1/cos²R)·absErr` of the exact ℝ value
`tan(PID law)`, given `hsafe`. Since 2026-09-14 the rounding constant is `2u` where it was `u`, `hsafe` is a
hypothesis, and `real_tan_rounds`'s new finite-input condition comes from it. Instance of
`pipeline_tan_of_arith_finite` at `pidRawEML`. Every `Trans1` constructor is now grounded. -/
theorem pid_tan_grounded (env : Env) (R : MachLib.Real) (hR0 : 0 ≤ R) (hR : R < pi / (1 + 1))
    (hsafe : FloatSafe realToR (stdI1 leanPrims) (stdI2 leanPrims) env pidRawEML)
    (hflx_lo : -R ≤ realToR (evalEML (stdI1 leanPrims) (stdI2 leanPrims) env pidRawEML).toF)
    (hflx_hi : realToR (evalEML (stdI1 leanPrims) (stdI2 leanPrims) env pidRawEML).toF ≤ R)
    (hxe_lo : -R ≤ exactR realToR env pidRawEML) (hxe_hi : exactR realToR env pidRawEML ≤ R) :
    AbsEnc ((u + u) * tan R + (1 / (cos R * cos R)) * absErr realToR env pidRawEML)
      (realToR (evalC (stdR1 leanPrims) (stdR2 leanPrims) env (emitC (tr1OfEML .tan pidRawEML))).toF)
      (tan (exactR realToR env pidRawEML)) :=
  pipeline_tan_of_arith_finite real_fpbridge (stdI1 leanPrims) (stdI2 leanPrims)
    (stdR1 leanPrims) (stdR2 leanPrims) (std_hrt1 leanPrims) (std_hrt2 leanPrims)
    env .tan R ((u + u) * tan R) hR0 hR pidRawEML isArith_pidRawEML hsafe
    hflx_lo hflx_hi hxe_lo hxe_hi
    (real_tan_rounds R _ (FloatSafe.add_isFinite hsafe) hR0 hR (abs_le_iff.mpr ⟨hflx_lo, hflx_hi⟩))

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
`pipeline_nested_local_finite` at `pidRawEML`, going through `isFoldLocal_of_isArith` to lift the arithmetic
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
`hround_all`, no `realOfAll14`.

**Since 2026-09-14** it also takes `hsafe` (the PID law's float side conditions) and `hcosh` (the runtime `cosh` of
it is finite), which the restated `real_fpbridge` and `real_cosh_rounds` need, and the inner `cosh` rounds at `4u`.
The bound is existential, so the conclusion reads as before. -/
theorem pid_log_cosh_grounded (env : Env) (R lo hi : MachLib.Real) (hR0 : 0 ≤ R) (hlo : 0 < lo)
    (hsafe : FloatSafe realToR (stdI1 leanPrims) (stdI2 leanPrims) env pidRawEML)
    (hcosh : (stdI1 leanPrims .cosh (evalEML (stdI1 leanPrims) (stdI2 leanPrims) env pidRawEML).toF).isFinite = true)
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
    .tr1 .ln _ (1 / lo) lo hi ((u + u) * (abs (log lo) + abs (log hi)))
      (le_of_lt (one_div_pos_of_pos hlo)) (log_lip_local lo hi hlo)
      hflx_lo2 hflx_hi2 hxe_lo2 hxe_hi2 (real_log_rounds lo hi _ hcosh hlo hflx_lo2 hflx_hi2)
      (.tr1 .cosh _ (sinh R) (-R) R ((u + u + u + u) * cosh R) (sinh_nonneg hR0) (cosh_lip_local R)
        hflx_lo1 hflx_hi1 hxe_lo1' hxe_hi1'
        (real_cosh_rounds R _ hcosh (abs_le_iff.mpr ⟨hflx_lo1, hflx_hi1⟩))
        (isFoldLocal_of_isArith (stdI1 leanPrims) (stdI2 leanPrims) realOfLogCosh env
          isArith_pidRawEML))
  obtain ⟨E, hE⟩ := pipeline_nested_local_finite real_fpbridge realOfLogCosh
    (stdI1 leanPrims) (stdI2 leanPrims) (stdR1 leanPrims) (stdR2 leanPrims)
    (std_hrt1 leanPrims) (std_hrt2 leanPrims) env
    (.tr1 .ln (.tr1 .cosh pidRawEML)) he (.tr1 _ _ (.tr1 _ _ hsafe))
  refine ⟨E, ?_⟩
  have heq : exactRn realToR realOfLogCosh env (.tr1 .ln (.tr1 .cosh pidRawEML))
      = log (cosh (exactR realToR env pidRawEML)) := by
    show log (cosh (exactRn realToR realOfLogCosh env pidRawEML))
      = log (cosh (exactR realToR env pidRawEML))
    rw [exactRn_eq_exactR_of_arith realOfLogCosh env isArith_pidRawEML]
  rwa [heq] at hE

end Certcom
