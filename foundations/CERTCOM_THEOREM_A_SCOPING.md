# certcom Theorem A — scoping the rounding frontier (2026-07-10)

A decomposition pass on the EML→C correctness stack, to find the **smallest honest next theorem**.
Everything below was verified by `#print axioms` on the real artifact, not read off docstrings.

## Headline finding

The rounding/accumulation model is **not unbuilt — it is proved, sorryAx-free, cancellation
included.** The frontier is not "build the forward-error model." It is **grounding** it: the entire
tower is proved `∀ toR, FPBridge toR → …`, and `FPBridge` (the standard model of floating-point) is
inhabited only by the degenerate `toR = fun _ => 0`. The smallest honest step is to name + register
the `FPBridge` grounding and instantiate the already-proved tower on a real kernel.

## What's proved (verified `#print axioms`, all sorryAx-free)

| Layer | Certificate | Footprint |
|---|---|---|
| **T1** translation validation | `Certcom.runProg_correct` (EMLToC) | emitted C ≡ EML source through calls/while/state |
| **T2** runtime discharge | `Certcom.runProg_correct_std` (EMLToCRuntime) | `[propext, Quot.sound]` — exact Float, no rounding; `mg_*` reduced to a shared primitive basis |
| **T3** composite error | `cosh/eml_fwd_reduces_to_*` (CompositeRuntimeError) | composites inherit ULP error from primitives |
| **Fold: arithmetic** | `Certcom.pipeline_arith` (AbsoluteFold) | **every** lit/var/+/−/× tree, **cancellation included, no sign hypothesis** |
| **Fold: cancelling kernel** | `Certcom.pipeline_det` (AbsoluteBridge) | the 2×2 determinant `x·y − z·w` |
| **Fold: log/sqrt** | `Certcom.pipeline_pos_over_arith` (AbsoluteFoldPos) | one-sided domain, positive-lower-bound hypothesis |
| **Fold: local transcendental** | `pipeline_{exp,log}_of_arith` (AbsoluteFoldLocal) | one exp/log layer over arithmetic |
| **Fold: nested glob-Lipschitz** | `pipeline_nested_glob/std` (CertifyNested) | fully recursive sin/cos/tanh/atan/abs |
| **Float↔Real interface** | `FPBridge` + `length_sq2_bridge` (FloatRealBridge) | the bridge + a worked `x²+y²` end-to-end certificate |

All fold certificates rest on: the `MachLib.Real` field/order axioms (witnessed against ℝ by
Theorem B / the axiom-ledger), the roundoff constants `u`/`u_nonneg`/`u_le_one`, and — as a
**discharged hypothesis, not an axiom** — `FPBridge toR`.

> **Stale docstring flagged:** `FloatRealBridge.lean`'s header still calls general cancelling
> accumulation "the remaining CompCert-scale T3 work, not claimed here." `AbsoluteFold.pipeline_arith`
> has since closed exactly that for the arithmetic fragment (cancellation included, sorryAx-free).
> Update that header when next in the file.

## The trust base — where it actually bottoms out

`FPBridge toR` (FloatRealBridge.lean) is the keystone:

```lean
structure FPBridge (toR : Float → MachLib.Real) : Prop where
  add : ∀ a b : Float, RoundsW u (toR (a + b)) (toR a + toR b)   -- correctly rounded, rel err ≤ u
  sub : ∀ a b : Float, RoundsW u (toR (a - b)) (toR a - toR b)
  mul : ∀ a b : Float, RoundsW u (toR (a * b)) (toR a * toR b)
  neg : ∀ a : Float, toR (-a) = -(toR a)                          -- IEEE neg is EXACT
```

Its **only inhabitant is the consistency witness** `example : FPBridge (fun _ => 0)`. No faithful
`toR : Float → Real` (the value a double denotes) is inhabited. Lean's `Float` is opaque/`@[extern]`,
so `FPBridge` for the real `toR` **cannot be proved inside Lean** — it is the IEEE-754 standard model,
and must be a hypothesis or a disclosed axiom. This is the precise, honest location of the
"measured, not proved" boundary from the blog.

## The honest open pieces (ranked)

1. **[Keystone] Ground `FPBridge` for a faithful `toR`.** Makes the whole proved tower bite on real
   floats. Two routes:
   - *(hard, Flocq-scale)* formalize binary64 with in-Lean rounding semantics and **prove**
     `FPBridge` — multi-month; needs an FP formalization Lean/Mathlib lacks.
   - *(bounded, honest)* name `realToR : Float → Real` + `real_fpbridge : FPBridge realToR` as a
     single **disclosed axiom** — the standard model, same trust status as `erf` (declared,
     un-witnessable because `Float` is opaque). Then instantiate the proved tower at `realToR`.
2. **[Small proof win] the `neg` node in the closed-form `absErr` fold.** `FPBridge` already carries
   the exact-`neg` field; wiring it into `AbsoluteFold` closes the arithmetic fragment fully (it is
   currently +/−/× ; unary neg is the one missing node). Pure Lean, additive.
3. **[Medium] `tr1`/`tr2` nodes in the closed-form (`absErr`) fold.** The existential-`E`
   `AbsoluteFoldNest` already does glob-Lipschitz `tr1`; port it to the closed-form fold.
4. **[Hard, named] full recursive local-Lipschitz nesting** (exp/log of subtrees that themselves
   contain local transcendentals) — needs interval arithmetic with directed rounding (range and
   error co-propagated). The genuinely-harder piece, named in `AbsoluteFoldLocal`'s scope note.
5. **[Deep] libm primitive grounding** — the `RoundsW u (toR (mg_f x)) (Real.f (toR x))` specs for
   exp/log/sin/… (the 11 libm calls, the "irreducible trust"). Same status as `FPBridge`.

## ✅ Update (2026-07-10) — keystone executed

The recommended keystone below is **done** (`MachLib/FPGrounding.lean`):
`Certcom.realToR` + `Certcom.real_fpbridge` (the disclosed IEEE-754 axioms) + the theorem
`Certcom.pipeline_det_grounded` — an **unconditional** forward-error certificate on the actual
emitted-C determinant `x·y − z·w`, `#print axioms` resting on exactly `{realToR, real_fpbridge, the
ℝ-witnessed MachLib.Real axioms, u, u_nonneg}`, no `FPBridge` hypothesis, no `sorryAx`. Registered in
`AxiomLedger` under a new `disclosedTrusted` category (distinct from the inert `disclosedUnwitnessed`):
254 axioms pinned, 5 headline footprints ⊆ trusted (66), and a dead-disclosure check confirms the two
axioms are load-bearing in the Theorem-A headline. Next: `tr1` nodes in the closed-form fold, or a
second grounded kernel (e.g. PID), or the Flocq-scale grounding that would derive `real_fpbridge`.

## ✅ Update (2026-07-17) — items 2–4 done, PLUS a second grounded transcendental (`exp`)

This doc's own "Files" table above already lists most of the remaining work as *proved* (not just
scoped) — `pipeline_arith` covers the whole arithmetic fragment including negation (item 2),
`pipeline_{exp,log}_of_arith` covers one local-Lipschitz transcendental layer, `pipeline_nested_glob/
std` covers full recursive nesting for globally-Lipschitz primitives — but this "Recommended first
target" section never got updated to say so, and neither the arithmetic-fragment PID kernel
(`pid_grounded`) nor a transcendental kernel had actually been **grounded** (disclosed axiom + concrete
instantiation, not just the lever) until a later session did both:

- **`pid_grounded`** (arithmetic fragment on the real `pid.eml` datapath) and **`pid_tanh_grounded`**
  (first grounded transcendental kernel, `tanh`-saturated PID — globally `1`-Lipschitz, so
  unconditional) — `Certcom.real_tanh_eps`/`real_tanh_rounds`, `MachLib/FPGrounding.lean`.
- **`pid_exp_grounded`** (this update) — the SECOND grounded transcendental, and the first through the
  *local*-Lipschitz lever (`pipeline_exp_of_arith`, `AbsoluteFoldLocal.lean`): `exp(PID law)`,
  conditional on the PID's computed AND exact values landing in a caller-supplied `[lo,hi]` (the
  honest, expected shape for a non-globally-Lipschitz primitive — `tanh`'s unconditional result was
  the special case, not the norm). New disclosed axioms `Certcom.real_exp_eps`/`real_exp_rounds`,
  same trust status as the `tanh` pair. `AxiomLedger`: 273 axioms pinned (was 271), 9 headline
  footprints ⊆ trusted (84), 6 disclosed-trusted (was 4) — `pid_exp_grounded` added as a headline,
  `#print axioms` confirms all four `Certcom.*` axioms genuinely load-bearing, `sorryAx`-free.

**What's actually still open**: item 4's "genuinely harder piece" (full recursive LOCAL-Lipschitz
nesting — a local primitive over a subtree that ITSELF contains local transcendentals, needing
interval arithmetic with directed rounding to co-propagate range and error) remains unattempted —
`AbsoluteFoldLocal.lean`'s own docstring already flags this precisely. Item 5 (libm grounding) is now
2-of-11 primitives disclosed (`tanh`, `exp`) — `log`, `sin`, `cos`, `sinh`, `cosh` and the rest of the
`Trans1`/`Trans2` basis still rest on the generic, ungrounded `FPBridge`-style trust rather than their
own named axiom. Next: ground `log` (the OTHER concrete instance `AbsoluteFoldLocal.lean` already
provides, `pipeline_log_of_arith`) for a third data point, or a globally-Lipschitz primitive via
`pipeline_nested_glob/std` for the first grounded RECURSIVE kernel.

## ✅ Update (2026-07-17, same session) — `log` grounded too, item 5 now 3-of-11

**`pid_log_grounded`** (`FPGrounding.lean`): `log(1.5·e + 0.4·i + 0.05·d)` — same shape as `exp`
(local-Lipschitz lever, `pipeline_log_of_arith`, `L = 1/lo`), with one further honest cost `exp`
didn't have: `log` needs the domain to be strictly POSITIVE (`lo > 0`), not just bounded, since `log`
is only meaningfully Lipschitz — and only analytically defined — on `(0,∞)`. New disclosed axioms
`Certcom.real_log_eps`/`real_log_rounds`, same trust status as the `tanh`/`exp` pairs. Built green on
the first real attempt after fixing one naming slip (`Trans1`'s log constructor is `.ln`, not `.log`
— `.log` is the MATH function name, `Trans1.ln` is the AST node; easy to conflate, caught immediately
by the elaborator, not a substantive error). `AxiomLedger`: 275 axioms pinned (was 273), 10 headline
footprints ⊆ trusted (86) (was 9), 8 disclosed-trusted (was 6) — no incidental leaked-axiom fix needed
this time (unlike `exp`'s `exp_lt`), since `log`'s Lipschitz proof draws only on axioms already in
`trustedFootprint` from earlier work. `#print axioms` confirms all four `Certcom.*` axioms genuinely
load-bearing, `sorryAx`-free; full 373-module build green; `sorry_audit` unchanged (3 allowlisted).

**Libm grounding is now 3-of-11** (`tanh`, `exp`, `log`) — three data points on the actual cost
structure per primitive: a disclosed rounding constant always; a domain hypothesis unless globally
Lipschitz (`tanh` is the one exception so far); and, for `log` specifically, a positivity
side-condition on top of the plain range bound. Remaining primitives with no grounded rounding
constant yet: `sin`, `cos`, `tan`, `sqrt`, `abs`, `asin`, `acos`, `atan`, `sinh`, `cosh`, `log10` (11
total in the `Trans1` basis, plus `eml`/`pow` in `Trans2`). The genuinely harder open piece (full
recursive local-Lipschitz nesting) is unchanged by this update — still unattempted, still the one
named in `AbsoluteFoldLocal.lean`'s own docstring.

## ✅ Update (2026-07-17, same session) — `sin` grounded, item 5 now 4-of-11

**`pid_sin_grounded`** (`FPGrounding.lean`): `sin(1.5·e + 0.4·i + 0.05·d)` — back to the GLOBALLY
Lipschitz side (`TrigLipschitz.sin_lipschitz`, `L=1`), same shape as `tanh` — no domain hypothesis at
all, straight through `pipeline_tr1_of_arith`. Second data point (after `tanh`) confirming the
globally-Lipschitz primitives really are as cheap as `tanh` suggested, not a one-off. New disclosed
axioms `Certcom.real_sin_eps`/`real_sin_rounds`. Built green first try. `AxiomLedger`: 277 axioms
pinned (was 275), 11 headline footprints ⊆ trusted (92) (was 86 — jump reflects a second incidental
leak fix, `MachLib.Real.sin`/`cos`/`HasDerivAt_sin`/`pythagorean`, all already-known ℝ-witnessed
axioms nothing had exercised as a headline before), 10 disclosed-trusted (was 8). `#print axioms`
clean, `sorryAx`-free, full build green.

**Libm grounding is now 4-of-11** (`tanh`, `sin` globally Lipschitz; `exp`, `log` locally Lipschitz).
Remaining ungrounded: `cos`, `tan`, `sqrt`, `abs`, `asin`, `acos`, `atan`, `sinh`, `cosh`, `log10`.
`cos`/`atan`/`abs` are the other globally-Lipschitz primitives (per `AbsoluteFold.lean`'s own
docstring) — cheapest next targets, same `pipeline_tr1_of_arith` pattern as `tanh`/`sin`. The
recursive-nesting piece remains the one genuinely different, harder item on this list.

## ✅ Update (2026-07-17, same session) — `cos` grounded, item 5 now 5-of-11

**`pid_cos_grounded`** (`FPGrounding.lean`): `cos(1.5·e + 0.4·i + 0.05·d)` — third globally-Lipschitz
data point (`TrigLipschitz.cos_lipschitz`, `L=1`), identical pattern to `tanh`/`sin`, unconditional.
New disclosed axioms `Certcom.real_cos_eps`/`real_cos_rounds`. Built green first try. `AxiomLedger`:
279 axioms pinned (was 277), 12 headline footprints ⊆ trusted (95) (was 92 — one more incidental leak
fix, `MachLib.Real.HasDerivAt_cos`, already-known ℝ-witnessed, needed for `cos_lipschitz`'s own MVT
proof the same way `HasDerivAt_sin` was needed for `sin`'s), 12 disclosed-trusted (was 10). `#print
axioms` clean, `sorryAx`-free, full build green.

**Libm grounding is now 5-of-11** (`tanh`, `sin`, `cos` globally Lipschitz; `exp`, `log` locally
Lipschitz) — exactly half the `Trans1` basis. Remaining ungrounded: `tan`, `sqrt`, `abs`, `asin`,
`acos`, `atan`, `sinh`, `cosh`, `log10`. `atan`/`abs` are the last two globally-Lipschitz primitives —
last cheap targets before the remaining ones all need their own domain/positivity bookkeeping
(`sqrt`/`asin`/`acos` bounded-domain, `sinh`/`cosh` symmetric-magnitude, `tan`/`log10` composite-
derived). The recursive-nesting piece remains unchanged, still the one genuinely harder open item.

## ✅ Update (2026-07-17, same session) — `atan` + `abs` grounded, all 5 globally-Lipschitz primitives done

**`pid_atan_grounded`**/**`pid_abs_grounded`** (`FPGrounding.lean`): the last two of the five
globally-Lipschitz primitives (`InverseTrig.atan_lipschitz`, `OperatorBasisGeneral.abs_abs_sub_le`,
both `L=1`), identical unconditional pattern to `tanh`/`sin`/`cos`. `abs` is IEEE-754-exact in
principle (sign-bit clear, no rounding), but disclosed the same way as every other primitive rather
than assumed exact — the runtime call still goes through `mg_abs`/`fabs`, not a bare sign-bit op Lean
can see. New disclosed axioms `Certcom.real_atan_eps`/`real_atan_rounds`/`real_abs_eps`/
`real_abs_rounds`. Needed one new import (`InverseTrig`/`OperatorBasisGeneral` — `atan`/`abs_abs_sub_le`
live outside `FPGrounding.lean`'s existing transitive closure, unlike `sin`/`cos`), fixed on the first
rebuild. `AxiomLedger`: 283 axioms pinned (was 279), 14 headline footprints ⊆ trusted (101) (was 95 —
one more incidental leak fix, `MachLib.Real.atan`/`HasDerivAt_atan`, needed for `atan_lipschitz`'s own
proof; `abs` needed none), 16 disclosed-trusted (was 12). `#print axioms` clean on both, `sorryAx`-free,
full build green.

**Libm grounding is now 7-of-11** (`tanh`,`sin`,`cos`,`atan`,`abs` globally Lipschitz — ALL FIVE done;
`exp`,`log` locally Lipschitz). Remaining: `tan`, `sqrt`, `asin`, `acos`, `sinh`, `cosh`, `log10` — every
one of these needs its own domain/positivity bookkeeping (`sqrt`/`asin`/`acos` bounded-domain levers
already exist per `SqrtNode.lean`/`InverseTrigBounded.lean`; `sinh`/`cosh` symmetric-magnitude per
`HyperbolicLipschitz.lean`; `tan`/`log10` composite-derived). The recursive-nesting piece remains the
one genuinely different, harder open item, unchanged by this update.

## ✅ Update (2026-07-17, same session) — `sqrt`, `log10`, `asin`, `acos`, `sinh`, `cosh` grounded — 13-of-14, only `tan` left

**Six primitives in one batch**, all reusing math that already existed in the tree (no new derivative
axioms) — the "already had the Lipschitz lemma, just needed pipeline + axiom + grounding" case, as
opposed to `tan`'s (below).

- **`pid_sqrt_grounded`** — one-sided domain (`lo>0`), `L=1/(√lo+√lo)`, via `SqrtNode.sqrt_lip_local`
  (already existed).
- **`pid_log10_grounded`** — one-sided domain (`lo>0`), `L=1/(lo·log 10)`, via
  `Log10Lipschitz.log10_lip_local` (already existed). `leanPrims`'s own `.log10` interpretation is
  itself a composite of `ln` (`ln x / ln 10`), not a native call — same honest disclosure regardless.
- **`pid_asin_grounded`** / **`pid_acos_grounded`** — first SYMMETRIC-domain primitives (`[-R,R]`,
  `R<1`), `L=1/√(1−R²)`, via `InverseTrigBounded.arcsin_lip_local`/`arccos_lip_local` (already
  existed). Needed one small promotion: `sq_lt_one_of_abs_le_lt_one` was `private` in
  `InverseTrigBounded.lean` — made public (one-line edit) so the new pipeline wrappers could reuse it
  to derive the `0 ≤ L` obligation from the same in-domain witness `absenc_arcsin_local`/
  `absenc_arccos_local` already use internally.
- **`pid_sinh_grounded`** — symmetric domain, `L=cosh R`, unconditional (`cosh R>0` for every `R`, no
  extra sign hypothesis — the `sinh`/`exp` cheap case).
- **`pid_cosh_grounded`** — symmetric domain, `L=sinh R`, needs one extra `0≤R` hypothesis (`sinh R≥0`
  only for `R≥0` — the `cosh`/`log` costlier case, mirroring how `log` layers positivity on `exp`'s
  plain range bound).

New math added (not just axiom+wrapper plumbing): `HyperbolicLipschitz.lean` gained
`sinh_lip_local`/`cosh_lip_local` — `[lo,hi]`-shaped restatements of the already-proven
`sinh_lipschitz_bound`/`cosh_lipschitz_bound` (straight `abs_le_iff` repackaging, 0 new axioms, matches
`sqrt_lip_local`/`log10_lip_local`/`arcsin_lip_local`'s shape so `AbsoluteFoldLocal`'s generic
`pipeline_tr1_of_arith_local` could consume them directly). Six new `pipeline_X_of_arith` wrappers
added to `AbsoluteFoldLocal.lean`, mirroring `pipeline_exp_of_arith`/`pipeline_log_of_arith`'s shape
exactly. Twelve new disclosed axioms (`real_sqrt_eps`/`_rounds`, `real_log10_eps`/`_rounds`,
`real_asin_eps`/`_rounds`, `real_acos_eps`/`_rounds`, `real_sinh_eps`/`_rounds`, `real_cosh_eps`/
`_rounds`) in `FPGrounding.lean`. Full build green first try on the whole batch (375/375 modules).
`AxiomLedger`: 295 axioms pinned (was 283), 20 headline footprints ⊆ trusted (123) (was 101 — ten
incidental leak fixes: `MachLib.Real.sqrt`/`sqrt_le_of_le_sq`/`sqrt_nonneg`/`sqrt_sq_nonneg`
(shared by `sqrt`/`asin`/`acos`), `arcsin`/`HasDerivAt_arcsin`, `arccos`/`HasDerivAt_arccos`,
`log10`/`log10_def` — all already-known ℝ-witnessed axioms simply not yet exercised by any prior
headline), 28 disclosed-trusted (was 16). `#print axioms` clean on all six, `sorryAx`-free
(`tools/sorry_audit.lean`: still exactly 3 allowlisted, no new sorries), full build green.

**Correction to the running count:** prior updates in this doc said "X-of-11" — that was a miscount.
`Trans1` (`EMLToC.lean`) has **14** constructors: `exp,ln,sin,cos,tan,sqrt,abs,asin,acos,atan,sinh,
cosh,tanh,log10`. **Libm grounding is now 13-of-14** — every `Trans1` primitive except `tan` is
grounded. `tan` is qualitatively different from this whole batch: unlike every primitive grounded so
far, **no `HasDerivAt_tan` axiom and no Lipschitz bound exist anywhere in the tree yet** — `Trig.lean`
only has `tan_def : cos x ≠ 0 → tan x = sin x / cos x` (an algebraic identity, not a derivative). `tan`
needs fresh derivation: `HasDerivAt_tan` via `HasDerivAt_div` on `sin`/`cos` (needs `cos x ≠ 0`), then a
domain-bounded Lipschitz argument on `[-R,R]`, `R<π/2` (so `cos` stays bounded away from `0`, giving
`1/cos²` bounded by `1/cos²R` — needs a `cos`-positivity-on-`(-π/2,π/2)` fact that doesn't yet exist
either). Genuinely the harder remaining single-node item; the separately-flagged full recursive
local-Lipschitz nesting piece is still open on top of that.

## ✅ Update (2026-07-17, same session) — `tan` grounded, 14-of-14: every `Trans1` primitive done

**The last primitive, and the only one in this whole arc needing genuinely new math.** Confirmed with
the user via `AskUserQuestion` before adding anything (mirroring the one precedent for a new axiom
elsewhere in this session's work, the Khovanskii branch-curve `hasDerivAt_implicit_local`): grounding
`tan` needs `cos` to stay bounded away from `0` on `[-R,R]`, `R<π/2`, and nothing in `MachLib.Real`
establishes general `sin`/`cos` sign behavior — only isolated points (`cos_zero`, `cos_pi`,
`cos_pi_div_two`, the single-point `sin_one_pos`). User approved adding the axiom.

**New file `TanLipschitz.lean`.** **One new axiom**: `sin_pos_of_pos_lt_pi_div_two (x) (0<x) (x<π/2) :
0<sin x` — the trigonometric analogue of `cosh_pos`, and a direct generalisation of the
already-disclosed single-point `sin_one_pos`. Everything else is DERIVED from it (0 further axioms):
`cos_pos_of_lt_pi_div_two` (MVT between `x` and `π/2`, using `cos_pi_div_two=0` as the boundary value),
`cos_pos_of_abs_lt_pi_div_two` (extends via `cos_neg` evenness), `cos_antitone` (MVT + the new axiom
bounding `-sin`'s sign, the trig analogue of `cosh_mono`), `cos_ge_of_abs_le` (radial form, matching
`sqrt_mono`'s role in `arcsin_lip_lt`), `HasDerivAt_tan` (derived as `(sin·cos⁻¹)'` exactly like
`HasDerivAt_tanh`'s `(sinh·cosh⁻¹)'`, simplified via `pythagorean` — but transferred from the raw
`sin·(1/cos)` lambda to `tan` via `HasDerivAt_congr`, a LOCAL δ-ball argument, not the global
`HasDerivAt_of_eq` every other primitive used: `tan_def`'s identity only holds where `cos≠0`, so the
two functions agree in a neighbourhood of `x`, not everywhere, unlike `tanh_eq_sinh_div_cosh` which is
unconditional since `cosh` is never zero), then `tan_lip_lt`/`tan_lip_local`/`absenc_tan_local`
mirroring `arcsin_lip_lt`'s exact structure (`L=1/cos²R`).

`pipeline_tan_of_arith` added to `AbsoluteFoldLocal.lean`. `pid_tan_grounded` added to
`FPGrounding.lean` — needs both `hR0:0≤R` (the `cosh`-shaped extra hypothesis) and `hR:R<π/2`. Full
build green first try on `TanLipschitz.lean`'s math (4 small `rw`/`congrArg`-direction slips caught and
fixed on the FIRST build attempt: an under-constrained implicit in `cos_pos_of_abs_lt_pi_div_two`'s
negative branch needing explicit intermediate `have`s instead of inline `by rw` terms; `congrArg cos h`
needing `h.symm` for the equality-case direction; `mach_ring` failing to close a 3-term identity
(`x+(y-x)=y`) that `mach_mpoly` closed instead — `mach_ring` is the narrower of the two, not a general
decision procedure; a dropped `rw`-to-`0` step in the `p=q` Lipschitz-bound case). Full project build
green after fixes (376/376 modules). `AxiomLedger`: 298 axioms pinned (was 295), 21 headlines ⊆ trusted
(132, was 123 — six incidental leak fixes: `HasDerivAt_congr`, `cos_neg`, `cos_pi_div_two`, `pi`, `tan`,
`tan_def`, all already-known ℝ-witnessed, simply unexercised by any prior headline), 31 disclosed-trusted
(was 28 — the two `real_tan_eps`/`_rounds` rounding constants plus `sin_pos_of_pos_lt_pi_div_two`
itself, disclosed for a different reason than every other entry: not residual libm/IEEE-754 trust, but
a foundational math fact `MachLib.Real`'s minimal trig axiomatization doesn't derive). `#print axioms`
clean, `sorryAx`-free (`tools/sorry_audit.lean`: still exactly 3 allowlisted, no new sorries).

**Every `Trans1` constructor is now grounded — Theorem A's libm-primitive-grounding item is CLOSED,
14-of-14.** The only remaining open item in this doc is the separately-flagged full recursive
local-Lipschitz nesting piece (a local primitive over a subtree that itself contains local
transcendentals) — see `AbsoluteFoldLocal.lean`'s own scope note, unchanged by this update.

## ✅ Update (2026-07-17, same session) — recursive local-Lipschitz nesting CLOSED

**The last open item on this whole doc.** `AbsoluteFoldLocal.lean`'s own scope note named the exact
blocker: at a nested local-Lipschitz node, the domain condition on the COMPUTED input
(`toR (evalEML … e).toF ∈ [lo,hi]`) is a fact about a float value produced by an arbitrarily deep
subtree, not a leaf — the concern being that the range and the accumulated error would need to be
propagated together via directed-rounding interval arithmetic.

**The resolution turned out to be simpler than that concern implied.** New file
`AbsoluteFoldNestLocal.lean`: `IsFoldLocal` — the nestable fragment for arithmetic plus `tr1` nodes,
where each occurrence carries its OWN witnessed domain `[lo,hi]`, Lipschitz certificate `(L, hLnn,
hLip)`, AND both range hypotheses (`hflx_lo/hi` on the computed value, `hxe_lo/hi` on the exact value)
as EXPLICIT constructor data — i.e. the fix is not to derive one range from the other via interval
arithmetic, it's to require both explicitly at every node, exactly repeating the flat
`pipeline_tr1_of_arith_local`'s own two-hypothesis shape instead of only allowing it at the outermost
node. Since the Lipschitz constant genuinely differs by primitive AND by the domain chosen at that
occurrence (`exp hi`, `1/lo`, `1/(√lo+√lo)`, `1/√(1-R²)`, `cosh R`, `sinh R`, `1/cos²R`, …) with no
single closed-form covering all of them, this per-occurrence data lives on the `tr1` constructor
itself rather than a global `Trans1 → Real` parameter (unlike `AbsoluteFoldNest`'s `Lip1`, which could
be global precisely because global-Lipschitz primitives need no domain at all).

`nested_fold_local`/`pipeline_nested_local` — the recursive theorem and its through-the-emitted-C
wrapper — mirror `AbsoluteFoldNest`'s `nested_fold`/`pipeline_nested` exactly: the bound stays
EXISTENTIAL (`∃ E, AbsEnc E …`), so each node's error is whatever `absenc_add`/`absenc_lip_local`
witnesses, composing cleanly with no closed form needed. Pure plumbing over the Lipschitz lemmas
already proven for every primitive this session (`ExpLipschitz`, `TransNodes`, `SqrtNode`,
`Log10Lipschitz`, `InverseTrigBounded`, `HyperbolicLipschitz`, `TanLipschitz`) — no new math, no new
axioms. Confirmed by `#print axioms`: only Lean core + already-known `MachLib.Real` field axioms,
nothing new — matches the pre-existing `nested_fold`/`pipeline_nested`/`pipeline_nested_glob`/
`pipeline_nested_std` precedent (`CertifyNested.lean`), none of which are in `AxiomLedger`'s
`headlines` either, since they're generic combinators, not certificates grounded at the real
`Certcom.realToR`/`leanPrims` artifact — that concrete-instantiation layer stays a separate, later step
for whichever specific nested kernel needs it, exactly as it already was for the globally-Lipschitz
case (`pipeline_nested_glob`/`pipeline_nested_std` were never concretely instantiated at `leanPrims`
either — this closure is at parity with, not behind, the established precedent).

**Non-vacuity, not just structure**: `log(sinh(x) + y)` — a LOCAL-Lipschitz primitive over an
arithmetic subtree that ITSELF contains another LOCAL-Lipschitz primitive, exactly the shape
`AbsoluteFoldNest` could not cover — is proven to be in the fragment, given honest range hypotheses at
each level, exercising two REAL, distinct per-primitive Lipschitz certificates (`sinh_lip_local`,
`log_lip_local`) composed through the recursion.

Full build green first try on the math (one `noncomputable` annotation needed on the demo's
`realOf1`). Full project build green (377/377 modules). `AxiomLedger` unchanged (298/21/132/7/31 —
correctly: no new disclosed axioms, nothing added to `headlines`). `sorry_audit`: still exactly 3
allowlisted, no new sorries.

**Every item flagged as open anywhere in this document is now closed**: all 14 `Trans1` primitives
grounded, and the recursive local-Lipschitz nesting gap resolved. The only work left in this whole
arc is optional, forward-looking, and un-scoped: concretely instantiating `pipeline_nested_local` at
`Certcom.realToR`/`leanPrims` for a specific multi-level kernel (mirroring `FPGrounding.lean`'s flat
`pid_X_grounded` pattern, one level deeper) — a natural next increment, not a gap.

## ✅ Update (2026-07-17, same session) — the multi-level instantiation, done

**The optional next increment named above, taken.** User: "multi-level instantiation, lets do this
please." `pid_log_cosh_grounded` (`FPGrounding.lean`) — the first (and only) headline whose footprint
spans EVERY disclosed primitive axiom at once, and the first genuinely LOCAL-over-LOCAL kernel
concretely grounded at the real `Certcom.realToR`/`leanPrims` artifact rather than left as the generic
`pipeline_nested_local` combinator.

**The kernel: `log(cosh(PID law))`** — the "log-cosh loss," a standard smooth, outlier-robust
alternative to L1/L2 loss genuinely used in control/ML gain-shaping, not an arbitrary composition.
`cosh` needs a symmetric domain `[-R,R]`; `log` needs a positive one-sided domain `[lo,hi]` — two
different domain SHAPES stacked, the harder case flagged in `pipeline_tr1_of_arith_local`'s own
docstring (positivity layered on top of a plain range bound), now one level deeper.

**Three pieces of new infrastructure, all in service of instantiating the generic
`nested_fold_local`/`pipeline_nested_local` at a concrete kernel**:
1. `realOfAll14`/`Eround1All`/`hround_all` (`FPGrounding.lean`) — since `pipeline_nested_local`'s
   `hround` is universally quantified over ALL fourteen `Trans1` constructors (not just the two the
   kernel actually uses), a concrete instantiation needed a TOTAL real-semantics map and a TOTAL
   disclosed-eps map across every primitive — buildable only now that all fourteen are grounded.
   `hround_all` is a 14-way `cases t with` split, one line per primitive, each closed directly by the
   `real_X_rounds` axiom already disclosed for it earlier this session.
2. `isFoldLocal_of_isArith` (`AbsoluteFoldNestLocal.lean`) — lifts a plain `IsArith` proof (e.g.
   `isArith_pidRawEML`) into `IsFoldLocal` by structural induction, since `IsFoldLocal`'s non-`tr1`
   constructors are a verbatim copy of `IsArith`'s.
3. `exactRn_eq_exactR_of_arith` (`AbsoluteFoldNestLocal.lean`) — proves `exactRn` agrees with the
   familiar flat `exactR` on any `IsArith` tree (their non-`tr1` cases are definitionally identical),
   so the final theorem's conclusion reads `log (cosh (exactR realToR env pidRawEML))` — matching
   every flat `pid_X_grounded`'s own conclusion shape — instead of the more general `exactRn`.

`pid_log_cosh_grounded` itself: builds the `IsFoldLocal` proof term for `.tr1 .ln (.tr1 .cosh
pidRawEML)` directly (`cosh_lip_local`/`log_lip_local` supply the two Lipschitz certificates, `sinh R`
and `1/lo` respectively), applies `pipeline_nested_local`, then rewrites the existential conclusion
into the `exactR`-based form via the two new helpers. Full build green FIRST TRY — no proof errors at
all, the payoff of the careful signature-matching work done grounding every individual primitive
earlier this session. Full project build green (375/376 modules built this pass, incremental). `#print
axioms` clean, `sorryAx`-free: `pid_log_cosh_grounded`'s footprint is exactly the union of all
fourteen primitives' disclosed axioms plus the standard `MachLib.Real` core — nothing unexpected.
`AxiomLedger`: 298 axioms pinned (UNCHANGED — no new axioms, everything here is theorems/defs over
already-disclosed ones), 22 headline footprints ⊆ trusted (132, UNCHANGED — zero incidental leaks:
every axiom this kernel touches was already made trusted by the individual primitive groundings
earlier this session), 31 disclosed-trusted (UNCHANGED). `sorry_audit`: still exactly 3 allowlisted.

**This closes the "optional, un-scoped" item named at the top of this update — certcom-A now has a
concrete, multi-level, axiom-disclosed certificate about a real recognizable composite kernel, not
just the flat single-primitive instances.** No further open items remain anywhere in this document.

## Recommended first target — the keystone, bounded route

**Name `realToR` + the single disclosed `FPBridge realToR` axiom, instantiate `pipeline_arith` (and
the `x²+y²` / PID kernel) at it, and register the axiom in the AxiomLedger.**

Result: the **first unconditional end-to-end forward-error certificate about actual `Float`
computations** — converting the whole `∀ toR, FPBridge toR → …` tower from "conditional, only a
degenerate witness" into "applies to the real artifact, modulo one honest, universally-accepted,
explicitly-disclosed axiom." Why this beats the pure-proof wins as a *first* step:

- It is the single keystone: one axiom grounds the entire proved tower at once.
- It completes the trust-boundary narrative — `FPBridge` is *the* axiom that structurally cannot be
  witnessed (opaque `Float`), the honest floor under everything, disclosed exactly like `erf`.
- It connects Theorem A to the ledger/witness machinery already built: Theorem A's footprint becomes
  auditable alongside the Khovanskii headlines, and the AxiomWitnessBridge gains a disclosed-but-
  un-witnessable entry with a stated reason (Float opaqueness) — not a hidden gap.
- Scope: ~1–2 sessions, mostly instantiation wiring + one axiom + ledger registration.

Optional warm-up: close the `neg` node (item 2) first — a small pure-Lean proof that fully closes the
arithmetic fragment, satisfying before the keystone.

## Files

`machlib/foundations/MachLib/`: `EMLToC.lean` (T1), `EMLToCRuntime.lean` (T2),
`CompositeRuntimeError.lean` (T3), `FloatRealBridge.lean` (the `FPBridge` interface + worked kernel),
`AbsoluteFold.lean` / `AbsoluteBridge.lean` / `AbsoluteFoldPos.lean` / `AbsoluteFoldLocal.lean` /
`AbsoluteFoldNest.lean` / `AbsoluteFoldNestLocal.lean` / `CertifyNested.lean` (the fold family).
Primitive Lipschitz lemmas: `ExpLipschitz.lean` / `TransNodes.lean` / `SqrtNode.lean` /
`Log10Lipschitz.lean` / `InverseTrigBounded.lean` / `HyperbolicLipschitz.lean` / `TanLipschitz.lean`.
Trust constants: `FPModel.lean` (`axiom u`, `RoundsW`). Ledger: `machlib/foundations/AxiomLedger.lean`;
witness bridge: `monogate-lean/MonogateEML/AxiomWitnessBridge.lean`.
