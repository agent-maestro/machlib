# MachLib — what is proven, what it rests on, what is open

A reader's front door. Its only job is to say, precisely and checkably, what
this library establishes, what those results depend on, and where the seams are.
If something here reads as a claim you can't reproduce in a few commands, that's
a bug in this document — tell us.

Scope note: this covers the **verified-numerics** core and the **axiom base**.
Other lanes (the Khovanskii zero bound, the larger frontier explorations) are
summarised honestly at the end with their asterisks named, not hidden.

A reader who cares about the *mathematics* of the EML class rather than about
compiled numerics should read `eml_depth_problems.md` instead: it defines the
object from scratch and states the four open questions in a form an outside
mathematician can attack or dismiss without reading anything else here.

---

## 1. What this is

A compact, **Mathlib-free** Lean 4 verification layer for the numeric kernels
that Forge emits (EML → C/Rust/WGSL/RTL/…). It is *not* a Mathlib replacement and
not a general analysis library. It proves a small, specific set of things about
floating-point and fixed-point numeric code, end to end, and is scrupulous about
the boundary between what is proved and what is assumed.

Everything below is `sorryAx`-free unless explicitly flagged. "`sorryAx`-free"
means no `sorry`/`admit` holes — every step is a real proof — but it does **not**
by itself mean the *axioms* a proof rests on are consistent. Section 4 is about
exactly that gap, and how we close it.

---

## 2. Start here: the two halves, and the join that is NOT yet proved

> ## ⚠ CORRECTED 2026-08-10. This section previously claimed the two halves were "the *same* checked fact, not two separate claims bridged by hand". **They are two separate claims, and the bridge is this prose.** Both halves are real; the join is not formalised. Corrected on inspection of the actual proof term, before the claim went to outside readers.

**What IS machine-checked, in two independent pieces:**

- `fxpid` builds the PID multiply-add `Kp·e + Ki·i + Kd·d` as a `List Bool`
  bit-vector circuit out of verified gates; `fxpid_correct` proves the netlist
  computes the sum of the three truncated scaled products.
- `fxpid_trunc_lt_3ulp` proves that circuit discards `< 3·2^FRAC` **integer
  units**. Pure `Nat` arithmetic, Lean-core only.
- `pid_trajectory_from_bits` proves that **for any `ε`**, a per-step bound `ε`
  lifts to `|xc n − xe n| ≤ ε · geom c n` for all `n`. For a contracting plant
  (`c = 0.99`) that is `≤ 100 ε` over the entire run.

**What is NOT proved — two joins, both currently carried by prose:**

1. ~~**`Nat` → `Real`.**~~ **CLOSED, same day** — `MachLib/FixedPointRealBridge.lean`.
   `fxmul_real_trunc_lt_ulp` and `fxpid_real_trunc_lt_3ulp` state the truncation
   bounds over `MachLib.Real`, derived from the `Nat` versions through
   `natCast_lt_mono` (proved here from `natCast_succ`). Both are unconditional —
   the `Nat` premise is discharged inside, not assumed. Reading them in Q-format
   is now ordinary ordered-field algebra rather than a convention in a comment.
2. **Datapath → closed loop.** **CLOSED for the affine PLANT kernel** —
   `MachLib.Real.fxaffine_traj_tracks_exact`. The netlist's own trajectory stays
   within `ulp · geom (qval c) n` of the exact real one, with `ε = ulp` *derived*
   from `fxaffine_step_error`, not supplied. The theorem quantifies over
   `List Bool`, so the subject really is the datapath.

   **Still open for `fxpid`.** The trajectory theorem's plant is the affine map
   `c·x + d`, and `fxaffine` is that kernel; `fxpid` is the *controller's*
   multiply-add. Connecting the controller's output to the plant's state update
   needs a closed-loop model this corpus does not have — and
   `pid_trajectory_from_bits` itself still quantifies `ε` universally, so the
   auditor's firing specimen still fires, correctly.

Inspect the proof term and the gap is immediate — `pid_trajectory_from_bits`
elaborates to `fun … => affine_trajectory_bound …`, mentioning no bit-level
object at all. The name is aspirational.

**Why this matters more than a wording fix.** The composition — implementation
error *derived from the shipped datapath* and *consumed by* a physical-system
guarantee — is the programme's most distinctive claim, and the thing outside
readers identified as potentially publishable.

**Status: the composition EXISTS, for the affine plant kernel.**
`fxaffine_traj_tracks_exact` is the end-to-end statement — implementation error
derived from the shipped datapath and consumed by a trajectory guarantee, in one
theorem whose statement names the datapath. That is what the section originally
claimed and did not have.

What remains is narrower and should be stated as such: the same composition for
the **controller** path (`fxpid`), which needs a closed-loop model relating
controller output to plant state. `pid_trajectory_from_bits` is untouched by this
work and still quantifies `ε` universally; do not cite *it* as the end-to-end
result. Cite `fxaffine_traj_tracks_exact`.

**Sized on 2026-09-05, by reading signatures rather than the route map. It is not a
composition of existing pieces.** Four objects are missing, and the first one blocks the
other three:

1. **The bit-level model is unsigned.** `MachLib.RTL` has `add`, `mul`, `fxmul`, `fxaffine`,
   `fxpid` over `List Bool` decoded by `toNat`; there is no subtraction, negation, or
   two's-complement anywhere, so `qval bs ≥ 0` always. A PID error signal `e = r − y` and a
   negative control output are **not representable** in the datapath the join is about.
   Negative feedback cannot be written in this model, so no stabilising closed loop can be.
2. **No closed-loop object over bits.** `fxTraj` hard-codes a constant `d`; nothing feeds
   `fxpid`'s output into `fxaffine`'s input, and `fxpid`'s `e`, `i`, `d` are free inputs with
   no accumulator recurrence and no anti-windup bound (`FixedPointSat.satW` exists and is used
   nowhere).
3. **No `qval`-scale step lemma for `fxpid`.** `fxpid_real_trunc_lt_3ulp` is at product scale;
   the analogue of `fxaffine_step_error` does not exist. This one is small.
4. **Every trajectory lemma is scalar and first-order.** A loop with an integrator is not, and
   `clamp_guarded_tracking` (`CompiledClosedLoop`), the one lemma with a controller in the loop,
   needs a Lipschitz bound of the control law in the state that no lemma supplies for the PID
   law.

The honest price is a signed fixed-point RTL layer with its own real bridge, a closed-loop
recurrence over bits, and a first-order (proportional, or saturated-integral) instance of the
tracking theorem — several sessions, mostly in (1). A "join" built inside the unsigned model
(positive feedback only) would be true and hollow, and is deliberately not written.

### ⚠ UPDATED 2026-09-06 — (1) and (2) are done, and there is now a closed-loop join for a P controller

`MachLib/SignedFixedPoint.lean` supplies the missing layer, and
`sfxloop_tracks_exact` is the composition **for a proportional controller**:

> the signed bit-level closed loop `X_{k+1} = A·X_k ⊕ KP·(R ⊖ X_k)`, built from `List Bool` pairs
> by the signed adder, subtractor and truncating multiply, stays within `4·ulp · geom(A−KP)(n)`
> of the exact real closed-loop trajectory — with the per-step `4·ulp` **derived from the bits**,
> not supplied.

`sorryAx`-free; the footprint is the algebra/`exp`-free spine plus `natCast` and the division
axioms — no analytic axiom, no float bridge. It ships with specimens
(`gain_specimen`, `sfxloop_tracks_exact_specimen`, and `sval_neg_specimen` exhibiting an actual
negative value), because this corpus has one recorded flagship that was vacuous for weeks while
every gate passed.

**How the four obstacles moved.**

1. **Unsigned model — REMOVED.** A signed value is a *pair* of unsigned vectors read as their
   difference, `sval (p, n) = qval p − qval n`. Not two's-complement: `RTL` has no fixed width
   (`addc` pads and grows), so there is no wraparound to model and nowhere to put a sign bit. The
   difference representation needs no width, adds no primitive, and makes addition, negation and
   **subtraction** exact, each discharged by an existing `RTL` correctness lemma.
2. **No closed-loop object over bits — REMOVED for this loop.** `sfxloop` feeds the controller's
   output into the plant's state update, which is what `fxTraj`'s constant `d` could not do.
3. **No `qval`-scale step lemma — done on the signed side.** `sval_sfxmul_error` bounds the signed
   truncating multiply two-sidedly by `2·ulp`; two of them give the loop's `4·ulp`. The bound is
   `2·ulp` and not `1·ulp` because each limb truncates two unsigned cross products, and that
   factor of two is carried rather than hidden. The `fxpid`-specific lemma is still not written.
4. **Scalar first-order trajectory lemmas — not binding here.** Closing a *proportional*
   controller around an affine plant leaves an affine map, `A·x + KP·(R−x) = (A−KP)·x + KP·R`, so
   `affine_trajectory_bound` applies unchanged. This is a property of the P controller, not a
   shortcut.

**What is still open, and it is obstacle (4) in its real form.** This is a P controller: no
integrator, no anti-windup, and the closed-loop map stays first-order. **A PID loop does not**,
because the integrator adds state — so the PID join needs a trajectory lemma over a non-scalar
state, which the corpus does not have. `pid_trajectory_from_bits` is still not the end-to-end
result and its `ε` is still universally quantified. What changed is that the blocker is now one
identified missing lemma rather than a representation that cannot express the problem at all.

---

## 3. The verified-numerics spine

The capstone sits on top of a layered algebra. Each layer is its own module,
`sorryAx`-free.

| Layer | What it proves |
|---|---|
| `FPModel` | **Cross-target equivalence**: two evaluations of the same exact value (e.g. Rust f64 vs WGSL f32) agree within the sum of their forward-error bounds (`cross_target`). The standard floating-point model (Higham) as a precision-generic `RoundsW w`. This is the *software/GPU* end. |
| `ForwardError`/`HybridError` | A compositional two-sided forward-error algebra (`Renc`), incl. transcendental∘arithmetic kernels (e.g. Gaussian). |
| `BackwardError` | Single-op backward error, the general `γₙ` bound (Higham), and the per-term inner-product result `chain_backward`. |
| `IntervalArith` | Rigorous enclosures: the loose symmetric product and the **tight 4-corner** `Interval.mul`. |
| `AffineContraction` | Trajectory bounds for affine / Lipschitz / domain-local / nonlinear iterations (the certificate the capstone uses). |
| `ConditionNumber` | The condition number characterised; `κ ≤ 3` proved for the dominant-term family. |
| `RippleCarry`→`BitVecMul`→`FixedPointRTL`→`FixedPointSat` | **Leg B, bits→analytic**, all **pure Lean-core** (`propext`/`Quot` only): a verified adder, a verified multiplier, the Q16.16 scaled multiply, and `fxmul_trunc_lt_ulp` — the shift discards `< 1 ULP`, *exactly* the analytic forward-error bound, now derived from the bit-level division rather than assumed. |

What this spine does **not** include: a proof that the Forge compiler itself is
correct (see §6), and grounding of the analytic base in a construction of ℝ
(see §4).

---

## 4. What it rests on — the axiom base, honestly

MachLib is Mathlib-free *by design*. The cost of that choice is explicit: the
things Mathlib would prove as theorems — the real-number field/order axioms, the
definitions and derivatives of `exp`/`sin`/`cos`/`log`/`sqrt`, the floating-point
model — are **axioms** here. As of 2026-09-05 the ledger pins **243 axioms**
(`lake env lean AxiomLedger.lean`: 221 `MachLib.*` plus 22 `Certcom.*`), of which
**149** form the trusted footprint of the headline theorems, and every one of those 149 is
modeled: 112 witnessed by a kernel-checked Mathlib term, 12 interpreted carrier and function
symbols, 3 standard, 22 IEEE-754 float-bridge facts validated by measurement — see
[`AXIOM_MANIFEST.md`](../AXIOM_MANIFEST.md), which is generated, and **(d)** below. (This
section said **260** from 2026-06-27 until 2026-09-05; that figure was a different count over a
different tree, and it is the reason `tools/prose_counts_check.py` now exists.) But a single
number lumps two very different kinds of axiom together, and the distinction is the whole point
(tier list in **(c)**). Four things make the base honest rather than hand-wavy:

**(a) The base is proven consistent, for the results that matter.**
`#print axioms` proves a theorem has no `sorry`; it does *not* prove its axioms
can't jointly derive `False` (a bogus `axiom foo : (0:Real) = 1` would pass every
`#print axioms` check yet make everything vacuous). `MachLib.CoreModel` closes
that gap for the flagship closure (the capstone + the forward/backward/interval/
contraction/κ results — an ordered commutative ring with `abs`). It bundles that
closure as `RealCoreSpec` and exhibits **two** inhabitants:

- `machlibWitness` over `MachLib.Real` — *faithfulness*: each field is the actual
  MachLib axiom, so the spec is no stronger than what MachLib assumes.
- `intModel` over **ℤ** — *consistency*: every closure axiom holds in ℤ, and
  `#print axioms intModel` = `[propext, Classical.choice, Quot.sound]` only — **none
  of MachLib's axioms**. A genuine external model.

A model exists ⇒ the closure can't prove `False` ⇒ those results are **not
vacuous**. A CI gate (`scripts/check_consistency_model.sh`) fails if `intModel`
ever becomes circular. This is the honest answer to "are these results empty?".
*Caveat:* the model covers the division-free, transcendental-free spine (what the
moat results ride on); the field and analytic axioms are modelled by ℝ, not ℤ —
which is exactly why they remain separate axioms.

**(b) The base is being minimised — what's redundant is removed, what's
primitive is named.** A systematic audit promoted **32 axioms to theorems
(292 → 260)** without changing any statement: the redundant ring/abs/field facts,
and — on the analytic side — the hyperbolic functions are now *entirely* reduced
to `exp` (their identities, conversions, and addition formulas are theorems;
only `sinh_eq`/`cosh_eq`, `tanh_eq`, and positivity remain axioms), plus the
one-sided trig bounds and `tan 0 = 0`. What remains is *defining* primitives
(the field operations, `exp`/`sin`/`cos`/… definitions and derivatives, the FP
unit roundoff, the carrier) — not derivable short of constructing ℝ, which is out
of scope under the Mathlib-free doctrine. The full promotion list (which 32 axioms,
each derivation) is tracked in the project's internal audit notes.

**(c) Two tiers — foundational primitives vs mathematical assumptions.** A single
count hides the axioms that actually matter. They split cleanly, and a reader
is entitled to see which is which:

- **Foundational primitives** (the overwhelming majority). The real-number field and
  order, the carrier, the definitions and derivatives of `exp`/`sin`/`cos`/`log`/`sqrt`,
  the FP unit roundoff, the Rolle zero-counting corollary. Mathlib proves every one of
  these as a theorem; they are standard. Grounding them is the open Mathlib-free work
  named above — *not* a claim about anything novel. Nobody should blink at these.
- **Mathematical assumptions** (a named handful). Axioms that assert a *deep classical
  theorem being cited*, not a substrate primitive — the asterisks, the contribution if
  discharged and the gap if not:
  - `PfaffianFunction.zero_count_bound_classical` — **Khovanskii's classical zero bound
    (1991, Ch. 3 Thm. 1)**. Mathlib does not have this either. It is consumed *only* by
    the legacy general-`PfaffianFunction` development; **no featured result and no
    application touches it** (verify with `#print axioms`).
  - `PfaffianFn.khovanskii_chain_step` — the chain-step form of the same classical bound,
    for the newer chain-explicit infrastructure.
  - `eml_pfaffian_validon_from_sin_equality` — the sin-barrier validity bridge the
    EML-separation results lean on.

The featured Khovanskii results stay in the first tier: the single-exp bound
(`expPoly_khovanskii_bound`) is **proven outright**, and the general triangular-chain
bound (`khovanskii_bound_full`) is a constructive **reduction** — given a reducibility
witness it derives the bound from the Rolle corollary, with no classical-Khovanskii
axiom. So the one deep assumption is isolated, named, and off the featured path. What is
earned and what is cited never share a count.

**(d) Every trusted axiom has a model, checked outside this library.** Nothing Mathlib-free
can show its own axioms are satisfiable, so the check lives in the sibling project
`monogate-lean`, which imports both Mathlib and MachLib and, for each of the 149 trusted axioms,
verifies in the kernel that a Mathlib term inhabits the axiom's *interpreted* type
(`MachLib.Real ↦ ℝ`, `exp ↦ Real.exp`, …). The result is a certificate *about* MachLib, never a
dependency *of* it. The 22 float-bridge axioms are the exception by nature — Mathlib has no
IEEE-754 semantics — and they are kept in their own class rather than averaged in, because a
hardware certificate rests on exactly those. The honest headline is therefore **zero unmodeled
axioms**, never "zero axioms". Gate 13 (`tools/soundness_witness_audit.py`) fails if the witness
project's toolchain drifts from this one, because the witness went dark for 33 days once while
the ledger kept reporting "trusted".

---

## 5. How to check any of this yourself

```
# every theorem is a real proof (no holes):
lake build MachLib

# what a result actually depends on (look for sorryAx — there is none):
#print axioms MachLib.Real.pid_trajectory_from_bits

# the consistency witness depends on NO MachLib axiom (core only):
#print axioms MachLib.Model.intModel
#   ⇒ [propext, Classical.choice, Quot.sound]

# the gates:
bash foundations/scripts/check_aggregator.sh          # no ungated orphan modules
bash foundations/scripts/check_consistency_model.sh   # ℤ-model stays external
python tools/check_zero_mathlib_dependency.py         # the zero-Mathlib claim
```

---

## 6. What this does **not** claim

- **No physical silicon claim here.** Leg B proves the *bit-level* datapath
  computes its denoted integer/fixed-point function. That an FPGA bitstream or a
  microcontroller binary behaves identically is a *separate, empirical* matter,
  handled in a different (gated) lane — not proved in this library.
- **No compiler-correctness claim.** The binding-integrity gate checks that a
  proof is *about the shipped expression* (via a canonical AST hash), and the
  cross-target results prove agreement *given the model*. Neither proves Forge's
  compiler is correct.
- **The analytic base is axiomatized, not constructed.** §4 is the whole story;
  we do not build ℝ. We prove the load-bearing closure consistent and minimise
  the rest.
- **Not a Mathlib replacement**, and not a general theorem library.
- **Coverage / close-rate numbers are per-release snapshots**, regenerable from
  source; treat any single number as snapshot-specific.

---

## 7. The other lanes — named with their asterisks

- **`L_F` query complexity — the zero-query layer, complete as of 2026-08-21.** A
  separate lane from the numerics spine: how many calls to the one transcendental
  generator `F(x) = eˣ + log₀ x` a function needs. `C_k` = computable with `k`
  `F`-queries.

  - **`C₀` is characterised, globally.** `zero_query_iff_ratGerm` makes
    `C₀ = eventual rational germs` an equality, and
    `zero_query_finite_exception_normal_form` upgrades that to a **global** normal
    form: an `F`-free term is `P(x)/Q(x)` outside a **finite** exceptional set, with
    `Q` nonvanishing there. The finite-exception form matters — the eventual form is
    blind to bounded regions, which is where `floor`/`mod` misbehave.
  - **Two exclusions, by two different instruments.** `logQueryLowerBound_holds`
    (`log ∉ C₀`, by substituting `x = exp t` and landing in `exp_not_algebraic` — a
    *growth* question moved into an *algebraic* frame) and `sign_not_zero_query`
    (`sign ∉ C₀`, by **level sets**: `zero_query_level_set` says a level set is finite
    or everything-off-the-exceptional-set, and a ray is neither). The second is the
    first lower bound here whose obstruction is *branching* rather than growth.
  - **And a matching upper bound.** `sign_query_cost_bounds_tight`: `1 ≤ q_F(sign) ≤ 12`.
    `sign` is **not** zero-query yet **is** a finite expression once one totalised
    transcendental is available — `sign x = (logGap x − logGap(0−x))/log 2` where
    `logGap x = log(2x) − log x` is the constant `log 2` on `x > 0` and `0` on `x ≤ 0`.
    **The zero-query barrier is a basis boundary, not an expressibility barrier.**
  - **The level-0 asymptotic toolkit, all algebraic.** `pev_zero_or_finite_roots`
    (synthetic division, no analysis), `pev_leading_form` (one exponent, both bounds),
    `ratGermTrichotomy_holds` (bounded or at-least-linear), `pev_eventual_sign` and
    `ratGermSignedTrichotomy_holds` (constant sign, **without** the intermediate value
    theorem), `ratGerm_shape` (decay-like-`1/x` versus a nonzero floor). None of these
    touches a derivative, continuity, Rolle or IVT axiom. Check any of them:
    ```
    #print axioms MachLib.ratGermSignedTrichotomy_holds
    #   ⇒ no HasDerivAt, no rolle, no sorryAx
    ```

  **What is open, and precisely where.** `q_F(sign) ≥ 2` reduces to `OneQueryLevelSet`
  (a *new* ledger row — **not** `OneQueryDichotomy`, which is an *eventual* statement
  and `sign` is eventually constant, so it excludes nothing). `q_F^global(exp) ∈ {1,2}`
  turns on the same bounded region. And `BoundedGermTranscendence` is now known to be
  **out of reach of every instrument in this library**: `polyEnvelope_of_Fbasis_floor`
  and `polyEnvelope_of_Fbasis_decay` prove `F ∘ S` has a polynomial envelope for *every*
  bounded rational `S`, while every exclusion theorem here works by *escaping* one. The
  differential route's infrastructure is built (`pderiv`, `y' = S'·y`,
  the germ-derivative transfer, and differentiation of the relation itself). What remains
  was described here on 2026-08-21 as "the transcendence input that rules out the
  eliminated relation being trivial". **That was the wrong type**, and the correction is now
  machine-checked rather than argued: with `W = pⱼ/p_m` the trivialising condition is
  `W' = (m−j)·S'·W`, an identity between *rational functions*, and what refutes it is an
  **order-of-vanishing count**. No transcendence input appears anywhere in it.

  **The count is proved, at arbitrary irreducible `q`.** `pole_order_contradiction` and its
  caller-facing form `cleared_relation_impossible` (`MachLib.PolyPoleCount`) close the
  count: for the cleared identity `(u'v − uv')·Q² = N·(P'Q − PQ')·u·v`, the left side carries
  `q^(k+l−1+2r)` while the right has **exact** order `r−1+k+l`, forcing `r ≤ 0`. The
  exactness is `ord_deriv_cross`, and it is what makes the count a strict inequality rather
  than a tautology — the companion `ord_cross_lower` is only a bound, and two bounds would
  prove nothing.

  **Two earlier scopings here were wrong and are superseded.** This section previously said
  the count closed only for `S` with a *genuine real pole*, and that the general case needed
  *real FTA* plus a division routine for quadratics. Neither holds: the count never inspects
  the degree of `q`, and `exists_irred_divisor'` produces an irreducible factor by minimal
  degree with no FTA. The real-pole restriction was an artifact of the available machinery,
  not of the mathematics.

  **What it rests on.** A twenty-module algebraic spine, built for this and reusable beyond
  it: canonical polynomials (`pnorm`, `PolyNF`), division with remainder (`pdivmod_spec`)
  and its coefficient-level identity (`pdivmod_identity`), degree additivity (`pmul_length`,
  `pmul_normal`), divisibility (`Pdvd`, `Pdvd_length`), extended Euclid with Bézout
  (`eea_bezout`) and the common-divisor half (`eea_divides`), **Euclid's lemma**
  (`euclid_lemma`), the `q`-adic factorisation with additivity and uniqueness (`ord_pmul`,
  `ord_unique`), cancellation (`peq_pmul_cancel_left`), and the derivative laws
  (`peq_pderiv_pmul`, `peq_pderiv_ppow`). **All of it is field-axiom-only** — 244 theorems
  under a whole-module `AxiomLedger` guard (invariant 7) that admits Lean core, the `Real`
  carrier and the field axioms and nothing else. Check it:
  ```
  lake env lean AxiomLedger.lean
  #   ⇒ "244 algebra-spine theorems field-axiom-checked (0 leaking)"
  ```

  **What it costs beyond the field axioms, named exactly once.** `DerivCoprime q r` — `q`
  does not divide `r·q'` — carried as a hypothesis, not discharged. It is *false* over `𝔽₂`
  (`q = X²+1`, `r = 2`) and true for irreducible `q` in characteristic zero; discharging it
  for `MachLib.Real` needs the order axioms and is deliberately left as a visible step.

  **Where the algebra stops.** Exactly one module sits outside the guard by design:
  `MachLib.PolyEvZero`, whose `pnorm_eq_nil_of_evZero` turns "vanishes on a tail" into "is
  the zero polynomial". That is false over a finite field, and its footprint is the ordered
  base and nothing more — no `HasDerivAt`, no `sorryAx`. Three facts this arc needed and
  could not have from the field axioms — polynomial extensionality, characteristic zero, and
  the infinitude of `ℝ` — are one obstruction wearing three faces: **the allow-list is the
  theory of fields, and fields can be finite.**

  **The composition is closed — as of 2026-08-23.** `minimal_relation_impossible`
  (`MachLib.BipevComposition`) threads every link into `False`: the relation on a tail, the
  cleared differentiated relation (`evRel_dcoeffs_ratFn`), elimination and descent
  (`elim_coeff_vanishes`), eventually-zero-is-zero (`pnorm_eq_nil_of_evZero`), the count's
  identity (`coeff_identity`), and `cleared_relation_impossible`. The three steps this
  section called "still not built" on 2026-08-21 — minimal degree, elimination,
  nontriviality — are built, and **none of them needed the tool its docstring predicted**:
  minimal degree took a `Nat` budget rather than well-founded recursion, and nontriviality
  took the count rather than a transcendence input.

  **And the top-level theorem, the same day.** `proper_relation_impossible`
  (`MachLib.BipevNonzeroCoeff`): for `S = P/Q` with an irreducible `q` dividing `Q` but not
  `P`, there is **no** eventually-holding polynomial relation `Σ pⱼ·exp(S x)ʲ = 0` whose
  leading coefficient is not eventually zero. Ten hypotheses, all structural — `q`
  irreducible, the two characteristic-zero conditions on `q`, `q ∤ P`, `q ∣ Q`, normality,
  `Q` nonzero as a polynomial and as a germ. No transcendence input appears anywhere in the
  chain. Check it:
  ```
  #print axioms MachLib.proper_relation_impossible
  #   ⇒ no sorryAx, no natCast, no Khovanskii axiom
  ```

  **And at the germ, not just the formula.** `germ_relation_impossible` (`MachLib.BipevGerm`)
  says the same for *any* `S` agreeing with `pev P · (1/pev Q)` on a tail. The transfer needs
  **no derivative**: `EvRel S Ls` mentions `S` exactly once, as `exp (S x)`, pointwise, so two
  functions agreeing on a tail have the same relations by intersecting two tails.
  `evRel_congr`'s footprint contains no `HasDerivAt` axiom of any kind, and the claim
  registry forbids all ten of them so it stays that way.

  **Four predictions, all overshot.** Every step of this arc was predicted, in a docstring or a
  commit, to need a heavier tool than it did: minimal degree (predicted well-founded
  recursion, took a `Nat` budget), nontriviality (predicted a transcendence input, took an
  order count), the nonzero lower coefficient (predicted minimality and a descent, took
  `exp_pos`), the germ transfer (predicted a derivative transfer, took two tails). The
  prediction is made while looking at the *statement*; the lighter tool only becomes visible
  once the surrounding lemmas exist.

  **The second characteristic-zero input, and its price.** The count needs `q ∤ (m−j)·1`.
  Over `Real` that is a *theorem*, not a hypothesis: `not_Pdvd_pnsum_one'` derives it from
  `zero_lt_one_ax` and `add_lt_add_left` alone — no `natCast`, no analysis. Over `𝔽₂` with
  `m−j = 2` it is false, the same boundary `DerivCoprime` sits on, reached by a different
  route.

  **The `S > 0` branch is separately untouched:** `F(S) = eˣ + log S` is not `exp` of
  anything, so `y' = S'·y` does not hold and the whole argument does not apply there.

- **The Khovanskii zero bound.** The project's most *distinctive* claim — Mathlib
  has no Khovanskii bound. Three things must be kept apart, because they are easy to
  conflate (an earlier version of this document conflated the first two):

  - **The shipped result is constructive — verified, not asserted.** The
    single-exponential bound `expPoly_khovanskii_bound` (zero count of a polynomial
    in `eˣ`) and the four safety-critical kernel applications built on it
    (Butler-Volmer electrode kinetics, the pharmacokinetic plasma kernel, the
    defibrillator discharge kernel, the critically-damped spring) depend on **no**
    classical-Khovanskii axiom and **no `sorry`**. `#print axioms` shows they rest
    only on the analytic base (the Rolle zero-counting corollary, the `HasDerivAt`
    rules, `exp_pos`, Real arithmetic and order) plus Lean's core — the *same*
    axiomatized base as the rest of the library (§4), not a citation of the theorem
    being proved. Check it:
    ```
    #print axioms MachLib.SingleExpKhovanskii.ExpPoly.expPoly_khovanskii_bound
    #   ⇒ no zero_count_bound_classical, no sorryAx
    ```
  - **Depth-2 is now proven too — unconditionally, as of `dda2a58`.** Between the
    single-exp bound and the cited general case sits the double-exponential chain
    (`x, eˣ, e^{eˣ}`). Its finite-zero bound `chain2_khovanskii_bound_unconditional`
    (`MachLib.ChainExp2NoZeros`) is **proven, not cited**: the reduction witness is
    *constructed* — a chain-aware nested descent measure, a polynomial-multiplier Rolle
    transfer, and an integrating-factor vehicle argument for the terminal case — so the
    only hypothesis is that the function is nonzero at *some* interior point (the honest
    minimum, since an identically-zero function has infinitely many zeros and no finite
    bound can exist). `#print axioms` shows no `zero_count_bound_classical` and no
    `sorryAx` — only the analytic base plus the honest Rolle corollary
    `zero_count_bound_by_deriv`. Check it:
    ```
    #print axioms MachLib.ChainExp2NoZeros.chain2_khovanskii_bound_unconditional
    #   ⇒ no zero_count_bound_classical, no sorryAx
    ```
    This is the first depth beyond 1 where the witness is *built* rather than assumed;
    depth-3+ would mirror the same arc with a deeper nested measure. It does **not**
    discharge the arbitrary-depth axiom below — that stands.
  - **Depth-2 finiteness is now EXPLICIT — `∃N` upgraded to `N(degrees)`, as of `cb20568`.**
    `chain2_khovanskii_bound_explicit` (`MachLib.ChainExp2NoZeros`) replaces the existential `∃N` with
    a concrete, computable degree functional:
    `zeros.length ≤ invPhi (Dx+2) (degreeY₁ p) (innerRank (Dx+2) p) (degreeY₀ p)` for every chain-2 `p`
    with `degreeX p ≤ Dx`. It is the *effective* (quantitative) Khovanskii bound at chain-2 — an
    explicit, level-indexed count (exponential in `degreeY₁`, inherent to this descent), not merely
    finiteness. It is the SAME well-founded recursion as the unconditional bound, re-run carrying a
    level-indexed budget `invPhi` in place of `∃N` (the naive invariant `levelBudget(degreeY₁, degreeY₀)`
    provably fails — a reduce grows `degreeY₀` — so the budget separates within-level counting from
    cross-level), with each arm discharged by machine-checked closure lemmas
    (`invPhi_reduce`/`invPhi_trim_any`) plus degree-monotonicity through both arms. `#print axioms`:
    ```
    #print axioms MachLib.ChainExp2NoZeros.chain2_khovanskii_bound_explicit
    #   ⇒ no zero_count_bound_classical, no sorryAx
    ```
    Arbitrary-depth *explicit* remains open: unlike depth-2/3 *finiteness*, the explicit depth step is a
    four-arm recursion over a `(depth)`-deep nested measure — a genuine build, not a mechanical mirror.
  - **The bound is now a usable TOOL — computable zero bounds for concrete kernels (`c6942b0`).**
    `khovBound p` (`MachLib.ChainExp2NoZeros`) states the bound in the *computable* syntactic degrees
    (`chain2_khovanskii_bound_syntactic` over-bounds the noncomputable `innerRank` via
    `innerRank_le_syntactic` + `invPhi_mono_ir`), so a concrete chain-2 EML kernel gets an explicit,
    machine-checked (`by decide`) ceiling on its zero-crossings. Worked: `e^(e^x) − x·e^x` crosses zero
    **≤ 47** times on any interval, `x·e^(e^x) − e^(2x)` **≤ 71** times (`khovBound_kernel*`) — an
    explicit bound on the oscillations/sign-changes of an iterated-exp transcendental, a safety-relevant
    quantity. sorryAx-free, `zero_count_bound_classical`-free.
  - **The general case is still cited — and it is an orphan.** A separate, more
    ambitious development — the bound for an *arbitrary* `PfaffianFunction` (general
    Pfaffian chains) — does rest on an axiom (`zero_count_bound_classical`) that
    **is** Khovanskii's classical 1991 theorem (Ch. 3, Thm. 1). That axiom
    *replaced* a prior `derivative_rank_lt` axiom which was **materially false on
    `exp_atom`** — and false for a structural reason, not a bug: the derivative of
    `eˣ` is `eˣ`, same chain, no rank decrease, so the naive "the derivative has
    smaller rank" induction simply does not hold. **No shipped result routes through
    this general axiom** (`#print axioms` on the applications confirms it); it is
    kept for a future generalization, not load-bearing today. Honest one-liner:
    *the single-exp and depth-2 Khovanskii bounds are proven (both dirty-axiom-free);
    the arbitrary-depth general-Pfaffian bound is still cited, and nothing that ships
    depends on the citation.*
- **The frontier explorations** (research notes, private) are deliberately framed
  as *lenses that compute a claim*, not proofs — e.g. restatements of open
  problems, never solutions. They are not part of what this library proves.

- **The EML depth/decay programme** (2026-08, `EMLLadderMeasure`, `EMLGermApproach`,
  `EMLHeightInterface`, `EMLHeightVsDepth`, `EMLDepth3Rung`, `EMLDecayLadderStep`, `EMLValueGap`) — the largest lane by
  volume this month, and the one most likely to be over-read, so its asterisks in full:

  **What is proved.** *(a)* `DecayFloor`, `GrowthEnvelope` and `EmlGermApproach` are **one
  obligation** written three ways — all three implications are theorems, and the obligations ledger
  reports the cycle as a single open debt rather than three. *(b)* The search for an induction
  parameter is **closed on both sides**: no `Nat`-valued measure on trees descending to both children
  can carry it, syntactically (`recipTree` costs two steps where a step buys one) or on germs (growth
  does not descend to the right child, unboundedly). *(c)* `decayFloorUpTo_three` — bounded rungs to
  depth 3, where the ceiling had been depth 2. *(d)* `decayFloor_of_ladderInputs` — the obligation
  itself follows from per-depth node bounds and lower envelopes, footprint-clean. *(e)* **the reduction
  to `LeadingMonomialFloor` was lossy, and is not any more**: syntactic exponential height
  `ehTree` bounds every `HeightModel` (`eh_le_ehTree`), so `eh_le_depth` factors through it, and
  `decayFloorByHeight_of_heightModel` draws a **strictly larger** conclusion from the *same* input —
  covering right spines of any length at level 1 where the depth-indexed form needs level 3. The
  strictness is exhibited, not assumed (`ehTree_lt_depth_witness`, `height_index_covers_more`), and
  the converse `DecayFloor → DecayFloorByHeight` is **not proved**.

  **What is open, and it is the whole thing.** `DecayFloor` is **not proved**. The bounded rungs do
  not approach it — depth 4 already needs an enumeration this project has measured and declined. The
  missing mathematical input is `EmlGermApproach`, whose *per-pair* form is a corollary of Hardy
  (1912) and whose open content is **the position of a single `∃ k`** (uniformity in the depth bound).
  **No axiom has been spent on it**, deliberately: an external mathematical input is not automatically
  an axiom, and until it is accepted without proof it is an obligation nobody has discharged.

  **Asterisks, stated rather than implied.** The impossibility result covers *local scalar growth
  descent through the syntax tree* — **not** every well-founded induction; lexicographic orders,
  ordinal ranks and non-structural arguments are untouched. *(e)* sharpens the **bound** and not the
  obligation: `LeadingMonomialFloor` is exactly as unproved as before, and a larger conclusion drawn
  from an input nobody has supplied moves nothing. `ehTree` also **overcounts** — it is syntactic, so
  it cannot see `exp (1 - log x) = e/x` collapse a level (`ehTree_overcounts_witness`) — which means
  even the sharpened chain `eh ≤ ehTree ≤ depth` has slack at both steps. The `HeightModel` interface proves
  nothing on its own: a height that is identically `0` satisfies every one of its closure axioms and
  refutes its floor property outright. And the growth envelope has **no eml-stdlib consumer** — that
  was pre-registered before the size-indexed version was built, and it held. Nothing in this lane is
  compiler-facing.

  Literature placement, with its own limits recorded (abstracts only, no paper read in full):
  `monogate-research/exploration/germ_approach_literature_2026_08_27/NOTE.md`.

- **`NegativeTranslationGrowingLeft` is DISCHARGED** (2026-08-28, `EMLNegTranslation`) — a separate
  obligation from the decay programme above, and **the only one to close in the 2026-08 arc**. The
  ledger went from six distinct open obligations to five.

  **What is proved.** A log-growth cap for depth ≤2 (`depth_le_two_log_growth_on_ray`, the mirror of
  the existing decay bound) squeezes the left child into `x ≤ A x ≤ x + 1`; inside that band a
  depth-≤2 tree is provably `var` (`band_depth_le_two_is_var`); the equation then pins the right
  child, and `negativeTranslationGrowingLeft_of_pinned` closes the reduction. No new axioms.

  **The residue fell the same day.** `pinnedRightChild_holds`: the equation pins `A₁` to within `1`
  of the germ `u = exp x − x − c` (the perturbation is at most linear against a target exponential in
  `u`, so one step of `exp` swallows it), and the five depth-≤1 forms are then exhausted — the three
  that cannot reach `exp x` die on the lower band, the two that can die on the `−x` term.

  **Asterisk on the discharge.** This is an impossibility theorem, so it is worth what its hypotheses
  are *individually* satisfiable for. `growingLeft_growth_hypothesis_satisfiable` ships with it: `var`
  satisfies the growth condition, so the emptied configuration space was not empty for a trivial
  reason. Footprints are base `Real` field axioms; no `sorryAx`, no analysis axioms.

  **And the asymmetry cell is closed.** `x_plus_neg_c_depth_exact_four` (same module, §6):
  `d_(0,∞)(x + c) = 4` for every `c < 0`, so with the positive side the value is **4 for every
  `c ≠ 0`**. §4's table had `{3, 4}` here and called it *"the first question this family raises that
  the existing machinery cannot answer"*; the machinery could, once the growing-left branch fell —
  the closure is pure assembly over `depth_le_two_exp_bounded_or_grows`, which had been in
  `EMLDepthTameness` all along with a docstring naming this exact use.

  **What stays asymmetric is the proof, not the value.** The positive side runs through
  `IntermediateBand` with `x < f x`; the negative side needs the mirror band, the depth-≤2 dichotomy,
  and a separate module for one of its two branches.

  **Where the sign finally enters.** `c < 0` is used **nowhere** in the reduction — the left child's
  collapse is a property of the band, not of the sign. It is consumed in exactly one place, `u_pos`,
  to know that `exp w − w − c > 0` so the equation can be inverted through `exp`. That is a thin use,
  and it means this proof does **not** explain the positive/negative asymmetry of `d(x + c)`; the
  asymmetry recorded in `EMLDepthTameness` §4 stands, now with one more of its branches closed.

---

## 8. The through-line

If there is a single contribution here it is a *method*, demonstrated rather than
asserted: **expose the invariant in the representation before reaching for
heavier automation** (the "decomposition before automation" doctrine —
`docs/proof_decomposition_before_automation.md`), and **prefer a provably
consistent, minimal axiom base over the illusion of zero axioms.** The axiom
audit in §4 is itself the cleanest case study of both: nothing was assumed away,
the redundant was removed, the primitive was named, and the load-bearing core was
proven non-vacuous. That is the part meant to be reproducible, critiqued, and
built on.
