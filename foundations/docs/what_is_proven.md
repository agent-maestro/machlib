# MachLib — what is proven, what it rests on, what is open

A reader's front door. Its only job is to say, precisely and checkably, what
this library establishes, what those results depend on, and where the seams are.
If something here reads as a claim you can't reproduce in a few commands, that's
a bug in this document — tell us.

Scope note: this covers the **verified-numerics** core and the **axiom base**.
Other lanes (the Khovanskii zero bound, the larger frontier explorations) are
summarised honestly at the end with their asterisks named, not hidden.

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
2. **Controller → closed loop.** `fxpid_trunc_lt_3ulp` bounds the *controller's
   multiply-add*. `pid_trajectory_from_bits` needs a bound on the *closed-loop
   state update*, `|xc (k+1) − (c·xc k + d)| ≤ ε`, which it takes as a
   **hypothesis** with `ε` universally quantified. Nothing derives one from the
   other; that needs a plant model this corpus does not yet have.

Inspect the proof term and the gap is immediate — `pid_trajectory_from_bits`
elaborates to `fun … => affine_trajectory_bound …`, mentioning no bit-level
object at all. The name is aspirational.

**Why this matters more than a wording fix.** The composition — implementation
error *derived from the shipped datapath* and *consumed by* a physical-system
guarantee — is the programme's most distinctive claim, and the thing outside
readers identified as potentially publishable.

**Status: one join closed, one open.** The remaining gap is join 2, and it is a
missing *modelling layer* rather than a missing lemma: it needs a plant model
relating the controller's multiply-add to the closed-loop state update. Until
that exists the honest statement is **two solid halves and one of two bridges**,
and `pid_trajectory_from_bits` should not be described as carrying a bit-level
quantity — it still quantifies `ε` universally.

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
model — are **axioms** here. As of 2026-06-27 the trusted base is **260 axioms**.
But that one number lumps two very different kinds of axiom together, and the
distinction is the whole point (tier list in **(c)**). Three things make the base
honest rather than hand-wavy:

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
count of 260 hides the axioms that actually matter. They split cleanly, and a reader
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
