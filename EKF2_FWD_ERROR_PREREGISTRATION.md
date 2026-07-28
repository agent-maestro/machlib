# Pre-registration — forward-error bound for the 2×2 EKF measurement update

**Status:** STATEMENT PRE-REGISTERED, NOT PROVEN. Posted **before the first tactic runs**.
**Date:** 2026-07-27. **Target file:** `foundations/MachLib/Ekf2MeasUpdateFwdError.lean` (does not
exist yet — this document is deliverable one).

Same discipline as the range-bearing anchor's pass criterion, and for the same reason: this bound has
four design decisions inside it, every one of them is easier to make honestly *now* than under proof
pressure, and afterwards every choice looks like it was made to flatter the result. So the
hypotheses, the domain constants, the scope and the grading are fixed here, and only the arithmetic
is left.

---

## 0. Why this piece

The three EKF silicon anchors all verify **AST → RTL**: bit-exact against a golden built from the
compiler's own arithmetic. That is the strongest available evidence for *emission* and is
constitutionally silent about whether that arithmetic is close to the mathematics. The scalar Kalman
flagship stood on three legs — optimality proven, forward error bounded, silicon. The EKF arc has
silicon, correctly claims **no** optimality (first-order), and has **PSD-safety already proven**
(`Matrix2JosephPSD.kalman2_joseph_psd`, for *any* gain, which is why it transfers to the EKF for
free). The missing leg is the forward-error bound. This is that leg.

---

## 1. What is bounded — and what is deliberately NOT

> **THE THEOREM COMPARES THE FIXED-POINT EKF UPDATE AGAINST THE IDEAL REAL-ARITHMETIC EKF UPDATE.**
> It does **not** bound distance to the true posterior, to the exact nonlinear Bayes filter, or to
> the truth. **Linearisation error is a modelling error, is a different quantity, and is not bounded
> here.**

That separation is the whole reason the bound is worth having. Fold the two together and the result
is unfalsifiable prose; keep them apart and each half is checkable.

Card language, fixed now: *"per-step implementation error ≤ ε; the linearisation error of the EKF
itself, and recursion-level growth, are separate and out of scope."*

---

## 2. The four design decisions

### D1 — SCOPE IS PER-STEP, and this is stated loudly, not buried

**Decision: bound ONE measurement update from an exact-real prior `(x, P)` and exact `z`. Not `N`.**

The scalar flagship's bound *was* recursive over N — but its recursion is **linear**. Here the state
error feeds the next linearisation point: `H` is a function of `x`, so an erroneous `x` produces an
erroneous `H`, which is a *different linear system* rather than the same one with a perturbed input.
An N-step bound therefore requires a stability/contraction hypothesis on the filter — which is
exactly the modelling-assumption category D-zero above commits to keeping out.

Per-step is fully honest and fully assembly. It composes later for anyone willing to add the
stability hypothesis **explicitly**, which is the only acceptable way to add it.

### D2 — COMPOSITION IS LIPSCHITZ, NOT ADDITIVE

The kernel certificates bound each kernel **at its exact input**. In the chain, `atan` receives an
already-erroneous quotient and `sqrt` an already-erroneous sum of squares. So each stage contributes

    (its own certified error)  +  (its derivative bound) × (upstream error)

and the derivative bounds are the amplification factors. The two transcendentals sit at **opposite
ends** of this, which is the structural fact the theorem is organised around:

| stage | amplification factor | domain needed? |
|---|---|---|
| `atan` | **\|atan′\| = 1/(1+u²) ≤ 1** everywhere | **NO — unconditional** |
| `sqrt` | `d√s/ds = 1/(2√s) = 1/(2r)` → **blows up at the origin** | **YES — `r ≥ r_min > 0`** |
| `x1/x0` | `‖∂(x1/x0)/∂x‖` ≤ `(1 + \|x1\|/\|x0\|)/\|x0\|` → blows up on the `x0 = 0` axis | **YES — `\|x0\| ≥ x0_min > 0`** |

`|atan′| ≤ 1` is **already machine-checked symbolically** — `sp.maximum` over the reals, not a
sampled claim (`hardware/modules/transcendental/tests/test_eml_atan_wide_certificate.py`). It was
machine-checked to license an *additive* certificate; here it is promoted to the **propagation
lemma**. Same fact, load-bearing in a second place.

**The sqrt domain hypothesis is not a weakness to minimise — it is the theorem being honest about the
physics.** Bearing is genuinely ill-conditioned at zero range; a bound that claimed otherwise would
be wrong. State the domain, then check the artifact satisfies it (§4).

### D3 — THE GAIN STAGE IS CONDITIONED BY λ_min(S) ≥ λ_min(R), AND THE PSD LEG SUPPLIES IT

Error through `S⁻¹` is controlled by `λ_min(S)`. The chain is entirely made of theorems already in
this repo:

```
  P is PSD                              -- kalman2_joseph_psd (any gain)      [BANKED]
  ⇒ H P Hᵀ is PSD                       -- psd2_congruence (G := H)           [BANKED]
  ⇒ S = H P Hᵀ + R  ⪰  R                -- psd2_add                          [BANKED]
  ⇒ λ_min(S) ≥ λ_min(R)                 -- a fixed, KNOWN constant from the anchor's own R
```

So the structural leg is not merely adjacent to the new bound — **it is load-bearing inside it**.
That is the zoo's theorems *composing* rather than coexisting, and it is the reason this is assembly.

**A fourth hypothesis falls out here and is registered now rather than discovered mid-proof.** The
bound needs the *computed* `S_hw` to be invertible too, and perturbation of an inverse requires a
smallness condition. Registered as an explicit hypothesis:

    h_wellcond : δ_S ≤ λ_min(R) / 2        ⇒  λ_min(S_hw) ≥ λ_min(R) / 2  ⇒  ‖S_hw⁻¹‖ ≤ 2/λ_min(R)

If `h_wellcond` turns out not to hold at the anchor's constants, **that is a finding and it gets
reported as one** — not a licence to weaken the hypothesis until it does.

### D4 — KERNEL BOUNDS ENTER AS HYPOTHESES, NEVER AS AXIOMS

`eml_atan_wide`'s certificate is **enumerated-plus-composition, not Lean-derived**. If its constant
entered MachLib as an axiom, the zero-new-axioms branding would die quietly in the first EKF file —
the exact failure mode the AxiomLedger exists to prevent, arriving through the front door.

Structure:

```lean
theorem ekf2_meas_update_fwd_error
    (h_sqrt  : ∀ s, s_min ≤ s → |sqrt_impl s - Real.sqrt s| ≤ c_sqrt)
    (h_atan  : ∀ u, |u| ≤ u_max → |atan_impl u - Real.arctan u| ≤ c_atan)
    (h_recip : ...)                       -- or reuse nr_reciprocal_2stage, already Lean-derived
    (h_dom   : ...) (h_wellcond : ...) (h_trunc : ...) :
    ‖x_hw⁺ - x_exact⁺‖ ≤ ε(c_sqrt, c_atan, c_recip, s, r_min, x0_min, λ_min R, ‖P‖, ‖y‖)
```

Proven **unconditionally as composition**; the *instantiation* at the certified constants is graded
separately. Zero new axioms stays literally true. And if the atan core certificate is ever upgraded
from enumerated to derived, **the theorem does not change — only its instantiation does.** That is
the two-layer rule expressed in the hypothesis structure itself.

**Precedent, not a novel dodge:** `KalmanUpdateFixedPoint.kalman_update_1d_fwd_error` already takes
the reciprocal's `Erec` as a hypothesis rather than importing a constant. This is that pattern, one
level up.

---

## 3. The statement skeleton

Ideal update (real arithmetic), `h(x) = (√(x0²+x1²), arctan(x1/x0))`, `H = ∂h/∂x`:

```
  y = z - h(x)        S = H P Hᵀ + R        K = P Hᵀ S⁻¹
  x⁺ = x + K y        P⁺ = (I-K) P (I-K)ᵀ + K R Kᵀ      (Joseph)
```

Error decomposition to be proven, each term named now so none can be quietly absorbed later:

| term | source | controlled by |
|---|---|---|
| `δ_h` | sqrt + atan + reciprocal + the qmuls feeding them | D2 Lipschitz chain, `r_min`, `x0_min` |
| `δ_H` | same kernels, differentiated form | D2, plus `r_min` twice (H has `1/r²`) |
| `δ_S` | `δ_H` through `H P Hᵀ`, plus `fxerr_dot2_fullwidth` | `‖P‖`, D2 |
| `δ_K` | `δ_S` through `S⁻¹`, plus `δ_H` | **D3**, `h_wellcond` |
| `δ_x⁺` | `‖K‖·δ_y + ‖y‖·δ_K` + final-add truncation | all of the above |

`ε` is the explicit fold of those. **Its numeric value is an OUTPUT of the proof and is deliberately
not predicted here** — pre-registering a target number would invite fitting the bound to it.

**Predict-step note:** `F` is constant-velocity, i.e. **linear**, for this model. The measurement
update is therefore the entire nonlinear story, and `fxerr_dot2_fullwidth` already covers the Joseph
side. The piece inventory is complete.

---

## 4. Domain constants — instantiated at the anchor, computed from the artifact

From `rb_ekf_arty/evidence/rb_golden_trajectory.txt` and `rtl/rb_ekf_anchor_top.v` (not estimated —
decoded):

| quantity | measured over the run | hypothesis to register | slack |
|---|---|---|---|
| range `r` | **5.000 … 5.491** | `r_min = 4.0` | 1.25× |
| `\|x0\|` | **2.041 … 3.000** | `x0_min = 2.0` | 1.02× |
| `λ_min(R)` | `R = diag(0.020004, 0.001999)` | **`0.001999`** (bearing) | exact |
| folded atan arg `u` | **0.409 … 0.750** | `u_max = 0.75` | exact |

`c_sqrt = 2⁻¹⁶ = 1.526e-05`, one-sided `[0, 1 ULP)`, **structural** (a restoring square root
truncates — no series, no iteration count).
`c_atan(u_max = 0.75) = 5.75e-03 rad`, **enumerated** over every representable Q16.16 point in the
interval.

**Two facts worth putting on the record now, because both are checkable and neither is flattering by
accident:**

1. **Every step folds.** `|x1/x0| ∈ [1.333, 2.448] > 1` at every evaluation, so the range-fold branch
   is the one exercised throughout — the anchor tests the path the theorem will bound, not the easy
   one.
2. **The atan argmax is the PRIOR, not the track.** `u = 0.750` at `x = (3, 4)` on step 0; every
   on-trajectory point is `u ≤ 0.463`. So the worst bearing error in the whole run occurs at the
   *initial linearisation point* and the filter immediately moves into a band ~10× better.
   Instantiating at the trajectory rather than at the kernel's worst case (`u ≤ 1`, `6.16e-02 rad`)
   is worth **10.7×** — and it is legitimate *only because* the domain is a stated hypothesis that
   the artifact is then checked against.

That check is what ties the legs together: **the anchor's 8-step trajectory becomes an instance of
the theorem's hypotheses**, so the silicon evidence and the bound stop being two separate claims
about the same design.

---

## 5. Grading, fixed in advance

| layer | grade |
|---|---|
| the composition theorem | **Lean-proven**, zero new axioms, sorryAx-free |
| `sqrt` kernel constant | **Structural** (truncating recurrence, every input) |
| `atan` kernel constant | **Enumerated** over all 131,073 Q16.16 points in the reduced interval |
| `reciprocal` constant | **Lean-derived** (`nr_reciprocal_2stage`) |
| `\|atan′\| ≤ 1` | **Exact, machine-checked symbolically** |
| the instantiated ε | **Lean composition over enumerated kernel certificates** — NOT "Lean-proven bound" |

That last row is the one that will be tempting to round up. It does not get rounded up.

---

## 6. Non-vacuity — how this is allowed to fail

A theorem that cannot fail is not evidence, and a bound that cannot be violated is not a bound. Three
checks ship **in the same commit** as the proof:

1. **Hypotheses satisfiable** — the anchor's trajectory satisfies `r_min`, `x0_min`, `u_max`,
   `h_wellcond`. If `h_wellcond` fails at these constants, **report it**; do not retune.
2. **Bound non-trivial** — `ε` must be small against the quantity it bounds. If `ε` exceeds the
   state magnitude the theorem is true and useless, and that is a **negative result to publish**, not
   a number to present.
3. **Bound actually binds** — a deliberately corrupted kernel constant must break the instantiation,
   and `ε` must be *above* the measured error of the golden trajectory. **`ε` below the measured
   error would mean the bound is unsound and the proof is wrong.** Both directions get asserted.

---

## 7. What is NOT being claimed, collected in one place

- not optimality — the EKF is first-order, MMSE does not carry, and it is not claimed anywhere
- not closeness to the true posterior or to the truth
- not an N-step or steady-state bound
- not a claim that `ε` is tight — it will be a sound worst-case fold, the same "sound but
  conservative" shape as `kalman_update_1d_fwd_error`, and it will say so
- not a Lean derivation of the atan constant — that stays enumerated until someone derives it

---

*Statement pre-registered. Assembly follows.*
