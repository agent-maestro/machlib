import MachLib.WitnessResidualGrowthCompetitionWitness
import MachLib.WitnessResidualQuadraticConvexity
import MachLib.MonotoneFromDeriv

/-! # `growthCompetitionWitness`'s actual derivative, connected to the quadratic tools

`WitnessResidualQuadraticConvexity.lean` built the pure-algebra half of the non-monotonicity
argument (the two "sign of an upward quadratic" tools). This file builds the OTHER half: the real
derivative of `T(x) := exp(A(x)) - B(x)` (`A := boundedNonConstantWitness c1`, `B :=
boundedNonConstantWitness c2`), obtained via the codebase's `HasDerivAt` composition rules, and an
identity connecting its RAW (composition-rule) value to the quadratic `S(E)`'s numerator after
clearing denominators.

**The composition step**, `growthCompetitionWitness_hasDerivAt`: `T = exp∘A - B`, so `T' =
exp(A(z))·A'(z) - B'(z)` via `HasDerivAt_comp` (for `exp∘A`) then `HasDerivAt_sub`. Both `A'(z)`
and `B'(z)` are exactly the RAW forms `boundedNonConstantWitness_hasDerivAt` already supplies —
this file adds no new derivative axiom usage, only composes existing ones.

**The clearing step.** The raw value `exp(A(z))·A'(z) - B'(z)` is a rational function of `E :=
exp(exp z)` (with denominators `(E-p)` and `(E-q)`, `p := log c1`, `q := log c2`) — NOT yet in the
polynomial form `quadratic_neg_between`/`quadratic_pos_below_vertex` need. Rather than doing
messy in-place fraction algebra, this file multiplies through by the (positive) denominator
`(E-p)²·(E-q)` using three small "multiplied-out" facts as building blocks:

- `exp_A_mul_denom`: `exp(A(z))·(E-p) = E` (from `exp_sub` + `exp_log`, since `exp(A(z)) =
  exp(exp z)/exp(log(E-p)) = E/(E-p)`, then clearing the `1/(E-p)` via `mul_inv`).
- `deriv_A_mul_denom`: `A'(z)·(E-p) = -(exp z · log c)` — a standalone extraction of the `hprod`
  step buried inside `boundedNonConstantWitness_deriv_neg`'s own proof (same technique, generalized
  so it can be reused for BOTH `c1` and `c2` here).
- `clear_denom_identity`: a fully abstract (7-atom) algebra lemma taking exactly these three
  "multiplied out" equations as hypotheses and concluding the FULL cleared identity — proved by
  substituting each hypothesis in at the right point via `rw`, with `mach_mpoly` closing the pure
  polynomial regrouping between substitutions. No fraction ever appears inside `mach_mpoly`'s view;
  it only ever sees polynomial identities in atoms `U, V, W, E, p, q, ez`.

The result, `growthCompetitionWitness_deriv_clear_denom`: `T'(z)·(E-p)²·(E-q) = exp(z)·quad(E)`,
where `quad` is EXACTLY the quadratic from `WitnessResidualQuadraticConvexity.lean`. Cross-checked
numerically (6 random `(c1,c2,x)` triples, matching to float precision) before writing any of the
Lean above — this is the KEY bridge: since `exp(z) > 0` and `(E-p)²·(E-q) > 0` (both established
elsewhere), `T'(z)`'s sign matches `quad(E)`'s sign exactly, turning a transcendental
derivative-sign question into the pure-algebra question the two tools already answer. -/

namespace MachLib
namespace Real

/-- `T(w) := exp(A(w)) - B(w)` in fully-unfolded raw-lambda form, matching
`boundedNonConstantWitness_hasDerivAt`'s own domain (so the composition rules apply directly,
with no `.eval`/tree-structure bookkeeping needed at this stage — that happens later, at the point
this gets applied to `growthCompetitionWitness.eval`). -/
theorem growthCompetitionWitness_hasDerivAt (c1 c2 z : Real)
    (hApos : 0 < Real.exp (Real.exp z) - Real.log c1)
    (hBpos : 0 < Real.exp (Real.exp z) - Real.log c2) :
    HasDerivAt
      (fun w => Real.exp (Real.exp w - Real.log (Real.exp (Real.exp w) - Real.log c1))
        - (Real.exp w - Real.log (Real.exp (Real.exp w) - Real.log c2)))
      (Real.exp (Real.exp z - Real.log (Real.exp (Real.exp z) - Real.log c1))
          * (Real.exp z - 1 / (Real.exp (Real.exp z) - Real.log c1) * (Real.exp (Real.exp z) * Real.exp z))
        - (Real.exp z - 1 / (Real.exp (Real.exp z) - Real.log c2) * (Real.exp (Real.exp z) * Real.exp z)))
      z := by
  have hA := boundedNonConstantWitness_hasDerivAt c1 z hApos
  have hB := boundedNonConstantWitness_hasDerivAt c2 z hBpos
  have hExpA := HasDerivAt_comp Real.exp
    (fun w => Real.exp w - Real.log (Real.exp (Real.exp w) - Real.log c1))
    (Real.exp z - 1 / (Real.exp (Real.exp z) - Real.log c1) * (Real.exp (Real.exp z) * Real.exp z))
    (Real.exp (Real.exp z - Real.log (Real.exp (Real.exp z) - Real.log c1)))
    z hA (HasDerivAt_exp _)
  exact HasDerivAt_sub _ _ _ _ z hExpA hB

/-- `exp(A(z))·(E-p) = E`. Via `exp_sub` (`exp(exp z - log(E-p)) = exp(exp z)/exp(log(E-p))`)
then `exp_log` (`exp(log(E-p)) = E-p`, needing `E-p>0`), then clearing the resulting `1/(E-p)`
via `mul_inv`. -/
theorem exp_A_mul_denom (c z : Real) (hpos : 0 < Real.exp (Real.exp z) - Real.log c) :
    Real.exp (Real.exp z - Real.log (Real.exp (Real.exp z) - Real.log c))
      * (Real.exp (Real.exp z) - Real.log c) = Real.exp (Real.exp z) := by
  have h1 : Real.exp (Real.exp z - Real.log (Real.exp (Real.exp z) - Real.log c))
      = Real.exp (Real.exp z) / Real.exp (Real.log (Real.exp (Real.exp z) - Real.log c)) :=
    exp_sub _ _
  have h2 : Real.exp (Real.log (Real.exp (Real.exp z) - Real.log c))
      = Real.exp (Real.exp z) - Real.log c := exp_log hpos
  rw [h1, h2, div_def _ _ (ne_of_gt hpos), mul_assoc]
  have h3 : (1 / (Real.exp (Real.exp z) - Real.log c)) * (Real.exp (Real.exp z) - Real.log c) = 1 := by
    rw [mul_comm]; exact mul_inv _ (ne_of_gt hpos)
  rw [h3, mul_one_ax]

/-- **Standalone extraction** of the `hprod` step buried inside
`boundedNonConstantWitness_deriv_neg`'s own proof — exposed here as its own reusable lemma (same
proof, unchanged) so it can serve BOTH `c1` and `c2` in the `growthCompetitionWitness` context. -/
theorem deriv_A_mul_denom (c z : Real) (hpos : 0 < Real.exp (Real.exp z) - Real.log c) :
    (Real.exp z - 1 / (Real.exp (Real.exp z) - Real.log c) * (Real.exp (Real.exp z) * Real.exp z))
      * (Real.exp (Real.exp z) - Real.log c) = -(Real.exp z * Real.log c) := by
  have hne : Real.exp (Real.exp z) - Real.log c ≠ 0 := ne_of_gt hpos
  have hinv : (1 / (Real.exp (Real.exp z) - Real.log c)) * (Real.exp (Real.exp z) - Real.log c) = 1 := by
    rw [mul_comm]; exact mul_inv _ hne
  have step1 : (Real.exp z
        - 1 / (Real.exp (Real.exp z) - Real.log c) * (Real.exp (Real.exp z) * Real.exp z))
      * (Real.exp (Real.exp z) - Real.log c)
      = Real.exp z * (Real.exp (Real.exp z) - Real.log c)
        - (1 / (Real.exp (Real.exp z) - Real.log c) * (Real.exp (Real.exp z) * Real.exp z))
          * (Real.exp (Real.exp z) - Real.log c) := by mach_ring
  rw [step1]
  have step2 : (1 / (Real.exp (Real.exp z) - Real.log c) * (Real.exp (Real.exp z) * Real.exp z))
      * (Real.exp (Real.exp z) - Real.log c)
      = (1 / (Real.exp (Real.exp z) - Real.log c) * (Real.exp (Real.exp z) - Real.log c))
        * (Real.exp (Real.exp z) * Real.exp z) := by
    rw [mul_assoc, mul_comm (Real.exp (Real.exp z) * Real.exp z)
      (Real.exp (Real.exp z) - Real.log c), ← mul_assoc]
  rw [step2, hinv]
  have step3 : Real.exp z * (Real.exp (Real.exp z) - Real.log c)
      - 1 * (Real.exp (Real.exp z) * Real.exp z) = -(Real.exp z * Real.log c) := by mach_ring
  exact step3

/-- Fully abstract clearing identity: given the three "multiplied out" facts as hypotheses,
the cleared polynomial identity follows by substituting each in turn (via `rw`) and closing the
pure-polynomial regrouping between substitutions with `mach_mpoly`. -/
theorem clear_denom_identity {U V W E p q ez : Real}
    (hexpAmul : U * (E - p) = E)
    (hAmul : V * (E - p) = -(ez * p))
    (hBmul : W * (E - q) = -(ez * q)) :
    (U * V - W) * (E - p) * (E - p) * (E - q) = ez * ((q - p) * E * E - p * q * E + p * p * q) := by
  have step1 : (U * V - W) * (E - p) = U * (E - p) * V - W * (E - p) := by mach_mpoly [U, V, W, E, p]
  rw [hexpAmul] at step1
  have step2 : (U * V - W) * (E - p) * (E - p) = E * (V * (E - p)) - W * (E - p) * (E - p) := by
    rw [step1]; mach_mpoly [E, V, W, p]
  rw [hAmul] at step2
  have step3 : (U * V - W) * (E - p) * (E - p) * (E - q)
      = E * (-(ez * p)) * (E - q) - (W * (E - q)) * (E - p) * (E - p) := by
    rw [step2]; mach_mpoly [E, ez, p, W, q, V]
  rw [hBmul] at step3
  rw [step3]
  mach_mpoly [E, ez, p, q]

/-- **The full cleared-denominator identity for `growthCompetitionWitness`'s raw derivative.**
`T'(z)·(E-p)²·(E-q) = exp(z)·quad(E)`, where `T'(z)` is the RAW (composition-rule) derivative
value from `growthCompetitionWitness_hasDerivAt`, `E := exp(exp z)`, `p := log c1`, `q := log c2`,
and `quad(E) := (q-p)·E² - pq·E + p²q` — the SAME quadratic `quadratic_neg_between` and
`quadratic_pos_below_vertex` reason about. Numerically cross-checked (6 random `(c1,c2,x)`
triples, all matching to float precision) before this Lean derivation. -/
theorem growthCompetitionWitness_deriv_clear_denom (c1 c2 z : Real)
    (hApos : 0 < Real.exp (Real.exp z) - Real.log c1)
    (hBpos : 0 < Real.exp (Real.exp z) - Real.log c2) :
    (Real.exp (Real.exp z - Real.log (Real.exp (Real.exp z) - Real.log c1))
        * (Real.exp z - 1 / (Real.exp (Real.exp z) - Real.log c1) * (Real.exp (Real.exp z) * Real.exp z))
      - (Real.exp z - 1 / (Real.exp (Real.exp z) - Real.log c2) * (Real.exp (Real.exp z) * Real.exp z)))
      * (Real.exp (Real.exp z) - Real.log c1) * (Real.exp (Real.exp z) - Real.log c1)
      * (Real.exp (Real.exp z) - Real.log c2)
      = Real.exp z * ((Real.log c2 - Real.log c1) * Real.exp (Real.exp z) * Real.exp (Real.exp z)
          - Real.log c1 * Real.log c2 * Real.exp (Real.exp z)
          + Real.log c1 * Real.log c1 * Real.log c2) :=
  clear_denom_identity (exp_A_mul_denom c1 z hApos) (deriv_A_mul_denom c1 z hApos)
    (deriv_A_mul_denom c2 z hBpos)

end Real
end MachLib
