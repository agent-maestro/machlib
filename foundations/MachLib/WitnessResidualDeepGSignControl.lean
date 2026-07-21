import MachLib.WitnessResidualGrowthCompetitionDeepWitness

/-! # The sign-control tool for `growthCompetitionWitnessDeep`'s derivative

`growthCompetitionWitnessDeep`'s raw derivative works out (verified against a finite-difference
ground truth via `mpmath` before any of this was written) to `T'(x) = exp(x)·E·g(E)` where
`E := exp(exp x)`, `p := log c1`, `q := log c2`, and

  `g(E) := q/(E-q)² - exp(E/(E-p))·p/(E-p)²`.

Unlike `growthCompetitionWitness`'s analogous quantity (which cleared to a pure-algebra
quadratic), `g` retains a genuine transcendental factor `exp(E/(E-p))` — no amount of clearing
denominators removes it. `quadratic_neg_between`/`quadratic_pos_below_vertex` (built for the
quadratic case) don't apply here. This file builds the ANALOGOUS tool for `g` directly, using a
different (simpler, in some ways) technique: rather than exploiting convexity, it directly shows
each of `g`'s two terms is MONOTONIC (decreasing) in `E` — pure order theory, no derivatives of
`g` itself needed — then bounds `g` on an interval by evaluating each term at whichever endpoint
is worst-case for it.

**`term1(E) := q/(E-q)²` is decreasing** — cross-multiplication reduces this to `(E1-q)² ≤
(E2-q)²` for `q < E1 ≤ E2`, itself immediate from squaring preserving order on nonnegatives.

**`term2(E) := exp(E/(E-p))·p/(E-p)²` is decreasing** — via two sub-facts. `E/(E-p)` is decreasing
(`E_div_decreasing`, a direct cross-multiplication: `E2/(E2-p) ≤ E1/(E1-p) ⟺ E1·p ≤ E2·p`, true
from `E1≤E2, p>0`), so `exp(E/(E-p))` is decreasing (monotone composition). `p/(E-p)²` is
decreasing (same fact as `term1`, numerator `p` instead of `q`). The product of two nonnegative
decreasing functions is decreasing (`mul_le_mul'` applied in the appropriate direction).

**The interval tool**: for `E ∈ [E_lo, E_hi]` (with `E_lo` past both `p` and `q`), since `term1` is
decreasing (smallest at `E_hi`) and `term2` is decreasing (largest — most subtracted — at `E_lo`),
`g(E) ≥ term1(E_hi) - term2(E_lo)` throughout the WHOLE interval — a single inequality check at
the worst-case corner, no monotonicity of `g` itself required. `g_upper_bound_on_interval` is the
mirror, using the OTHER corner. Together these play exactly the role
`quadratic_neg_between`/`quadratic_pos_below_vertex` played for `growthCompetitionWitness`, for a
target function that genuinely can't be reduced to algebra.

**What remains, precisely, to close `growthCompetitionWitnessDeep`'s non-monotonicity** (not
attempted past this point in this round): (1) the `HasDerivAt` composition for `T_D` itself
(reusing `boundedNonConstantWitness_hasDerivAt` for both `A := BNCW c1` and `B := BNCW c2`, same
as `growthCompetitionWitness`'s own derivative work, but with one more layer of `HasDerivAt_comp`
for the extra `exp`); (2) an identity connecting the raw derivative to `exp(x)·E·g(E)` (harder
than `growthCompetitionWitness`'s `clear_denom_identity`, since the algebra can't fully clear —
this file's `g` already IS in cleared form, so the identity needed is "raw derivative equals
`exp(x)*E*g(E)` directly", not a further polynomial reduction); (3) concrete numeric axioms for
`c1=1.5, c2=2.0` bracketing not just `log(1.5)`/`log(2.0)` (as before) but ALSO `exp` at the
specific computed values `E/(E-p)` arising at the chosen witness `E`-points — genuinely NEW
numeric machinery beyond anything `growthCompetitionWitness` needed, since that tree's numeric
facts never needed to bound `exp` at anything other than `0` (trivial) and the log-bound
endpoints; (4) the `E`-to-`x` translation and final `strictMono`/`strictAnti` assembly (this part
IS a close structural match to `growthCompetitionWitness`'s own, reusable with parameter changes).
Piece (3) is the genuinely new difficulty — everything else is either already-built machinery or
a direct analogue of work already done. -/

namespace MachLib
namespace Real

theorem sq_le_sq_of_nonneg_le {a b : Real} (ha : 0 ≤ a) (hab : a ≤ b) : a * a ≤ b * b :=
  mul_le_mul' ha hab ha hab

theorem add_le_add {a b c d : Real} (h1 : a ≤ b) (h2 : c ≤ d) : a + c ≤ b + d := by
  have step1 : c + a ≤ c + b := add_le_add_left h1 c
  have step2 : b + c ≤ b + d := add_le_add_left h2 b
  have e1 : c + a = a + c := add_comm c a
  have e2 : c + b = b + c := add_comm c b
  rw [e1, e2] at step1
  exact le_trans step1 step2

/-- `q/(E-q)²` is decreasing in `E`, for `q < E1 ≤ E2`. -/
theorem term1_decreasing {q E1 E2 : Real} (hq : 0 < q) (hqE1 : q < E1) (hE1E2 : E1 ≤ E2) :
    q / ((E2 - q) * (E2 - q)) ≤ q / ((E1 - q) * (E1 - q)) := by
  have hE1q : 0 ≤ E1 - q := le_of_lt (sub_pos_of_lt hqE1)
  have hE1qle : E1 - q ≤ E2 - q := by
    have h := add_le_add_left hE1E2 (-q)
    have e1 : -q + E1 = E1 - q := by mach_mpoly [q, E1]
    have e2 : -q + E2 = E2 - q := by mach_mpoly [q, E2]
    rwa [e1, e2] at h
  have hsq : (E1 - q) * (E1 - q) ≤ (E2 - q) * (E2 - q) := sq_le_sq_of_nonneg_le hE1q hE1qle
  have hE1qpos : 0 < E1 - q := sub_pos_of_lt hqE1
  have hE1qsqpos : 0 < (E1 - q) * (E1 - q) := mul_pos hE1qpos hE1qpos
  exact div_le_div_pos (le_of_lt hq) (le_refl q) hE1qsqpos hsq

/-- `E/(E-p)` is decreasing in `E`, for `p < E1 ≤ E2`. Direct cross-multiplication:
`E2/(E2-p) ≤ E1/(E1-p) ⟺ E2*(E1-p) ≤ E1*(E2-p) ⟺ -E2*p ≤ -E1*p ⟺ E1*p ≤ E2*p`, true from
`E1≤E2, p>0`. -/
theorem E_div_decreasing {p E1 E2 : Real} (hp : 0 < p) (hpE1 : p < E1) (hE1E2 : E1 ≤ E2) :
    E2 / (E2 - p) ≤ E1 / (E1 - p) := by
  have hE1p : 0 < E1 - p := sub_pos_of_lt hpE1
  have hE2p : 0 < E2 - p := sub_pos_of_lt (lt_of_lt_of_le hpE1 hE1E2)
  rw [div_le_div_iff hE2p hE1p]
  have hcross : E2 * (E1 - p) = E1 * E2 - E2 * p := by mach_mpoly [E1, E2, p]
  have hcross2 : E1 * (E2 - p) = E1 * E2 - E1 * p := by mach_mpoly [E1, E2, p]
  rw [hcross, hcross2]
  have hstep : E1 * p ≤ E2 * p := mul_le_mul_of_nonneg_right hE1E2 (le_of_lt hp)
  exact sub_le_sub_left hstep (E1 * E2)

/-- `exp(E/(E-p))·p/(E-p)²` is decreasing in `E`, for `p < E1 ≤ E2` — product of two nonnegative
decreasing factors. -/
theorem term2_decreasing {p E1 E2 : Real} (hp : 0 < p) (hpE1 : p < E1) (hE1E2 : E1 ≤ E2) :
    Real.exp (E2 / (E2 - p)) * (p / ((E2 - p) * (E2 - p)))
      ≤ Real.exp (E1 / (E1 - p)) * (p / ((E1 - p) * (E1 - p))) := by
  have hexp_le : Real.exp (E2 / (E2 - p)) ≤ Real.exp (E1 / (E1 - p)) :=
    exp_monotone (E_div_decreasing hp hpE1 hE1E2)
  have hdiv_le : p / ((E2 - p) * (E2 - p)) ≤ p / ((E1 - p) * (E1 - p)) :=
    term1_decreasing hp hpE1 hE1E2
  have hexp_pos : 0 ≤ Real.exp (E2 / (E2 - p)) := le_of_lt (Real.exp_pos _)
  have hdiv_pos : 0 ≤ p / ((E2 - p) * (E2 - p)) := by
    have hE2p : 0 < E2 - p := sub_pos_of_lt (lt_of_lt_of_le hpE1 hE1E2)
    exact le_of_lt (div_pos_of_pos_pos hp (mul_pos hE2p hE2p))
  exact mul_le_mul' hexp_pos hexp_le hdiv_pos hdiv_le

/-- `g(E) := q/(E-q)² - exp(E/(E-p))·p/(E-p)²` is bounded BELOW throughout `[E_lo,E_hi]` by its
value at the "worst case" corner (`term1` at `E_hi`, `term2` at `E_lo`) — since `term1` is
decreasing (smallest at `E_hi`) and `term2` is decreasing (largest at `E_lo`, hence most
subtracted). Mirrors `quadratic_pos_below_vertex`'s role, without needing `g` itself to be
monotonic. -/
theorem g_lower_bound_on_interval {p q E_lo E_hi E : Real} (hp : 0 < p) (hq : 0 < q)
    (hpElo : p < E_lo) (hqElo : q < E_lo) (hloE : E_lo ≤ E) (hEhi : E ≤ E_hi) :
    q / ((E_hi - q) * (E_hi - q)) - Real.exp (E_lo / (E_lo - p)) * (p / ((E_lo - p) * (E_lo - p)))
      ≤ q / ((E - q) * (E - q)) - Real.exp (E / (E - p)) * (p / ((E - p) * (E - p))) := by
  have hqE : q < E := lt_of_lt_of_le hqElo hloE
  have ht1 : q / ((E_hi - q) * (E_hi - q)) ≤ q / ((E - q) * (E - q)) :=
    term1_decreasing (E1 := E) (E2 := E_hi) hq hqE hEhi
  have ht2 : Real.exp (E / (E - p)) * (p / ((E - p) * (E - p)))
      ≤ Real.exp (E_lo / (E_lo - p)) * (p / ((E_lo - p) * (E_lo - p))) :=
    term2_decreasing (E1 := E_lo) (E2 := E) hp hpElo hloE
  have h := add_le_add ht1 (neg_le_neg ht2)
  have e1 : q / ((E_hi - q) * (E_hi - q))
      + -(Real.exp (E_lo / (E_lo - p)) * (p / ((E_lo - p) * (E_lo - p))))
      = q / ((E_hi - q) * (E_hi - q))
        - Real.exp (E_lo / (E_lo - p)) * (p / ((E_lo - p) * (E_lo - p))) := (sub_def _ _).symm
  have e2 : q / ((E - q) * (E - q)) + -(Real.exp (E / (E - p)) * (p / ((E - p) * (E - p))))
      = q / ((E - q) * (E - q)) - Real.exp (E / (E - p)) * (p / ((E - p) * (E - p))) :=
    (sub_def _ _).symm
  rwa [e1, e2] at h

/-- Mirror: `g(E)` bounded ABOVE throughout `[E_lo,E_hi]` by its value at the OTHER corner. -/
theorem g_upper_bound_on_interval {p q E_lo E_hi E : Real} (hp : 0 < p) (hq : 0 < q)
    (hpElo : p < E_lo) (hqElo : q < E_lo) (hloE : E_lo ≤ E) (hEhi : E ≤ E_hi) :
    q / ((E - q) * (E - q)) - Real.exp (E / (E - p)) * (p / ((E - p) * (E - p)))
      ≤ q / ((E_lo - q) * (E_lo - q)) - Real.exp (E_hi / (E_hi - p)) * (p / ((E_hi - p) * (E_hi - p))) := by
  have ht1 : q / ((E - q) * (E - q)) ≤ q / ((E_lo - q) * (E_lo - q)) :=
    term1_decreasing (E1 := E_lo) (E2 := E) hq hqElo hloE
  have hpE : p < E := lt_of_lt_of_le hpElo hloE
  have ht2 : Real.exp (E_hi / (E_hi - p)) * (p / ((E_hi - p) * (E_hi - p)))
      ≤ Real.exp (E / (E - p)) * (p / ((E - p) * (E - p))) :=
    term2_decreasing (E1 := E) (E2 := E_hi) hp hpE hEhi
  have h := add_le_add ht1 (neg_le_neg ht2)
  have e1 : q / ((E - q) * (E - q))
      + -(Real.exp (E / (E - p)) * (p / ((E - p) * (E - p))))
      = q / ((E - q) * (E - q)) - Real.exp (E / (E - p)) * (p / ((E - p) * (E - p))) :=
    (sub_def _ _).symm
  have e2 : q / ((E_lo - q) * (E_lo - q))
      + -(Real.exp (E_hi / (E_hi - p)) * (p / ((E_hi - p) * (E_hi - p))))
      = q / ((E_lo - q) * (E_lo - q)) - Real.exp (E_hi / (E_hi - p)) * (p / ((E_hi - p) * (E_hi - p))) :=
    (sub_def _ _).symm
  rwa [e1, e2] at h

end Real
end MachLib
