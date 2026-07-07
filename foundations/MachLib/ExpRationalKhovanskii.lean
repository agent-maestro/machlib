import MachLib.PolynomialRootCount
import MachLib.SturmNonOscillation
import MachLib.FieldLemmas

/-!
# Constructive Khovanskii for exp+rational chains — Brick 1 (rational base case)

Track B of retiring `PfaffianFunction.zero_count_bound_classical` from the
sin/cos any-depth barrier: extend the constructive Khovanskii step to admit a
rational (`1/x`) generator, which is the one non-exp-type generator EML's
exp+log chains need. Map + plan:
`monogate-research/exploration/eml_exp_rational_khovanskii_extend_scoping_2026_07_07/FINDINGS.md`.

The `1/x` level does not need a Rolle/integrating-factor argument: a Pfaffian
function over the `1/x` bottom is *rational* in `x`, so its zeros are the zeros
of a numerator polynomial — bounded by degree. This file lays the abstract
content of that step, `poly_root_count_bound`-only, division-free:

  **if every zero of `f` on `(a,b)` is also a zero of a not-identically-zero
  polynomial `q`, then `f` has at most `degreeUpper q` zeros there.**

For the `1/x` case, `f z = q z / zᴷ` and (on `z > 0`) `f z = 0 → q z = 0` — the
caller supplies that implication (Brick 1b: the `MultiPoly`-in-`(x,1/x)` →
numerator encoding). This brick is the root-count core the descent's new bottom
case will cite.
-/

namespace MachLib
namespace PolynomialRootCount

open MachLib.Real
open MachLib.PolynomialEvidence

/-- **Brick 1 — zero-count bounded by a dominating polynomial.** If, on `(a,b)`,
every zero of `f` is a zero of a polynomial `q` that is not identically zero,
then any list of distinct zeros of `f` in `(a,b)` has length `≤ degreeUpper q`.
The rational base case (`f = q / xᴷ`, zeros preserved on `x>0`) is the intended
instance; the numerator relation is discharged by the caller via `hsub`. -/
theorem zero_count_bound_of_subset_poly
    (q : Poly) (f : Real → Real) (a b : Real) (hab : a < b)
    (hne : ∃ x : Real, Poly.eval q x ≠ 0)
    (hsub : ∀ z : Real, a < z → z < b → f z = 0 → Poly.eval q z = 0) :
    ∀ zeros : List Real,
      zeros.Nodup →
      (∀ z ∈ zeros, a < z ∧ z < b ∧ f z = 0) →
      zeros.length ≤ degreeUpper q := by
  intro zeros hnd hz
  refine poly_root_count_bound q a b hab hne zeros hnd (fun z hzmem => ?_)
  obtain ⟨ha, hb, hfz⟩ := hz z hzmem
  exact ⟨ha, hb, hsub z ha hb hfz⟩

end PolynomialRootCount

/-! ## Brick 2 — the reciprocal generator's coherence

The one non-exp generator EML needs is `1/x`, whose Pfaffian relation is
`y' = −y²` (`(1/x)' = −(1/x)²`). This is the coherence the extended descent's
bottom level requires; the `−(y·y)` form matches `MultiPoly.eval (−varY²)` along
a chain with `y = 1/x`. -/

open MachLib.Real

/-- **Brick 2 — reciprocal coherence.** On `x > 0`,
`(1/x)' = −((1/x)·(1/x))` — the `1/x` generator satisfies its Pfaffian relation
`y' = −y²`. Built from `HasDerivAt_inv` (reciprocal rule) with the value bridged
from `−1/(x·x)` to `−((1/x)·(1/x))` via `one_div_mul_one_div` + `neg_div`. -/
theorem reciprocal_hasDerivAt (x : Real) (hx : 0 < x) :
    HasDerivAt (fun x => 1 / x) (-((1 / x) * (1 / x))) x := by
  have hx0 : x ≠ 0 := ne_of_gt hx
  have h : HasDerivAt (fun y => 1 / y) (-1 / (x * x)) x := by
    simpa using HasDerivAt_inv (fun y => y) 1 x hx0 (HasDerivAt_id x)
  have hb : (-1 / (x * x) : Real) = -((1 / x) * (1 / x)) := by
    rw [one_div_mul_one_div hx, neg_div (ne_of_gt (mul_pos hx hx))]
  rw [hb] at h
  exact h

end MachLib
