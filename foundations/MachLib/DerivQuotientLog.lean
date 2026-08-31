import MachLib.Differentiation
import MachLib.FieldLemmas

/-!
# Two derivative rules the corpus was missing: `log ∘ S` and a quotient

Both checked absent **by statement** — no theorem in `MachLib/` concludes
`HasDerivAt (fun t => log (S t)) _ _` or `HasDerivAt (fun t => N t / D t) _ _`.

* **`logComp_hasDerivAt`** — the logarithmic derivative, `(log ∘ S)′ = S′/S` where `S > 0`. This is
  the object the whole `¬ RatGerm (log ∘ S)` route turns on: a rational function's logarithmic
  derivative having a *rational primitive* is what `no_rational_logarithm` refuses.
* **`div_hasDerivAt`** — the quotient rule. `Differentiation` ships `HasDerivAt_inv` (the reciprocal)
  but never composes it with the product rule, so every quotient derivative in the corpus has been
  open-coded from those two.

The reciprocal-to-quotient step needs one field identity, `D·(1/(D·D)) = 1/D`, proved by cancelling a
factor rather than by unfolding `1/·` twice — which is the step that makes the rest `mach_mpoly` over
a single atom.
-/

namespace MachLib

open Real

/-- **The logarithmic derivative.** `(log ∘ S)′ = S′/S` where `S > 0`. -/
theorem logComp_hasDerivAt {S : Real → Real} {s x : Real}
    (hS : HasDerivAt S s x) (hpos : 0 < S x) :
    HasDerivAt (fun t => log (S t)) (s / S x) x := by
  have h := HasDerivAt_comp Real.log S s (1 / S x) x hS (HasDerivAt_log_pos (S x) hpos)
  have e : (1 : Real) / S x * s = s / S x := by
    rw [div_def s (S x) (ne_of_gt hpos), div_def 1 (S x) (ne_of_gt hpos)]
    mach_mpoly [s, 1 / S x]
  rw [e] at h
  exact h

/-- **The quotient rule**, from the product and reciprocal rules. -/
theorem div_hasDerivAt {N D : Real → Real} {n d x : Real}
    (hN : HasDerivAt N n x) (hD : HasDerivAt D d x) (hDne : D x ≠ 0) :
    HasDerivAt (fun t => N t / D t)
      ((n * D x - N x * d) / (D x * D x)) x := by
  have hinv := HasDerivAt_inv D d x hDne hD
  have hprod := HasDerivAt_mul N (fun t => 1 / D t) n (-d / (D x * D x)) x hN hinv
  have hfun : (fun t => N t * (1 / D t)) = (fun t => N t / D t) := by
    funext t
    by_cases hz : D t = 0
    · rw [hz, div_zero, div_zero]
      mach_ring
    · rw [div_def (N t) (D t) hz]
  rw [hfun] at hprod
  have hDD : D x * D x ≠ 0 := mul_ne_zero hDne hDne
  -- `D x · (1/(D x · D x)) = 1/D x`, by cancelling one factor
  have hkey : D x * (1 / (D x * D x)) = 1 / D x := by
    refine mul_left_cancel hDne ?_
    rw [show D x * (D x * (1 / (D x * D x))) = (D x * D x) * (1 / (D x * D x)) from by mach_ring,
        mul_inv (D x * D x) hDD, mul_inv (D x) hDne]
  have e : n * (1 / D x) + N x * (-d / (D x * D x))
      = (n * D x - N x * d) / (D x * D x) := by
    rw [div_def (-d) (D x * D x) hDD, div_def (n * D x - N x * d) (D x * D x) hDD, ← hkey]
    mach_mpoly [n, D x, N x, d, 1 / (D x * D x)]
  rw [e] at hprod
  exact hprod

end MachLib
