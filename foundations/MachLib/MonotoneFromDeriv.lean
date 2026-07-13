import MachLib.Rolle
import MachLib.Ring
import MachLib.Differentiation

/-!
# Strict monotonicity from a derivative sign (Gate 2d, IFT gate — brick 1.a)

The uniqueness half of a monotonic implicit function: a function whose derivative is everywhere positive
(negative) on `[a,b]` is strictly increasing (decreasing). Derived from the witnessed Mean Value Theorem
`mean_value_theorem_ct` (`f b − f a = f'(c)(b−a)`) — no IVT, no continuity axiom, no new analytic axiom
(footprint `rolle_ct` through MVT). First tractable brick of the two-exponential IFT/parametrization gate;
generalizes the ad-hoc `exp_lt` monotonicity used in the worked instances.

The order-arithmetic goes through small helper lemmas with simple `Real` parameters (application atoms like
`f a` defeat both `mach_ring`'s AC and `mach_mpoly`'s atom parser).
-/

namespace MachLib
namespace Real

private theorem mfd_sub_pos {x y : Real} (h : x < y) : 0 < y - x := by
  have h2 := add_lt_add_left h (-x)
  rw [show -x + x = 0 from by mach_mpoly [x], show -x + y = y - x from by mach_mpoly [x, y]] at h2
  exact h2

private theorem mfd_lt_of_sub {x y : Real} (h : 0 < y - x) : x < y := by
  have h2 := add_lt_add_left h x
  rw [add_zero, show x + (y - x) = y from by mach_mpoly [x, y]] at h2
  exact h2

private theorem mfd_neg_pos {x : Real} (h : x < 0) : 0 < -x := by
  have h2 := add_lt_add_left h (-x)
  rw [add_zero, show -x + x = 0 from by mach_mpoly [x]] at h2
  exact h2

private theorem mfd_lt_of_neg {x y : Real} (h : -x < -y) : y < x :=
  mfd_lt_of_sub (by
    have hp := mfd_sub_pos h
    rwa [show -y - -x = x - y from by mach_mpoly [x, y]] at hp)

/-- **Strictly increasing from a positive derivative.** `f a < f b`. Via MVT. -/
theorem strictMono_of_deriv_pos (f : Real → Real) (a b : Real) (hab : a < b)
    (hdiff : ∀ c : Real, a ≤ c → c ≤ b → ∃ f' : Real, HasDerivAt f f' c)
    (hpos : ∀ c f' : Real, a ≤ c → c ≤ b → HasDerivAt f f' c → 0 < f') :
    f a < f b := by
  obtain ⟨c, f', hac, hcb, hderiv, heq⟩ := mean_value_theorem_ct f a b hab hdiff
  have hprod : (0 : Real) < f' * (b - a) :=
    mul_pos (hpos c f' (le_of_lt_r hac) (le_of_lt_r hcb) hderiv) (mfd_sub_pos hab)
  rw [← heq] at hprod
  exact mfd_lt_of_sub hprod

/-- **Strictly decreasing from a negative derivative.** `f b < f a`. Reduces to the positive case for `−f`. -/
theorem strictAnti_of_deriv_neg (f : Real → Real) (a b : Real) (hab : a < b)
    (hdiff : ∀ c : Real, a ≤ c → c ≤ b → ∃ f' : Real, HasDerivAt f f' c)
    (hneg : ∀ c f' : Real, a ≤ c → c ≤ b → HasDerivAt f f' c → f' < 0) :
    f b < f a := by
  have hmono : (fun x => -f x) a < (fun x => -f x) b := by
    apply strictMono_of_deriv_pos (fun x => -f x) a b hab
    · intro c hca hcb
      obtain ⟨f', hf'⟩ := hdiff c hca hcb
      exact ⟨-f', HasDerivAt_neg f f' c hf'⟩
    · intro c f'' hca hcb hderiv
      obtain ⟨f', hf'⟩ := hdiff c hca hcb
      rw [HasDerivAt_unique (fun x => -f x) f'' (-f') c hderiv (HasDerivAt_neg f f' c hf')]
      exact mfd_neg_pos (hneg c f' hca hcb hf')
  exact mfd_lt_of_neg hmono

end Real
end MachLib
