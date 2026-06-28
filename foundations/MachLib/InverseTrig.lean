import MachLib.Differentiation
import MachLib.Rolle
import MachLib.FPModel
import MachLib.FieldLemmas

/-!
# `arctan` — declared as a primitive, its 1-Lipschitz bound DERIVED via MVT

`atan` is not in MachLib's analytic base, so it is declared here as a primitive function
(like `sin`/`cos`/`sinh`) with its defining facts `atan 0 = 0` and its derivative
`atan' = 1/(1+x²)` as axioms — the same *derivative-of-a-primitive* category as
`HasDerivAt_sin`/`HasDerivAt_cos` (which are axioms). **This file adds those 3 axioms**;
everything below is then *derived* (no further axioms):

* `atan` is **1-Lipschitz** (`atan' = 1/(1+x²) ≤ 1`), via MVT — like `sin`/`cos`/`tanh`;
* `|atan x| ≤ |x|` (1-Lipschitz from `atan 0 = 0`), so `atan` *preserves* a magnitude
  bound — no need for a `π/2` constant.

`asin` (`arcsin`) is left out: its derivative `1/√(1−x²)` is unbounded near `±1`, so it
needs a domain guard — the genuinely harder case for a single stdlib kernel.
-/

namespace MachLib.Real

/-- `arctan`, a primitive function. -/
axiom atan : Real → Real

/-- `arctan 0 = 0` (defining). -/
axiom atan_zero : atan 0 = 0

/-- `arctan' = 1/(1+x²)` (the derivative-of-primitive axiom, like `HasDerivAt_sin`). -/
axiom HasDerivAt_atan (x : Real) : HasDerivAt atan (1 / (1 + x * x)) x

/-- `|atan'| ≤ 1` (since `1 + x² ≥ 1`). -/
theorem atan_deriv_le_one (x : Real) : abs (1 / (1 + x * x)) ≤ 1 := by
  have hge1 : (1 : Real) ≤ 1 + x * x := le_add_of_nonneg_right (mul_self_nonneg x)
  have hpos : 0 < 1 + x * x := lt_of_lt_of_le zero_lt_one_ax hge1
  rw [abs_of_nonneg (one_div_nonneg_of_pos hpos)]
  exact div_le_one_of_le_of_pos hpos hge1

/-- **`atan` is 1-Lipschitz** — `|atan a − atan b| ≤ |a − b|`, via MVT. -/
theorem atan_lipschitz (a b : Real) : abs (atan a - atan b) ≤ abs (a - b) := by
  have step : ∀ p q : Real, p < q → abs (atan q - atan p) ≤ q - p := by
    intro p q hpq
    obtain ⟨c, f', _, _, hdc, hval⟩ :=
      mean_value_theorem atan p q hpq (fun c _ _ => ⟨1 / (1 + c * c), HasDerivAt_atan c⟩)
    rw [hval, HasDerivAt_unique atan f' (1 / (1 + c * c)) c hdc (HasDerivAt_atan c),
        abs_mul, abs_of_nonneg (le_of_lt (sub_pos_of_lt hpq))]
    exact le_trans (mul_le_mul_of_nonneg_right (atan_deriv_le_one c)
      (le_of_lt (sub_pos_of_lt hpq))) (le_of_eq (one_mul_thm _))
  rcases lt_total a b with h | h | h
  · rw [show abs (atan a - atan b) = abs (atan b - atan a) from by
          rw [show atan a - atan b = -(atan b - atan a) from by mach_ring, abs_neg],
        show a - b = -(b - a) from by mach_ring, abs_neg,
        abs_of_nonneg (le_of_lt (sub_pos_of_lt h))]
    exact step a b h
  · rw [h]
    have hz : atan b - atan b = 0 := by mach_ring
    rw [hz, abs_zero]; exact abs_nonneg _
  · rw [abs_of_nonneg (le_of_lt (sub_pos_of_lt h))]; exact step b a h

/-- `|atan x| ≤ |x|` (1-Lipschitz from `atan 0 = 0`), so `atan` preserves a magnitude bound. -/
theorem abs_atan_le_abs (x : Real) : abs (atan x) ≤ abs x := by
  have h := atan_lipschitz x 0
  rwa [atan_zero, show atan x - 0 = atan x from by mach_ring, show x - 0 = x from by mach_ring] at h

end MachLib.Real
