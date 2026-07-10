import MachLib.Basic
import MachLib.Lemmas
import MachLib.Forge
import MachLib.Ring
import MachLib.FPModel
import MachLib.Trig
import MachLib.Differentiation
import MachLib.Rolle

/-!
# `sin` / `cos` are 1-Lipschitz — derived, not axiomatised (Road 3 wedge)

`ErrorAlgebraTrans` used `sin_lipschitz`/`cos_lipschitz` as Trig axioms. They are
*derivable* from `mean_value_theorem` (`Rolle`) + `HasDerivAt_sin`/`HasDerivAt_cos`
(`Differentiation`) + `|cos|,|sin| ≤ 1` (`Trig`). This file proves them as
theorems and the axioms are removed from `Trig` — shrinking the trusted base by 2
(294 → 292) and establishing the MVT-derivation pattern for the rest of Road 3.

Layering note: this lives *above* `Rolle` (which needs `Differentiation` which
needs `Trig`), so the facts cannot live in `Trig` itself — hence a dedicated file,
imported by `ErrorAlgebraTrans`.
-/

namespace MachLib.Real

theorem abs_sub_comm (x y : Real) : abs (x - y) = abs (y - x) := by
  apply le_antisymm
  · apply abs_le_of
    · rw [show x - y = -(y - x) from by mach_ring]; exact neg_le_abs (y - x)
    · rw [show -(x - y) = y - x from by mach_ring]; exact le_abs_self (y - x)
  · apply abs_le_of
    · rw [show y - x = -(x - y) from by mach_ring]; exact neg_le_abs (x - y)
    · rw [show -(y - x) = x - y from by mach_ring]; exact le_abs_self (x - y)

-- `abs_neg` and `abs_cos_le_one` are pre-existing Lemmas axioms; reused here.
theorem abs_neg_sin_le_one (c : Real) : abs (-sin c) ≤ 1 := by
  rw [abs_neg]; exact abs_sin_le_one c

/-- One-sided MVT bound for `sin` on `a < b`: `|sin b − sin a| ≤ b − a`. -/
theorem sin_lip_lt {a b : Real} (hab : a < b) : abs (sin b - sin a) ≤ b - a := by
  obtain ⟨c, f', _, _, hd, heq⟩ :=
    mean_value_theorem_ct sin a b hab (fun c _ _ => ⟨cos c, HasDerivAt_sin c⟩)
  have hf' : f' = cos c := HasDerivAt_unique sin f' (cos c) c hd (HasDerivAt_sin c)
  have hba_nn : 0 ≤ b - a := sub_nonneg_of_le (le_of_lt hab)
  rw [heq, hf', abs_mul, abs_of_nonneg hba_nn]
  exact le_trans (mul_le_mul_of_nonneg_right (abs_cos_le_one c) hba_nn)
                 (le_of_eq (one_mul_thm (b - a)))

/-- One-sided MVT bound for `cos` on `a < b`: `|cos b − cos a| ≤ b − a`. -/
theorem cos_lip_lt {a b : Real} (hab : a < b) : abs (cos b - cos a) ≤ b - a := by
  obtain ⟨c, f', _, _, hd, heq⟩ :=
    mean_value_theorem_ct cos a b hab (fun c _ _ => ⟨-sin c, HasDerivAt_cos c⟩)
  have hf' : f' = -sin c := HasDerivAt_unique cos f' (-sin c) c hd (HasDerivAt_cos c)
  have hba_nn : 0 ≤ b - a := sub_nonneg_of_le (le_of_lt hab)
  rw [heq, hf', abs_mul, abs_of_nonneg hba_nn]
  exact le_trans (mul_le_mul_of_nonneg_right (abs_neg_sin_le_one c) hba_nn)
                 (le_of_eq (one_mul_thm (b - a)))

/-- **`sin` is 1-Lipschitz** — theorem (was a Trig axiom). -/
theorem sin_lipschitz (a b : Real) : abs (sin a - sin b) ≤ abs (a - b) := by
  rcases lt_total a b with h | h | h
  · rw [abs_sub_comm (sin a) (sin b),
        show abs (a - b) = b - a from by
          rw [abs_sub_comm a b]; exact abs_of_nonneg (sub_nonneg_of_le (le_of_lt h))]
    exact sin_lip_lt h
  · rw [h, show sin b - sin b = 0 from by mach_ring, show b - b = (0 : Real) from by mach_ring]
    exact le_refl _
  · rw [show abs (a - b) = a - b from abs_of_nonneg (sub_nonneg_of_le (le_of_lt h))]
    exact sin_lip_lt h

/-- **`cos` is 1-Lipschitz** — theorem (was a Trig axiom). -/
theorem cos_lipschitz (a b : Real) : abs (cos a - cos b) ≤ abs (a - b) := by
  rcases lt_total a b with h | h | h
  · rw [abs_sub_comm (cos a) (cos b),
        show abs (a - b) = b - a from by
          rw [abs_sub_comm a b]; exact abs_of_nonneg (sub_nonneg_of_le (le_of_lt h))]
    exact cos_lip_lt h
  · rw [h, show cos b - cos b = 0 from by mach_ring, show b - b = (0 : Real) from by mach_ring]
    exact le_refl _
  · rw [show abs (a - b) = a - b from abs_of_nonneg (sub_nonneg_of_le (le_of_lt h))]
    exact cos_lip_lt h

end MachLib.Real
