import MachLib.Differentiation
import MachLib.Hyperbolic
import MachLib.HyperbolicId
import MachLib.Rolle
import MachLib.FieldLemmas
import MachLib.FPModel

/-!
# `tanh` is 1-Lipschitz — derived via MVT (no new axioms)

`sin`/`cos` were promoted axiom→theorem (`TrigLipschitz`) by deriving their 1-Lipschitz
bound from `mean_value_theorem` + `HasDerivAt`. This extends that to the hyperbolic
tangent. `tanh' = 1/cosh² ≤ 1` (since `cosh ≥ 1`), so `tanh` is **bounded-Lipschitz** like
`sin`/`cos`. Everything is *derived* from `HasDerivAt_exp` + the calculus rules + `sinh_eq`
/`cosh_eq`/`tanh_eq` — `0 new axioms`.
-/

namespace MachLib.Real

private theorem two_ne_zero' : (1 : Real) + 1 ≠ 0 := two_ne_zero

/-- `sinh' = cosh`, derived from `sinh = (exp − exp∘neg)/2`. -/
theorem HasDerivAt_sinh (x : Real) : HasDerivAt sinh (cosh x) x := by
  have hen : HasDerivAt (fun y => exp (-y)) (exp (-x) * (-1)) x :=
    HasDerivAt_comp exp (fun y => -y) (-1) (exp (-x)) x
      (HasDerivAt_neg (fun y => y) 1 x (HasDerivAt_id x)) (HasDerivAt_exp (-x))
  have hsub : HasDerivAt (fun y => exp y - exp (-y)) (exp x - exp (-x) * (-1)) x :=
    HasDerivAt_sub exp (fun y => exp (-y)) (exp x) (exp (-x) * (-1)) x (HasDerivAt_exp x) hen
  have hmul : HasDerivAt (fun y => (exp y - exp (-y)) * (1 / (1 + 1)))
      ((exp x - exp (-x) * (-1)) * (1 / (1 + 1)) + (exp x - exp (-x)) * 0) x :=
    HasDerivAt_mul (fun y => exp y - exp (-y)) (fun _ => 1 / (1 + 1))
      (exp x - exp (-x) * (-1)) 0 x hsub (HasDerivAt_const (1 / (1 + 1)) x)
  have hderiv : (exp x - exp (-x) * (-1)) * (1 / (1 + 1)) + (exp x - exp (-x)) * 0 = cosh x := by
    rw [cosh_eq, div_def (exp x + exp (-x)) (1 + 1) two_ne_zero']
    mach_mpoly [exp x, exp (-x), (1 / (1 + 1) : Real)]
  rw [hderiv] at hmul
  exact HasDerivAt_of_eq (fun y => (exp y - exp (-y)) * (1 / (1 + 1))) sinh (cosh x) x
    (fun y => by rw [sinh_eq y, div_def (exp y - exp (-y)) (1 + 1) two_ne_zero']) hmul

/-- `cosh' = sinh`, derived from `cosh = (exp + exp∘neg)/2`. -/
theorem HasDerivAt_cosh (x : Real) : HasDerivAt cosh (sinh x) x := by
  have hen : HasDerivAt (fun y => exp (-y)) (exp (-x) * (-1)) x :=
    HasDerivAt_comp exp (fun y => -y) (-1) (exp (-x)) x
      (HasDerivAt_neg (fun y => y) 1 x (HasDerivAt_id x)) (HasDerivAt_exp (-x))
  have hadd : HasDerivAt (fun y => exp y + exp (-y)) (exp x + exp (-x) * (-1)) x :=
    HasDerivAt_add exp (fun y => exp (-y)) (exp x) (exp (-x) * (-1)) x (HasDerivAt_exp x) hen
  have hmul : HasDerivAt (fun y => (exp y + exp (-y)) * (1 / (1 + 1)))
      ((exp x + exp (-x) * (-1)) * (1 / (1 + 1)) + (exp x + exp (-x)) * 0) x :=
    HasDerivAt_mul (fun y => exp y + exp (-y)) (fun _ => 1 / (1 + 1))
      (exp x + exp (-x) * (-1)) 0 x hadd (HasDerivAt_const (1 / (1 + 1)) x)
  have hderiv : (exp x + exp (-x) * (-1)) * (1 / (1 + 1)) + (exp x + exp (-x)) * 0 = sinh x := by
    rw [sinh_eq, div_def (exp x - exp (-x)) (1 + 1) two_ne_zero']
    mach_mpoly [exp x, exp (-x), (1 / (1 + 1) : Real)]
  rw [hderiv] at hmul
  exact HasDerivAt_of_eq (fun y => (exp y + exp (-y)) * (1 / (1 + 1))) cosh (sinh x) x
    (fun y => by rw [cosh_eq y, div_def (exp y + exp (-y)) (1 + 1) two_ne_zero']) hmul

private theorem eq_div_of_mul_eq' {x z k : Real} (hk : k ≠ 0) (h : x * k = z) : x = z / k := by
  rw [← h, mul_comm x k, mul_div_cancel_left' hk]

/-- `tanh' = 1/cosh²`, derived as `(sinh · cosh⁻¹)'` and simplified by `cosh²−sinh²=1`. -/
theorem HasDerivAt_tanh (x : Real) : HasDerivAt tanh (1 / (cosh x * cosh x)) x := by
  have hcne : cosh x ≠ 0 := cosh_ne_zero x
  have hccne : cosh x * cosh x ≠ 0 := mul_ne_zero hcne hcne
  have hmul : HasDerivAt (fun y => sinh y * (1 / cosh y))
      (cosh x * (1 / cosh x) + sinh x * (-sinh x / (cosh x * cosh x))) x :=
    HasDerivAt_mul sinh (fun y => 1 / cosh y) (cosh x) (-sinh x / (cosh x * cosh x)) x
      (HasDerivAt_sinh x) (HasDerivAt_inv cosh (sinh x) x hcne (HasDerivAt_cosh x))
  have key : (cosh x * (1 / cosh x) + sinh x * (-sinh x / (cosh x * cosh x))) * (cosh x * cosh x)
      = 1 := by
    have e2 : (1 / (cosh x * cosh x)) * (cosh x * cosh x) = 1 := by
      rw [mul_comm]; exact mul_inv (cosh x * cosh x) hccne
    rw [div_def (-sinh x) (cosh x * cosh x) hccne,
        show (cosh x * (1 / cosh x) + sinh x * (-sinh x * (1 / (cosh x * cosh x)))) * (cosh x * cosh x)
          = cosh x * (1 / cosh x) * (cosh x * cosh x)
            + sinh x * -sinh x * ((1 / (cosh x * cosh x)) * (cosh x * cosh x)) from by
          mach_mpoly [cosh x, sinh x, 1 / cosh x, (1 / (cosh x * cosh x) : Real)],
        mul_inv (cosh x) hcne, e2,
        show (1 : Real) * (cosh x * cosh x) + sinh x * -sinh x * 1
          = cosh x * cosh x - sinh x * sinh x from by mach_ring, pythagorean_hyp]
  rw [eq_div_of_mul_eq' hccne key] at hmul
  exact HasDerivAt_of_eq (fun y => sinh y * (1 / cosh y)) tanh (1 / (cosh x * cosh x)) x
    (fun y => by rw [tanh_eq_sinh_div_cosh y, div_def (sinh y) (cosh y) (cosh_ne_zero y)]) hmul

/-- `|tanh'| ≤ 1` (since `cosh² ≥ 1`). -/
theorem abs_tanh_deriv_le_one (x : Real) : abs (1 / (cosh x * cosh x)) ≤ 1 := by
  have hpos : 0 < cosh x * cosh x := mul_pos (cosh_pos x) (cosh_pos x)
  have hge1 : (1 : Real) ≤ cosh x * cosh x :=
    le_trans (le_of_eq (one_mul_thm 1).symm)
      (le_trans (mul_le_mul_of_nonneg_right (cosh_ge_one x) (le_of_lt zero_lt_one_ax))
        (mul_le_mul_of_nonneg_left (cosh_ge_one x) (le_of_lt (cosh_pos x))))
  rw [abs_of_nonneg (one_div_nonneg_of_pos hpos)]
  exact div_le_one_of_le_of_pos hpos hge1

/-- **`tanh` is 1-Lipschitz** — `|tanh a − tanh b| ≤ |a − b|`, via MVT (no new axioms);
the hyperbolic analogue of `sin_lipschitz`/`cos_lipschitz`. -/
theorem tanh_lipschitz (a b : Real) : abs (tanh a - tanh b) ≤ abs (a - b) := by
  have step : ∀ p q : Real, p < q → abs (tanh q - tanh p) ≤ q - p := by
    intro p q hpq
    obtain ⟨c, f', _, _, hdc, hval⟩ :=
      mean_value_theorem tanh p q hpq (fun c _ _ => ⟨1 / (cosh c * cosh c), HasDerivAt_tanh c⟩)
    rw [hval, HasDerivAt_unique tanh f' (1 / (cosh c * cosh c)) c hdc (HasDerivAt_tanh c),
        abs_mul, abs_of_nonneg (le_of_lt (sub_pos_of_lt hpq))]
    exact le_trans (mul_le_mul_of_nonneg_right (abs_tanh_deriv_le_one c)
      (le_of_lt (sub_pos_of_lt hpq))) (le_of_eq (one_mul_thm _))
  rcases lt_total a b with h | h | h
  · rw [show abs (tanh a - tanh b) = abs (tanh b - tanh a) from by
          rw [show tanh a - tanh b = -(tanh b - tanh a) from by mach_ring, abs_neg],
        show a - b = -(b - a) from by mach_ring, abs_neg,
        abs_of_nonneg (le_of_lt (sub_pos_of_lt h))]
    exact step a b h
  · rw [h]
    have hz : tanh b - tanh b = 0 := by mach_ring
    rw [hz, abs_zero]; exact abs_nonneg _
  · rw [abs_of_nonneg (le_of_lt (sub_pos_of_lt h))]; exact step b a h

/-- `|tanh x| ≤ 1` (bounded, from `−1 < tanh x < 1`). -/
theorem abs_tanh_le_one (x : Real) : abs (tanh x) ≤ 1 := by
  apply abs_le_of (le_of_lt (tanh_lt_one x))
  have h := neg_le_neg (le_of_lt (neg_one_lt_tanh x))
  rwa [show -(-1 : Real) = 1 from by mach_ring] at h

end MachLib.Real
