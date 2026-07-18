import MachLib.SinhTaylorRemainder
import MachLib.CosTaylorRemainder

/-!
# The real-valued cosh Taylor-remainder bound — extends `SinhTaylorRemainder` by one level

`eml_cosh.v` computes `cosh(x) ≈ 1 + x²/2 + x⁴/24 + x⁶/720`, one degree past `eml_sinh.v`'s
3-term `x + x³/6 + x⁵/120` — exactly the same "one level deeper" relationship `eml_cos.v` has to
`eml_sin.v`. Mirrors `CosTaylorRemainder`'s reuse trick: `Rch0(y) := Rsh1(y) − y⁶/720`, whose
derivative is exactly `Rsh0(y)` (`Rsh1' = Rsh2` already, and the new `−y⁶/720` term's derivative
is the missing `−y⁵/120` piece completing `Rsh0`). One more `abs_mvt_step` on top of the already-
built `Rsh0_bound` gives the whole certificate — no fresh MVT chain needed. `sorryAx`-free.
-/

namespace MachLib.Real

/-- `Rch0(y) = Rsh1(y) − y⁶/720 = cosh(y) − 1 − y²/2 − y⁴/24 − y⁶/720` — exactly `eml_cosh.v`'s
forward-error remainder against its true 4-term Maclaurin truncation. -/
noncomputable def Rch0 (y : Real) : Real :=
  Rsh1 y - y * y * y * y * y * y * (1 / sevenhundredtwenty : Real)

theorem Rch0_deriv : ∀ c : Real, HasDerivAt Rch0 (Rsh0 c) c := by
  intro c
  have hy6 : HasDerivAt (fun y => y * y * y * y * y * y * (1 / sevenhundredtwenty : Real))
      (((c * c + c * c + c * c) * (c * c * c) + (c * c * c) * (c * c + c * c + c * c))
        * (1 / sevenhundredtwenty : Real) + (c * c * c * c * c * c) * 0) c :=
    HasDerivAt_mul (fun y => y * y * y * y * y * y) (fun _ => (1 / sevenhundredtwenty : Real))
      ((c * c + c * c + c * c) * (c * c * c) + (c * c * c) * (c * c + c * c + c * c)) 0 c
      (hD_y6 c) (HasDerivAt_const (1 / sevenhundredtwenty : Real) c)
  have hfull := HasDerivAt_sub Rsh1 (fun y => y * y * y * y * y * y * (1 / sevenhundredtwenty : Real))
    (Rsh2 c) _ c (Rsh1_deriv c) hy6
  have hclean : Rsh2 c
      - (((c * c + c * c + c * c) * (c * c * c) + (c * c * c) * (c * c + c * c + c * c))
        * (1 / sevenhundredtwenty : Real) + (c * c * c * c * c * c) * 0)
      = Rsh0 c := by
    unfold Rsh2 Rsh0
    have hy6simp : ((c * c + c * c + c * c) * (c * c * c) + (c * c * c) * (c * c + c * c + c * c))
        * (1 / sevenhundredtwenty : Real) + (c * c * c * c * c * c) * 0
        = (c * c * c * c * c + c * c * c * c * c + c * c * c * c * c + c * c * c * c * c
            + c * c * c * c * c + c * c * c * c * c) * (1 / sevenhundredtwenty) := by mach_ring
    rw [hy6simp, sixth_of_720 (c * c * c * c * c)]
    mach_ring
  exact hasDerivAt_congr_val hfull hclean

theorem Rch0_zero : Rch0 0 = 0 := by unfold Rch0; rw [Rsh1_zero]; mach_ring

/-- **The main result.** `|cosh(x) − (1 + x²/2 + x⁴/24 + x⁶/720)| ≤ sinh(x)·x⁷` for `x ≥ 0` —
the real-valued forward-error bound for `eml_cosh.v`'s exact 4-term Maclaurin truncation.
`sorryAx`-free. -/
theorem Rch0_bound (x : Real) (hx0 : 0 ≤ x) :
    abs (Rch0 x) ≤ ((((((sinh x * x) * x) * x) * x) * x) * x) * x := by
  apply abs_mvt_step Rch0 Rsh0 x ((((((sinh x * x) * x) * x) * x) * x) * x) hx0
    (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (sinh_nonneg hx0) hx0) hx0) hx0) hx0) hx0) hx0)
    Rch0_deriv Rch0_zero
  intro t ht0 htx
  have h1 : abs (Rsh0 t) ≤ (((((sinh t * t) * t) * t) * t) * t) * t := Rsh0_bound t ht0
  have h2 : (((((sinh t * t) * t) * t) * t) * t) * t ≤ (((((sinh x * x) * x) * x) * x) * x) * x := by
    have ha : sinh t * t ≤ sinh x * x :=
      le_trans (mul_le_mul_of_nonneg_right (sinh_mono htx) ht0)
        (mul_le_mul_of_nonneg_left htx (sinh_nonneg hx0))
    have hb : (sinh t * t) * t ≤ (sinh x * x) * x :=
      le_trans (mul_le_mul_of_nonneg_right ha ht0)
        (mul_le_mul_of_nonneg_left htx (mul_nonneg (sinh_nonneg hx0) hx0))
    have hc : ((sinh t * t) * t) * t ≤ ((sinh x * x) * x) * x :=
      le_trans (mul_le_mul_of_nonneg_right hb ht0)
        (mul_le_mul_of_nonneg_left htx (mul_nonneg (mul_nonneg (sinh_nonneg hx0) hx0) hx0))
    have hd : (((sinh t * t) * t) * t) * t ≤ (((sinh x * x) * x) * x) * x :=
      le_trans (mul_le_mul_of_nonneg_right hc ht0)
        (mul_le_mul_of_nonneg_left htx (mul_nonneg (mul_nonneg (mul_nonneg (sinh_nonneg hx0) hx0) hx0) hx0))
    have he : ((((sinh t * t) * t) * t) * t) * t ≤ ((((sinh x * x) * x) * x) * x) * x :=
      le_trans (mul_le_mul_of_nonneg_right hd ht0)
        (mul_le_mul_of_nonneg_left htx
          (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (sinh_nonneg hx0) hx0) hx0) hx0) hx0))
    exact le_trans (mul_le_mul_of_nonneg_right he ht0)
      (mul_le_mul_of_nonneg_left htx
        (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (sinh_nonneg hx0) hx0) hx0) hx0) hx0) hx0))
  exact le_trans h1 h2

end MachLib.Real
