import MachLib.SinTaylorRemainder

/-!
# The real-valued cos Taylor-remainder bound — reusing `SinTaylorRemainder`'s chain

`eml_cos.v` (Forge's hardware `cos` transcendental) computes the 4-term Maclaurin truncation
`1 − x²/2 + x⁴/24 − x⁶/720`, one degree past `eml_sin.v`'s 3-term `x − x³/6 + x⁵/120`. Rather
than re-deriving a fresh MVT chain, this file extends `SinTaylorRemainder`'s existing R5→R0
chain by exactly ONE more level: `Rcos(y) := R1(y) + y⁶/720`, whose derivative is `-R0(c)`
(R1 already differentiates to R2; the new `y⁶/720` term's derivative collapses to the missing
`y⁵/120` piece, and `R2(c) + c⁵/120 = -R0(c)` by direct term inspection). `Rcos_bound` then
falls out of the SAME `abs_mvt_step`/monotonicity-chain technique used throughout
`SinTaylorRemainder`, extended one degree (`x⁶ → x⁷`).

## A `mach_ring` gotcha, resolved this time (not just documented and set aside)

`SinTaylorRemainder`'s docstring flags an unresolved quirk: the sign-flip identity
`-A+B-C+D = -(A-B+C-D)` closes instantly over fully-abstract atoms but hangs/fails when hit
directly with the concrete `sin c`/nested-fraction subterms this file's `Rcos_deriv` needs.
The fix used here: prove `neg_sub_add_id` ONCE generically (`mach_ring` on abstract `A B C D`,
trivial), then `exact neg_sub_add_id (sin c) c (...) (...)` — pure term substitution, no
re-normalization of the concrete expression ever happens. Worth reusing for any future
`mach_ring` failure of this shape rather than re-deriving a workaround from scratch.

`sorryAx`-free.
-/

namespace MachLib.Real

theorem hD_y6 : ∀ c : Real,
    HasDerivAt (fun y => y * y * y * y * y * y)
      ((c * c + c * c + c * c) * (c * c * c) + (c * c * c) * (c * c + c * c + c * c)) c := by
  intro c
  exact HasDerivAt_of_eq (fun y => (y * y * y) * (y * y * y)) (fun y => y * y * y * y * y * y) _ c
    (fun y => by mach_ring)
    (HasDerivAt_mul (fun y => y * y * y) (fun y => y * y * y)
      (c * c + c * c + c * c) (c * c + c * c + c * c) c (hD_y3 c) (hD_y3 c))

noncomputable def sevenhundredtwenty : Real := (1 + 1 + 1 + 1 + 1 + 1 : Real) * onetwenty

theorem sevenhundredtwenty_ne_zero : sevenhundredtwenty ≠ 0 := by
  unfold sevenhundredtwenty
  exact ne_of_gt (mul_pos my_six_pos
    (by unfold onetwenty; exact mul_pos my_five_pos (by unfold twentyfour; exact mul_pos my_four_pos my_six_pos)))

/-- `(x+x+x+x+x+x)·(1/720) = x·(1/120)` — the `y⁶ ↔ y⁵` coefficient relation (`6/720 = 1/120`). -/
theorem sixth_of_720 (x : Real) :
    (x + x + x + x + x + x) * (1 / sevenhundredtwenty) = x * (1 / onetwenty) := by
  have hrw : (x + x + x + x + x + x) * (1 / sevenhundredtwenty)
      = ((1 + 1 + 1 + 1 + 1 + 1) * (1 / sevenhundredtwenty)) * x := by mach_ring
  rw [hrw, frac_reduce (1 + 1 + 1 + 1 + 1 + 1) onetwenty sevenhundredtwenty onetwenty_ne_zero
    sevenhundredtwenty_ne_zero (by unfold sevenhundredtwenty; rfl)]
  mach_ring

/-- Generic sign-flip identity, proven once over abstract atoms; specialize at concrete values
to sidestep `mach_ring`'s fragility on this exact nested-fraction shape when hit directly. -/
theorem neg_sub_add_id (A B C D : Real) : -A + B - C + D = -(A - B + C - D) := by
  mach_ring

/-- `Rcos(y) = R1(y) + y⁶/720 = cos(y) − 1 + y²/2 − y⁴/24 + y⁶/720` — exactly `eml_cos.v`'s
forward-error remainder against its true 4-term Maclaurin truncation. -/
noncomputable def Rcos (y : Real) : Real :=
  R1 y + y * y * y * y * y * y * (1 / sevenhundredtwenty : Real)

theorem Rcos_deriv : ∀ c : Real, HasDerivAt Rcos (-(R0 c)) c := by
  intro c
  have hy6 : HasDerivAt (fun y => y * y * y * y * y * y * (1 / sevenhundredtwenty : Real))
      (((c * c + c * c + c * c) * (c * c * c) + (c * c * c) * (c * c + c * c + c * c))
        * (1 / sevenhundredtwenty : Real) + (c * c * c * c * c * c) * 0) c :=
    HasDerivAt_mul (fun y => y * y * y * y * y * y) (fun _ => (1 / sevenhundredtwenty : Real))
      ((c * c + c * c + c * c) * (c * c * c) + (c * c * c) * (c * c + c * c + c * c)) 0 c
      (hD_y6 c) (HasDerivAt_const (1 / sevenhundredtwenty : Real) c)
  have hfull := HasDerivAt_add R1 (fun y => y * y * y * y * y * y * (1 / sevenhundredtwenty : Real))
    (R2 c) _ c (R1_deriv c) hy6
  have hclean : R2 c
      + (((c * c + c * c + c * c) * (c * c * c) + (c * c * c) * (c * c + c * c + c * c))
        * (1 / sevenhundredtwenty : Real) + (c * c * c * c * c * c) * 0)
      = -(R0 c) := by
    unfold R2 R0
    have hy6simp : ((c * c + c * c + c * c) * (c * c * c) + (c * c * c) * (c * c + c * c + c * c))
        * (1 / sevenhundredtwenty : Real) + (c * c * c * c * c * c) * 0
        = (c * c * c * c * c + c * c * c * c * c + c * c * c * c * c + c * c * c * c * c
            + c * c * c * c * c + c * c * c * c * c) * (1 / sevenhundredtwenty) := by mach_ring
    rw [hy6simp, sixth_of_720 (c * c * c * c * c)]
    exact neg_sub_add_id (sin c) c (c * c * c * (1 / (1 + 1 + 1 + 1 + 1 + 1)))
      (c * c * c * c * c * (1 / onetwenty))
  exact hasDerivAt_congr_val hfull hclean

theorem Rcos_zero : Rcos 0 = 0 := by unfold Rcos; rw [R1_zero]; mach_ring

/-- **`|cos(x) − (1 − x²/2 + x⁴/24 − x⁶/720)| ≤ x⁷` for `x ≥ 0`** — the real-valued forward-error
bound for `eml_cos.v`'s exact 4-term Maclaurin truncation. `sorryAx`-free. -/
theorem Rcos_bound (x : Real) (hx0 : 0 ≤ x) :
    abs (Rcos x) ≤ ((((((x * x) * x) * x) * x) * x) * x) := by
  apply abs_mvt_step Rcos (fun c => -(R0 c)) x (((((x * x) * x) * x) * x) * x) hx0
    (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hx0 hx0) hx0) hx0) hx0) hx0)
    Rcos_deriv Rcos_zero
  intro t ht0 htx
  have h1 : abs (-(R0 t)) ≤ ((((t * t) * t) * t) * t) * t := by
    rw [abs_neg]; exact R0_bound t ht0
  have h2 : ((((t * t) * t) * t) * t) * t ≤ ((((x * x) * x) * x) * x) * x := by
    have ha : t * t ≤ x * x :=
      le_trans (mul_le_mul_of_nonneg_right htx ht0) (mul_le_mul_of_nonneg_left htx hx0)
    have hb : (t * t) * t ≤ (x * x) * x :=
      le_trans (mul_le_mul_of_nonneg_right ha ht0) (mul_le_mul_of_nonneg_left htx (mul_nonneg hx0 hx0))
    have hc : ((t * t) * t) * t ≤ ((x * x) * x) * x :=
      le_trans (mul_le_mul_of_nonneg_right hb ht0)
        (mul_le_mul_of_nonneg_left htx (mul_nonneg (mul_nonneg hx0 hx0) hx0))
    have hd : (((t * t) * t) * t) * t ≤ (((x * x) * x) * x) * x :=
      le_trans (mul_le_mul_of_nonneg_right hc ht0)
        (mul_le_mul_of_nonneg_left htx (mul_nonneg (mul_nonneg (mul_nonneg hx0 hx0) hx0) hx0))
    exact le_trans (mul_le_mul_of_nonneg_right hd ht0)
      (mul_le_mul_of_nonneg_left htx (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hx0 hx0) hx0) hx0) hx0))
  exact le_trans h1 h2

end MachLib.Real
