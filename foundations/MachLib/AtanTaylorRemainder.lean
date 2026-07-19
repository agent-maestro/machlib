import MachLib.SinTaylorRemainder
import MachLib.InverseTrig
import MachLib.DivisionError
import MachLib.Decimal

/-!
# The real-valued `atan` Taylor-remainder bound — a ONE-STEP MVT chain, not an 8-level one

Forge's Verilog backend (`hardware/modules/transcendental/eml_atan.v`) implements `atan(x)` on real
FPGA silicon via a 4-term Maclaurin truncation, `atan(x) ≈ x − x³/3 + x⁵/5 − x⁷/7`, valid on `[−1,1]`.

Unlike `tan`/`tanh` (whose derivative is a polynomial IN THE FUNCTION ITSELF, `1 ± f²`, so every
higher derivative is again a polynomial in `f` that needs an 8-level MVT chain to unwind), `atan`'s
derivative `1/(1+x²)` is a rational function DIRECTLY IN `x`. This makes the remainder telescope:

`R0(y) := atan(y) − (y − y³/3 + y⁵/5 − y⁷/7)`
`R0'(y) = 1/(1+y²) − (1 − y² + y⁴ − y⁶) = [1 − (1−y²+y⁴−y⁶)(1+y²)] / (1+y²) = y⁸ / (1+y²)`

(the numerator telescopes via the geometric-series identity `(1−y²+y⁴−y⁶)(1+y²) = 1−y⁸`). Since
`1+y² ≥ 1`, `|R0'(y)| = y⁸/(1+y²) ≤ y⁸` for `y ≥ 0` — a single flat bound, needing only ONE
application of the plain-MVT step (`abs_mvt_step`, imported from `SinTaylorRemainder`), not a
repeated chain. Verified symbolically (sympy) before encoding, not guessed.

**Result**: `R0_bound` below is `|atan(x) − (x − x³/3 + x⁵/5 − x⁷/7)| ≤ x⁸ · x = x⁹` for `x ∈ [0,1]`
— the real-valued half of the hardware forward-error certificate. `sorryAx`-free, 0 new axioms
(reuses `HasDerivAt_atan` from `MachLib.InverseTrig`).
-/

namespace MachLib.Real

/-! ## Small fraction-cancellation facts: `n · (1/n) = 1` for `n = 3, 5, 7`, used to turn the raw
product-rule derivative of `y³/3`, `y⁵/5`, `y⁷/7` into the clean `y²`, `y⁴`, `y⁶` Taylor
coefficients. -/

theorem my_three_pos : (0 : Real) < 1 + 1 + 1 := add_pos (add_pos zero_lt_one_ax zero_lt_one_ax) zero_lt_one_ax
theorem my_seven_pos : (0 : Real) < 1 + 1 + 1 + 1 + 1 + 1 + 1 :=
  add_pos (add_pos (add_pos (add_pos (add_pos (add_pos zero_lt_one_ax zero_lt_one_ax) zero_lt_one_ax)
    zero_lt_one_ax) zero_lt_one_ax) zero_lt_one_ax) zero_lt_one_ax

theorem my_three_ne_zero : (1 + 1 + 1 : Real) ≠ 0 := ne_of_gt my_three_pos
theorem my_five_ne_zero : (1 + 1 + 1 + 1 + 1 : Real) ≠ 0 := ne_of_gt my_five_pos
theorem my_seven_ne_zero : (1 + 1 + 1 + 1 + 1 + 1 + 1 : Real) ≠ 0 := ne_of_gt my_seven_pos

/-- `(c+c+c) · (1/3) = c`. -/
theorem thirds_cancel (c : Real) : (c + c + c) * (1 / (1 + 1 + 1)) = c := by
  rw [show c + c + c = (1 + 1 + 1) * c from by mach_ring, mul_comm (1 + 1 + 1 : Real) c, mul_assoc,
    mul_inv (1 + 1 + 1) my_three_ne_zero, mul_one_ax]

/-- `(c+c+c+c+c) · (1/5) = c`. -/
theorem fifths_cancel (c : Real) : (c + c + c + c + c) * (1 / (1 + 1 + 1 + 1 + 1)) = c := by
  rw [show c + c + c + c + c = (1 + 1 + 1 + 1 + 1) * c from by mach_ring,
    mul_comm (1 + 1 + 1 + 1 + 1 : Real) c, mul_assoc, mul_inv (1 + 1 + 1 + 1 + 1) my_five_ne_zero,
    mul_one_ax]

/-- `(c+c+c+c+c+c+c) · (1/7) = c`. -/
theorem sevenths_cancel (c : Real) : (c + c + c + c + c + c + c) * (1 / (1 + 1 + 1 + 1 + 1 + 1 + 1)) = c := by
  rw [show c + c + c + c + c + c + c = (1 + 1 + 1 + 1 + 1 + 1 + 1) * c from by mach_ring,
    mul_comm (1 + 1 + 1 + 1 + 1 + 1 + 1 : Real) c, mul_assoc,
    mul_inv (1 + 1 + 1 + 1 + 1 + 1 + 1) my_seven_ne_zero, mul_one_ax]

/-! ## `hD_y6`, `hD_y7` — one level further than `SinTaylorRemainder` provides. -/

theorem hD_y6raw : ∀ c : Real,
    HasDerivAt (fun y => (y * y * y) * (y * y * y))
      ((c * c + c * c + c * c) * (c * c * c) + (c * c * c) * (c * c + c * c + c * c)) c := by
  intro c
  exact HasDerivAt_mul (fun y => y * y * y) (fun y => y * y * y) (c * c + c * c + c * c)
    (c * c + c * c + c * c) c (hD_y3 c) (hD_y3 c)

theorem hD_y6 : ∀ c : Real,
    HasDerivAt (fun y => y * y * y * y * y * y)
      ((c * c + c * c + c * c) * (c * c * c) + (c * c * c) * (c * c + c * c + c * c)) c := by
  intro c
  exact HasDerivAt_of_eq (fun y => (y * y * y) * (y * y * y)) (fun y => y * y * y * y * y * y) _ c
    (fun y => by mach_ring) (hD_y6raw c)

theorem hD_y7raw : ∀ c : Real,
    HasDerivAt (fun y => (y * y * y) * (y * y * y * y))
      ((c * c + c * c + c * c) * (c * c * c * c) + (c * c * c) * ((c + c) * (c * c) + (c * c) * (c + c))) c := by
  intro c
  exact HasDerivAt_mul (fun y => y * y * y) (fun y => y * y * y * y) (c * c + c * c + c * c)
    ((c + c) * (c * c) + (c * c) * (c + c)) c (hD_y3 c) (hD_y4 c)

theorem hD_y7 : ∀ c : Real,
    HasDerivAt (fun y => y * y * y * y * y * y * y)
      ((c * c + c * c + c * c) * (c * c * c * c) + (c * c * c) * ((c + c) * (c * c) + (c * c) * (c + c))) c := by
  intro c
  exact HasDerivAt_of_eq (fun y => (y * y * y) * (y * y * y * y)) (fun y => y * y * y * y * y * y * y) _ c
    (fun y => by mach_ring) (hD_y7raw c)

/-! ## `R0` — the actual hardware remainder — and its derivative `R1 = 1/(1+y²) − (1−y²+y⁴−y⁶)`. -/

/-- The truncation polynomial Forge's `eml_atan.v` computes: `y − y³/3 + y⁵/5 − y⁷/7`. -/
noncomputable def Patan (y : Real) : Real :=
  y - y * y * y * (1 / (1 + 1 + 1)) + y * y * y * y * y * (1 / (1 + 1 + 1 + 1 + 1))
    - y * y * y * y * y * y * y * (1 / (1 + 1 + 1 + 1 + 1 + 1 + 1))

/-- `R0(y) = atan(y) − Patan(y)` — the exact real-valued hardware remainder. -/
noncomputable def R0atan (y : Real) : Real := atan y - Patan y

theorem Patan_deriv (c : Real) :
    HasDerivAt Patan (1 - c * c + c * c * c * c - c * c * c * c * c * c) c := by
  have h1 : HasDerivAt (fun y : Real => y) 1 c := HasDerivAt_id c
  have h3 : HasDerivAt (fun y : Real => y * y * y * (1 / (1 + 1 + 1)))
      ((c * c + c * c + c * c) * (1 / (1 + 1 + 1))) c :=
    hasDerivAt_congr_val
      (HasDerivAt_mul (fun y => y * y * y) (fun _ => (1 / (1 + 1 + 1) : Real))
        (c * c + c * c + c * c) 0 c (hD_y3 c) (HasDerivAt_const (1 / (1 + 1 + 1)) c))
      (by mach_ring)
  have h5 : HasDerivAt (fun y : Real => y * y * y * y * y * (1 / (1 + 1 + 1 + 1 + 1)))
      (((c + c) * (c * c * c) + (c * c) * (c * c + c * c + c * c)) * (1 / (1 + 1 + 1 + 1 + 1))) c :=
    hasDerivAt_congr_val
      (HasDerivAt_mul (fun y => y * y * y * y * y) (fun _ => (1 / (1 + 1 + 1 + 1 + 1) : Real))
        ((c + c) * (c * c * c) + (c * c) * (c * c + c * c + c * c)) 0 c (hD_y5 c)
        (HasDerivAt_const (1 / (1 + 1 + 1 + 1 + 1)) c))
      (by mach_ring)
  have h7 : HasDerivAt (fun y : Real => y * y * y * y * y * y * y * (1 / (1 + 1 + 1 + 1 + 1 + 1 + 1)))
      (((c * c + c * c + c * c) * (c * c * c * c) + (c * c * c) * ((c + c) * (c * c) + (c * c) * (c + c)))
        * (1 / (1 + 1 + 1 + 1 + 1 + 1 + 1))) c :=
    hasDerivAt_congr_val
      (HasDerivAt_mul (fun y => y * y * y * y * y * y * y) (fun _ => (1 / (1 + 1 + 1 + 1 + 1 + 1 + 1) : Real))
        ((c * c + c * c + c * c) * (c * c * c * c) + (c * c * c) * ((c + c) * (c * c) + (c * c) * (c + c))) 0 c
        (hD_y7 c) (HasDerivAt_const (1 / (1 + 1 + 1 + 1 + 1 + 1 + 1)) c))
      (by mach_ring)
  have hsub1 := HasDerivAt_sub (fun y : Real => y) (fun y => y * y * y * (1 / (1 + 1 + 1))) 1 _ c h1 h3
  have hadd := HasDerivAt_add _ (fun y => y * y * y * y * y * (1 / (1 + 1 + 1 + 1 + 1))) _ _ c hsub1 h5
  have hfull := HasDerivAt_sub _ (fun y => y * y * y * y * y * y * y * (1 / (1 + 1 + 1 + 1 + 1 + 1 + 1))) _ _ c hadd h7
  refine hasDerivAt_congr_val hfull ?_
  rw [show (c * c + c * c + c * c) * (1 / (1 + 1 + 1)) = c * c from thirds_cancel (c * c),
    show ((c + c) * (c * c * c) + c * c * (c * c + c * c + c * c)) * (1 / (1 + 1 + 1 + 1 + 1))
      = c * c * c * c from by
      rw [show (c + c) * (c * c * c) + c * c * (c * c + c * c + c * c)
        = (c * c * c * c) + (c * c * c * c) + (c * c * c * c) + (c * c * c * c) + (c * c * c * c)
        from by mach_ring]
      exact fifths_cancel (c * c * c * c),
    show ((c * c + c * c + c * c) * (c * c * c * c) + c * c * c * ((c + c) * (c * c) + c * c * (c + c)))
      * (1 / (1 + 1 + 1 + 1 + 1 + 1 + 1)) = c * c * c * c * c * c from by
      rw [show (c * c + c * c + c * c) * (c * c * c * c) + c * c * c * ((c + c) * (c * c) + c * c * (c + c))
        = (c*c*c*c*c*c) + (c*c*c*c*c*c) + (c*c*c*c*c*c) + (c*c*c*c*c*c) + (c*c*c*c*c*c)
          + (c*c*c*c*c*c) + (c*c*c*c*c*c)
        from by mach_ring]
      exact sevenths_cancel (c * c * c * c * c * c)]
  mach_ring

theorem Patan_zero : Patan 0 = 0 := by unfold Patan; mach_ring

/-- `R0(0) = 0` (`atan 0 = 0` and `Patan 0 = 0`). -/
theorem R0atan_zero : R0atan 0 = 0 := by
  unfold R0atan; rw [atan_zero, Patan_zero]; mach_ring

theorem R0atan_deriv (c : Real) :
    HasDerivAt R0atan (1 / (1 + c * c) - (1 - c * c + c * c * c * c - c * c * c * c * c * c)) c :=
  HasDerivAt_sub atan Patan _ _ c (HasDerivAt_atan c) (Patan_deriv c)

/-- **The telescoping identity**: `R0'(y) = y⁸/(1+y²)`, verified symbolically before encoding
(`(1−y²+y⁴−y⁶)(1+y²) = 1−y⁸`, a geometric-series-style cancellation). -/
theorem R0atan_deriv_eq (c : Real) :
    1 / (1 + c * c) - (1 - c * c + c * c * c * c - c * c * c * c * c * c)
      = (c * c * c * c * c * c * c * c) * (1 / (1 + c * c)) := by
  have hcc_nonneg : (0 : Real) ≤ c * c := mul_self_nonneg c
  have h1cc_pos : (0 : Real) < 1 + c * c := lt_of_lt_of_le zero_lt_one_ax (le_add_of_nonneg_right hcc_nonneg)
  have h1cc_ne : (1 + c * c : Real) ≠ 0 := ne_of_gt h1cc_pos
  have e1 : (1 / (1 + c * c) : Real) * (1 + c * c) = 1 := by
    rw [mul_comm, mul_inv (1 + c * c) h1cc_ne]
  refine mul_right_cancel' h1cc_ne ?_
  rw [show (1 / (1 + c * c) - (1 - c * c + c * c * c * c - c * c * c * c * c * c)) * (1 + c * c)
      = 1 / (1 + c * c) * (1 + c * c)
        - (1 - c * c + c * c * c * c - c * c * c * c * c * c) * (1 + c * c) from by mach_ring,
    e1,
    show ((c * c * c * c * c * c * c * c) * (1 / (1 + c * c))) * (1 + c * c)
      = (c * c * c * c * c * c * c * c) * ((1 / (1 + c * c)) * (1 + c * c)) from by mach_ring,
    e1]
  mach_mpoly [c]
  mach_ring

/-- **`R0atan`'s derivative, in the clean `y⁸/(1+y²)` form.** -/
theorem R0atan_deriv' (c : Real) :
    HasDerivAt R0atan ((c * c * c * c * c * c * c * c) * (1 / (1 + c * c))) c :=
  hasDerivAt_congr_val (R0atan_deriv c) (R0atan_deriv_eq c)

/-- `y⁸/(1+y²) ≤ y⁸` for `y ≥ 0` (dividing by something `≥ 1` shrinks a nonneg numerator). -/
theorem atan_rem_deriv_le (t : Real) (ht0 : 0 ≤ t) :
    (t * t * t * t * t * t * t * t) * (1 / (1 + t * t)) ≤ t * t * t * t * t * t * t * t := by
  have ht8_nonneg : (0 : Real) ≤ t * t * t * t * t * t * t * t :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg
      ht0 ht0) ht0) ht0) ht0) ht0) ht0) ht0
  have h1cc_pos : (0 : Real) < 1 + t * t :=
    lt_of_lt_of_le zero_lt_one_ax (le_add_of_nonneg_right (mul_self_nonneg t))
  have h1cc : (1 : Real) ≤ 1 + t * t := le_add_of_nonneg_right (mul_self_nonneg t)
  have hinv_le : (1 : Real) / (1 + t * t) ≤ 1 := div_le_one_of_le_of_pos h1cc_pos h1cc
  have hstep := mul_le_mul_of_nonneg_left hinv_le ht8_nonneg
  rwa [mul_one_ax] at hstep

/-- `0 ≤ t ≤ x → t⁸ ≤ x⁸` (repeated `mul_le_mul'`, degree by degree). -/
theorem pow8_mono {t x : Real} (ht0 : 0 ≤ t) (htx : t ≤ x) :
    t * t * t * t * t * t * t * t ≤ x * x * x * x * x * x * x * x := by
  have hx0 : 0 ≤ x := le_trans ht0 htx
  have d2 : t * t ≤ x * x := mul_le_mul' ht0 htx ht0 htx
  have n2 : 0 ≤ t * t := mul_nonneg ht0 ht0
  have d3 : t * t * t ≤ x * x * x := mul_le_mul' n2 d2 ht0 htx
  have n3 : 0 ≤ t * t * t := mul_nonneg n2 ht0
  have d4 : t * t * t * t ≤ x * x * x * x := mul_le_mul' n3 d3 ht0 htx
  have n4 : 0 ≤ t * t * t * t := mul_nonneg n3 ht0
  have d5 : t * t * t * t * t ≤ x * x * x * x * x := mul_le_mul' n4 d4 ht0 htx
  have n5 : 0 ≤ t * t * t * t * t := mul_nonneg n4 ht0
  have d6 : t * t * t * t * t * t ≤ x * x * x * x * x * x := mul_le_mul' n5 d5 ht0 htx
  have n6 : 0 ≤ t * t * t * t * t * t := mul_nonneg n5 ht0
  have d7 : t * t * t * t * t * t * t ≤ x * x * x * x * x * x * x := mul_le_mul' n6 d6 ht0 htx
  have n7 : 0 ≤ t * t * t * t * t * t * t := mul_nonneg n6 ht0
  exact mul_le_mul' n7 d7 ht0 htx

/-- **The atan real-valued hardware forward-error certificate.** `|atan(x) − (x − x³/3 + x⁵/5 −
x⁷/7)| ≤ x⁸ · x = x⁹` for `x ≥ 0` — a single flat bound from a single MVT step (unlike `sin`'s 5
levels or `tan`'s 8), thanks to `atan`'s clean telescoping remainder derivative `y⁸/(1+y²)`. -/
theorem R0atan_bound (x : Real) (hx0 : 0 ≤ x) :
    abs (R0atan x) ≤ (x * x * x * x * x * x * x * x) * x := by
  apply abs_mvt_step R0atan (fun c => (c * c * c * c * c * c * c * c) * (1 / (1 + c * c))) x
    (x * x * x * x * x * x * x * x) hx0
    (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg
      hx0 hx0) hx0) hx0) hx0) hx0) hx0) hx0)
    R0atan_deriv' R0atan_zero
  intro t ht0 htx
  have ht8_nonneg : (0 : Real) ≤ t * t * t * t * t * t * t * t :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg
      ht0 ht0) ht0) ht0) ht0) ht0) ht0) ht0
  have h1cc_pos : (0 : Real) < 1 + t * t :=
    lt_of_lt_of_le zero_lt_one_ax (le_add_of_nonneg_right (mul_self_nonneg t))
  have hprod_nonneg : (0 : Real) ≤ (t * t * t * t * t * t * t * t) * (1 / (1 + t * t)) :=
    mul_nonneg ht8_nonneg (le_of_lt (one_div_pos_of_pos h1cc_pos))
  rw [abs_of_nonneg hprod_nonneg]
  exact le_trans (atan_rem_deriv_le t ht0) (pow8_mono ht0 htx)

end MachLib.Real
