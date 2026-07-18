import MachLib.Trig
import MachLib.Forge
import MachLib.Rolle
import MachLib.Ring
import MachLib.FPModel
import MachLib.FieldLemmas

/-!
# The real-valued sin Taylor-remainder bound — pathfinder for hardware forward-error grounding

Forge's Verilog backend (`hardware/modules/transcendental/eml_sin.v`) implements `sin(x)` on real
FPGA silicon via a 3-term Maclaurin truncation, `sin(x) ≈ x − x³/6 + x⁵/120`, valid on `[−π/2,π/2]`,
computed in Q16.16 fixed-point. Certifying that hardware's forward error needs TWO independent
pieces: (1) how far the TRUNCATED POLYNOMIAL itself is from the true `sin`, and (2) how far Q-format
FIXED-POINT ARITHMETIC (truncating shifts, not round-to-nearest) drifts from exact real arithmetic
computing that polynomial. **This file is (1), COMPLETE**: `R0_bound` below is exactly
`|sin(x) − (x − x³/6 + x⁵/120)| ≤ x⁶` for `x ≥ 0` — the real-valued half of the certificate,
`sorryAx`-free. The Q-format fixed-point layer (2) is a separate, not-yet-started piece.

**Method.** MachLib has no general Taylor's-theorem-with-remainder machinery (the SHARP Lagrange
`x⁷/7!` bound needs Cauchy's generalized MVT or an auxiliary-function/Rolle argument — its own
undertaking). Built instead a repeated PLAIN-MVT chain (`abs_mvt_step`): differentiate the remainder
`R0(y) = sin(y) − (y − y³/6 + y⁵/120)` five times down to `R5(y) = cos(y) − 1`, bound `R5` via
`|sin| ≤ 1`, then propagate the bound back up through `R4, R3, R2, R1` to `R0` via MVT with a
CONSTANT sup-bound at each step. Provably correct, but LOOSER than the sharp bound (`x⁶` here vs.
`x⁷/5040` sharp — off by a factor of `~x·5040/6 ≈ 840x` at `x`) — an honest, checked bound, not a
guessed or optimal one. Tightening it (via Cauchy's generalized MVT, or an explicit
Taylor's-theorem-with-integral-remainder development) is a natural follow-on, not attempted here.

**A real tooling gap found and worked around**: `mach_ring` normalizes RING structure
(associativity/commutativity/distributivity) but does NOT do decimal-literal or fraction-literal
ARITHMETIC — confirmed directly, it cannot close `0.5 + 0.5 = 1` or `1/(1+1) + 1/(1+1) = 1` on its
own. Worked around via the field axiom `mul_inv` instead (`frac_reduce`, the general form of
`double_half`'s technique). Separately, `MachLib.Real` has no `OfNat` instance for literals beyond
0/1 — an attempted "scale everything by 720 = 6! to avoid fractions entirely" strategy needed
`OfScientific` decimal literals (`720.0`) and hit the SAME decimal-arithmetic wall from the other
direction (`mach_ring` can't verify `360.0+360.0=720.0` either); abandoned in favour of the
fraction-based route below, which avoids both walls by keeping every denominator as either a small
repeated-`1` sum (`1+1+1+1+1+1` for six, cheap for `mach_ring`) or a PRODUCT of two such sums
(`twentyfour := four*six`, `onetwenty := five*twentyfour`) rather than ever needing a large flat sum
or a decimal literal.

**Not done**: the odd-symmetry extension (`R0` is an odd function since `sin` and the truncated
polynomial are both odd, so `|R0(x)| ≤ |x|⁶` for ALL `x`, not just `x ≥ 0` — mathematically
immediate) hit an unrelated `mach_ring` associativity quirk on the specific 4-term
sum-with-division shape `R0(-y) = -R0(y)` expands to (confirmed: the same identity over opaque
atoms closes fine; the failure is specific to how `mach_ring` re-associates the nested `y*y*y*(1/6)`
products under negation). Given `R0_bound` below is the substantive result, this polish item was set
aside rather than chased further — the extension to negative `x` is standard and can be added later
without touching anything else here.
-/

open MachLib.Real

/-- Transport a `HasDerivAt` fact along a proof that its derivative VALUE equals another expression
— used throughout to clean up "raw" combinator output into the exact next-level target form. -/
theorem hasDerivAt_congr_val {f : MachLib.Real → MachLib.Real} {a b x : MachLib.Real}
    (h : HasDerivAt f a x) (hab : a = b) : HasDerivAt f b x := hab ▸ h

/-- `(y·y)' = c+c` at `c` (product rule, not yet simplified to `2c` — `mach_ring` handles that
downstream where needed). -/
theorem hD_y2 : ∀ c : MachLib.Real, HasDerivAt (fun y => y * y) (c + c) c := by
  intro c
  exact hasDerivAt_congr_val
    (HasDerivAt_mul (fun y => y) (fun y => y) 1 1 c (HasDerivAt_id c) (HasDerivAt_id c))
    (by mach_ring)

/-- `(y·y·y)' = c·c+c·c+c·c` at `c` (product rule on `(y·y)·y`, reusing `hD_y2`). -/
theorem hD_y3 : ∀ c : MachLib.Real, HasDerivAt (fun y => y * y * y) (c * c + c * c + c * c) c := by
  intro c
  exact hasDerivAt_congr_val
    (HasDerivAt_mul (fun y => y * y) (fun y => y) (c + c) 1 c (hD_y2 c) (HasDerivAt_id c))
    (by mach_ring)

/-- `(y·y·y·y)' = (c+c)·(c·c)+(c·c)·(c+c)` (product rule on `(y·y)·(y·y)`, via `HasDerivAt_of_eq`
since `y·y·y·y` and `(y·y)·(y·y)` are ring-equal but not definitionally the same term). -/
theorem hD_y4raw : ∀ c : MachLib.Real,
    HasDerivAt (fun y => (y * y) * (y * y)) ((c + c) * (c * c) + (c * c) * (c + c)) c := by
  intro c
  exact HasDerivAt_mul (fun y => y * y) (fun y => y * y) (c + c) (c + c) c (hD_y2 c) (hD_y2 c)

theorem hD_y4 : ∀ c : MachLib.Real,
    HasDerivAt (fun y => y * y * y * y) ((c + c) * (c * c) + (c * c) * (c + c)) c := by
  intro c
  exact HasDerivAt_of_eq (fun y => (y * y) * (y * y)) (fun y => y * y * y * y) _ c
    (fun y => by mach_ring) (hD_y4raw c)

/-- `(y·y·y·y·y)' = (c+c)·(c·c·c)+(c·c)·(c·c+c·c+c·c)` (product rule on `(y·y)·(y·y·y)`). -/
theorem hD_y5raw : ∀ c : MachLib.Real,
    HasDerivAt (fun y => (y * y) * (y * y * y))
      ((c + c) * (c * c * c) + (c * c) * (c * c + c * c + c * c)) c := by
  intro c
  exact HasDerivAt_mul (fun y => y * y) (fun y => y * y * y) (c + c) (c * c + c * c + c * c) c
    (hD_y2 c) (hD_y3 c)

theorem hD_y5 : ∀ c : MachLib.Real,
    HasDerivAt (fun y => y * y * y * y * y)
      ((c + c) * (c * c * c) + (c * c) * (c * c + c * c + c * c)) c := by
  intro c
  exact HasDerivAt_of_eq (fun y => (y * y) * (y * y * y)) (fun y => y * y * y * y * y) _ c
    (fun y => by mach_ring) (hD_y5raw c)

/-! ## Fraction-coefficient machinery

`mach_ring` handles ring structure but not decimal/fraction-literal arithmetic (see the module
docstring). `frac_reduce` is the general field-axiom-based technique (`mul_left_cancel` + `mul_inv`)
for relating a monomial's raw derivative coefficient (`n` copies of `x`) to the clean coefficient the
next Taylor level needs (`x/d`), whenever `n·d = D`. Every denominator beyond `six` is built as a
PRODUCT of small repeated-`1` sums (`twentyfour := four·six`, `onetwenty := five·twentyfour`) so the
factorisation facts `frac_reduce` needs are true by `rfl`, never requiring a large flat sum or a
decimal literal. -/

theorem frac_reduce (n d D : MachLib.Real) (hd : d ≠ 0) (hD : D ≠ 0) (hnd : n * d = D) :
    n * (1 / D) = 1 / d := by
  apply mul_left_cancel hd
  have h1 : d * (n * (1 / D)) = D * (1 / D) := by rw [← hnd]; mach_ring
  rw [h1, mul_inv D hD, mul_inv d hd]

theorem my_two_pos : (0 : MachLib.Real) < 1 + 1 := add_pos zero_lt_one_ax zero_lt_one_ax
theorem my_four_pos : (0 : MachLib.Real) < 1 + 1 + 1 + 1 :=
  add_pos (add_pos (add_pos zero_lt_one_ax zero_lt_one_ax) zero_lt_one_ax) zero_lt_one_ax
theorem my_five_pos : (0 : MachLib.Real) < 1 + 1 + 1 + 1 + 1 :=
  add_pos (add_pos (add_pos (add_pos zero_lt_one_ax zero_lt_one_ax) zero_lt_one_ax) zero_lt_one_ax)
    zero_lt_one_ax
theorem my_six_pos : (0 : MachLib.Real) < 1 + 1 + 1 + 1 + 1 + 1 :=
  add_pos (add_pos (add_pos (add_pos (add_pos zero_lt_one_ax zero_lt_one_ax) zero_lt_one_ax)
    zero_lt_one_ax) zero_lt_one_ax) zero_lt_one_ax

theorem my_two_ne_zero : (1 + 1 : MachLib.Real) ≠ 0 := ne_of_gt my_two_pos
theorem my_four_ne_zero : (1 + 1 + 1 + 1 : MachLib.Real) ≠ 0 := ne_of_gt my_four_pos
theorem my_six_ne_zero : (1 + 1 + 1 + 1 + 1 + 1 : MachLib.Real) ≠ 0 := ne_of_gt my_six_pos

noncomputable def twentyfour : MachLib.Real := (1 + 1 + 1 + 1 : MachLib.Real) * (1 + 1 + 1 + 1 + 1 + 1)
noncomputable def onetwenty : MachLib.Real := (1 + 1 + 1 + 1 + 1 : MachLib.Real) * twentyfour

theorem twentyfour_ne_zero : twentyfour ≠ 0 := by
  unfold twentyfour; exact ne_of_gt (mul_pos my_four_pos my_six_pos)

theorem onetwenty_ne_zero : onetwenty ≠ 0 := by
  unfold onetwenty
  exact ne_of_gt (mul_pos my_five_pos (by unfold twentyfour; exact mul_pos my_four_pos my_six_pos))

/-- `(x+x+x)·(1/6) = x·(1/2)` — the `y³ ↔ y²` coefficient relation (`3/6 = 1/2`). -/
theorem sixth_thrice (x : MachLib.Real) :
    (x + x + x) * (1 / (1 + 1 + 1 + 1 + 1 + 1)) = x * (1 / (1 + 1)) := by
  have hrw : (x + x + x) * (1 / (1 + 1 + 1 + 1 + 1 + 1))
      = ((1 + 1 + 1) * (1 / (1 + 1 + 1 + 1 + 1 + 1))) * x := by mach_ring
  rw [hrw, frac_reduce (1 + 1 + 1) (1 + 1) (1 + 1 + 1 + 1 + 1 + 1) my_two_ne_zero my_six_ne_zero
    (by mach_ring)]
  mach_ring

/-- `(x+x+x+x)·(1/24) = x·(1/6)` — the `y⁴ ↔ y³` coefficient relation (`4/24 = 1/6`). -/
theorem fourth_of_24 (x : MachLib.Real) :
    (x + x + x + x) * (1 / twentyfour) = x * (1 / (1 + 1 + 1 + 1 + 1 + 1)) := by
  have hrw : (x + x + x + x) * (1 / twentyfour) = ((1 + 1 + 1 + 1) * (1 / twentyfour)) * x := by
    mach_ring
  rw [hrw, frac_reduce (1 + 1 + 1 + 1) (1 + 1 + 1 + 1 + 1 + 1) twentyfour my_six_ne_zero
    twentyfour_ne_zero (by unfold twentyfour; rfl)]
  mach_ring

/-- `(x+x+x+x+x)·(1/120) = x·(1/24)` — the `y⁵ ↔ y⁴` coefficient relation (`5/120 = 1/24`). -/
theorem fifth_of_120 (x : MachLib.Real) :
    (x + x + x + x + x) * (1 / onetwenty) = x * (1 / twentyfour) := by
  have hrw : (x + x + x + x + x) * (1 / onetwenty) = ((1 + 1 + 1 + 1 + 1) * (1 / onetwenty)) * x := by
    mach_ring
  rw [hrw, frac_reduce (1 + 1 + 1 + 1 + 1) twentyfour onetwenty twentyfour_ne_zero onetwenty_ne_zero
    (by unfold onetwenty; rfl)]
  mach_ring

/-- **Generic MVT step.** If `f 0 = 0`, `f' = g` everywhere, and `|g(t)| ≤ B` (a CONSTANT) for all
`t ∈ [0,x]`, then `|f(x)| ≤ B·x`. The crude "constant sup times width" Lagrange-style bound — looser
than the sharp integral-based one, but needs only plain MVT (`mean_value_theorem_ct`), not
integration or Cauchy's generalized MVT. Reused at every level below. -/
theorem abs_mvt_step (f g : MachLib.Real → MachLib.Real) (x B : MachLib.Real)
    (hx0 : 0 ≤ x) (hB : 0 ≤ B)
    (hderiv : ∀ c : MachLib.Real, HasDerivAt f (g c) c)
    (hf0 : f 0 = 0)
    (hgB : ∀ t : MachLib.Real, 0 ≤ t → t ≤ x → abs (g t) ≤ B) :
    abs (f x) ≤ B * x := by
  rcases (le_iff_lt_or_eq 0 x).mp hx0 with hlt | heq
  · obtain ⟨c, f', hac, hcb, hd, hval⟩ :=
      mean_value_theorem_ct f 0 x hlt (fun c _ _ => ⟨g c, hderiv c⟩)
    rw [HasDerivAt_unique f f' (g c) c hd (hderiv c)] at hval
    rw [hf0, sub_zero, sub_zero] at hval
    have hstep : abs (f x) = abs (g c) * x := by rw [hval, abs_mul, abs_of_nonneg hx0]
    rw [hstep]
    have h1 : abs (g c) ≤ B := hgB c (le_of_lt hac) (le_of_lt hcb)
    exact mul_le_mul_of_nonneg_right h1 hx0
  · have hx0' : x = 0 := heq.symm
    rw [hx0', show f 0 = 0 from hf0, abs_zero, mul_zero]
    exact le_refl 0

/-! ## The remainder chain, from the innermost (5th) derivative down to `R0`

`R5 = R4' = R3'' = R2''' = R1⁗ = R0⁽⁵⁾` — each `Rk` vanishes at 0 by construction (the polynomial
part matches `sin`'s own Taylor coefficients exactly through degree 5), and `Rk' = R(k-1)` chains
the bound down from `R5` (trivial) to `R0` (`sin(y) − (y − y³/6 + y⁵/120)`, the actual hardware
remainder). -/

/-- `R5(y) = cos y − 1`. -/
noncomputable def R5 (y : MachLib.Real) : MachLib.Real := cos y - 1

theorem R5_deriv : ∀ c : MachLib.Real, HasDerivAt R5 (-sin c) c := by
  intro c
  exact hasDerivAt_congr_val
    (HasDerivAt_sub cos (fun _ => 1) (-sin c) 0 c (HasDerivAt_cos c) (HasDerivAt_const 1 c))
    (by mach_ring)

theorem R5_zero : R5 0 = 0 := by unfold R5; rw [cos_zero]; mach_ring

/-- `|cos(x) − 1| ≤ x` for `x ≥ 0`. -/
theorem R5_bound (x : MachLib.Real) (hx0 : 0 ≤ x) : abs (R5 x) ≤ 1 * x := by
  apply abs_mvt_step R5 (fun c => -sin c) x 1 hx0 (le_of_lt zero_lt_one_ax) R5_deriv R5_zero
  intro t _ _; rw [abs_neg]; exact abs_sin_le_one t

/-- `R4(y) = sin y − y`. -/
noncomputable def R4 (y : MachLib.Real) : MachLib.Real := sin y - y

theorem R4_deriv : ∀ c : MachLib.Real, HasDerivAt R4 (R5 c) c := by
  intro c
  exact hasDerivAt_congr_val
    (HasDerivAt_sub sin (fun y => y) (cos c) 1 c (HasDerivAt_sin c) (HasDerivAt_id c))
    (by unfold R5; mach_ring)

theorem R4_zero : R4 0 = 0 := by unfold R4; rw [sin_zero]; mach_ring

/-- `|sin(x) − x| ≤ x²` for `x ≥ 0`. -/
theorem R4_bound (x : MachLib.Real) (hx0 : 0 ≤ x) : abs (R4 x) ≤ x * x := by
  apply abs_mvt_step R4 R5 x x hx0 hx0 R4_deriv R4_zero
  intro t ht0 htx
  have h1 : abs (R5 t) ≤ 1 * t := R5_bound t ht0
  rw [one_mul_thm] at h1
  exact le_trans h1 htx

/-- `R3(y) = 1 − y²/2 − cos y`. -/
noncomputable def R3 (y : MachLib.Real) : MachLib.Real :=
  1 - y * y * ((1 / (1 + 1) : MachLib.Real)) - cos y

theorem R3_deriv : ∀ c : MachLib.Real, HasDerivAt R3 (R4 c) c := by
  intro c
  have hyy2 : HasDerivAt (fun y => y * y * ((1 / (1 + 1) : MachLib.Real)))
      ((c + c) * ((1 / (1 + 1) : MachLib.Real)) + (c * c) * 0) c :=
    HasDerivAt_mul (fun y => y * y) (fun _ => (1 / (1 + 1) : MachLib.Real)) (c + c) 0 c
      (hD_y2 c) (HasDerivAt_const (1 / (1 + 1) : MachLib.Real) c)
  have hsub1 : HasDerivAt (fun y => (1 : MachLib.Real) - y * y * ((1 / (1 + 1) : MachLib.Real)))
      (0 - ((c + c) * ((1 / (1 + 1) : MachLib.Real)) + (c * c) * 0)) c :=
    HasDerivAt_sub (fun _ => 1) (fun y => y * y * ((1 / (1 + 1) : MachLib.Real))) 0 _ c
      (HasDerivAt_const 1 c) hyy2
  have hfull := HasDerivAt_sub (fun y => (1 : MachLib.Real) - y * y * (1 / (1 + 1) : MachLib.Real))
    cos _ (-sin c) c hsub1 (HasDerivAt_cos c)
  have hclean : (0 - ((c + c) * (1 / (1 + 1) : MachLib.Real) + (c * c) * 0)) - -sin c = R4 c := by
    unfold R4
    have hdh : (c + c) * (1 / (1 + 1)) = c := by
      have step : (c + c) * (1 / (1 + 1)) = c * (1 / (1 + 1) + 1 / (1 + 1)) := by mach_ring
      have hah : (1 : MachLib.Real) / (1 + 1) + 1 / (1 + 1) = 1 := by
        have hgen : ∀ h : MachLib.Real, h + h = (1 + 1) * h := by intro h; mach_ring
        rw [hgen (1 / (1 + 1))]; exact mul_inv (1 + 1) my_two_ne_zero
      rw [step, hah]; mach_ring
    have hrearr : (0 : MachLib.Real) - ((c + c) * (1 / (1 + 1)) + c * c * 0) - -sin c
        = sin c - (c + c) * (1 / (1 + 1)) := by mach_ring
    rw [hrearr, hdh]
  exact hasDerivAt_congr_val hfull hclean

theorem R3_zero : R3 0 = 0 := by unfold R3; rw [cos_zero]; mach_ring

/-- `|1 − x²/2 − cos(x)| ≤ x³` for `x ≥ 0`. -/
theorem R3_bound (x : MachLib.Real) (hx0 : 0 ≤ x) : abs (R3 x) ≤ (x * x) * x := by
  apply abs_mvt_step R3 R4 x (x * x) hx0 (mul_nonneg hx0 hx0) R3_deriv R3_zero
  intro t ht0 htx
  have h1 : abs (R4 t) ≤ t * t := R4_bound t ht0
  have h2 : t * t ≤ x * x :=
    le_trans (mul_le_mul_of_nonneg_right htx ht0) (mul_le_mul_of_nonneg_left htx hx0)
  exact le_trans h1 h2

/-- `R2(y) = −sin y + y − y³/6`. -/
noncomputable def R2 (y : MachLib.Real) : MachLib.Real :=
  -sin y + y - y * y * y * ((1 / (1 + 1 + 1 + 1 + 1 + 1) : MachLib.Real))

theorem R2_deriv : ∀ c : MachLib.Real, HasDerivAt R2 (R3 c) c := by
  intro c
  have hy3 : HasDerivAt (fun y => y * y * y * ((1 / (1 + 1 + 1 + 1 + 1 + 1) : MachLib.Real)))
      ((c * c + c * c + c * c) * (1 / (1 + 1 + 1 + 1 + 1 + 1) : MachLib.Real) + (c * c * c) * 0) c :=
    HasDerivAt_mul (fun y => y * y * y) (fun _ => (1 / (1 + 1 + 1 + 1 + 1 + 1) : MachLib.Real))
      (c * c + c * c + c * c) 0 c (hD_y3 c) (HasDerivAt_const (1 / (1 + 1 + 1 + 1 + 1 + 1) : MachLib.Real) c)
  have hnegsin : HasDerivAt (fun y => -sin y) (-cos c) c :=
    HasDerivAt_neg sin (cos c) c (HasDerivAt_sin c)
  have hadd : HasDerivAt (fun y => -sin y + y) (-cos c + 1) c :=
    HasDerivAt_add (fun y => -sin y) (fun y => y) (-cos c) 1 c hnegsin (HasDerivAt_id c)
  have hfull := HasDerivAt_sub (fun y => -sin y + y)
    (fun y => y * y * y * (1 / (1 + 1 + 1 + 1 + 1 + 1) : MachLib.Real)) (-cos c + 1) _ c hadd hy3
  have hclean : (-cos c + 1)
      - ((c * c + c * c + c * c) * (1 / (1 + 1 + 1 + 1 + 1 + 1) : MachLib.Real) + (c * c * c) * 0)
      = R3 c := by
    unfold R3
    rw [show (c * c + c * c + c * c) * (1 / (1 + 1 + 1 + 1 + 1 + 1) : MachLib.Real) + (c * c * c) * 0
        = (c * c + c * c + c * c) * (1 / (1 + 1 + 1 + 1 + 1 + 1) : MachLib.Real) from by mach_ring]
    rw [sixth_thrice (c * c)]
    mach_ring
  exact hasDerivAt_congr_val hfull hclean

theorem R2_zero : R2 0 = 0 := by unfold R2; rw [sin_zero]; mach_ring

/-- `|−sin(x) + x − x³/6| ≤ x⁴` for `x ≥ 0`. -/
theorem R2_bound (x : MachLib.Real) (hx0 : 0 ≤ x) : abs (R2 x) ≤ ((x * x) * x) * x := by
  apply abs_mvt_step R2 R3 x ((x * x) * x) hx0 (mul_nonneg (mul_nonneg hx0 hx0) hx0) R2_deriv R2_zero
  intro t ht0 htx
  have h1 : abs (R3 t) ≤ (t * t) * t := R3_bound t ht0
  have h2 : (t * t) * t ≤ (x * x) * x := by
    have ha : t * t ≤ x * x :=
      le_trans (mul_le_mul_of_nonneg_right htx ht0) (mul_le_mul_of_nonneg_left htx hx0)
    exact le_trans (mul_le_mul_of_nonneg_right ha ht0) (mul_le_mul_of_nonneg_left htx (mul_nonneg hx0 hx0))
  exact le_trans h1 h2

/-- `R1(y) = cos y − 1 + y²/2 − y⁴/24`. -/
noncomputable def R1 (y : MachLib.Real) : MachLib.Real :=
  cos y - 1 + y * y * ((1 / (1 + 1) : MachLib.Real)) - y * y * y * y * ((1 / twentyfour : MachLib.Real))

theorem R1_deriv : ∀ c : MachLib.Real, HasDerivAt R1 (R2 c) c := by
  intro c
  have hyy2 : HasDerivAt (fun y => y * y * ((1 / (1 + 1) : MachLib.Real)))
      ((c + c) * ((1 / (1 + 1) : MachLib.Real)) + (c * c) * 0) c :=
    HasDerivAt_mul (fun y => y * y) (fun _ => (1 / (1 + 1) : MachLib.Real)) (c + c) 0 c (hD_y2 c)
      (HasDerivAt_const (1 / (1 + 1) : MachLib.Real) c)
  have hy4 : HasDerivAt (fun y => y * y * y * y * ((1 / twentyfour : MachLib.Real)))
      (((c + c) * (c * c) + (c * c) * (c + c)) * (1 / twentyfour : MachLib.Real) + (c * c * c * c) * 0) c :=
    HasDerivAt_mul (fun y => y * y * y * y) (fun _ => (1 / twentyfour : MachLib.Real))
      ((c + c) * (c * c) + (c * c) * (c + c)) 0 c (hD_y4 c) (HasDerivAt_const (1 / twentyfour : MachLib.Real) c)
  have h1 : HasDerivAt (fun y => cos y - 1) (-sin c - 0) c :=
    HasDerivAt_sub cos (fun _ => 1) (-sin c) 0 c (HasDerivAt_cos c) (HasDerivAt_const 1 c)
  have h2 : HasDerivAt (fun y => cos y - 1 + y * y * ((1 / (1 + 1) : MachLib.Real)))
      ((-sin c - 0) + ((c + c) * ((1 / (1 + 1) : MachLib.Real)) + (c * c) * 0)) c :=
    HasDerivAt_add (fun y => cos y - 1) (fun y => y * y * ((1 / (1 + 1) : MachLib.Real)))
      (-sin c - 0) _ c h1 hyy2
  have hfull := HasDerivAt_sub (fun y => cos y - 1 + y * y * ((1 / (1 + 1) : MachLib.Real)))
    (fun y => y * y * y * y * ((1 / twentyfour : MachLib.Real))) _ _ c h2 hy4
  have hclean : ((-sin c - 0) + ((c + c) * ((1 / (1 + 1) : MachLib.Real)) + (c * c) * 0))
      - (((c + c) * (c * c) + (c * c) * (c + c)) * (1 / twentyfour : MachLib.Real) + (c * c * c * c) * 0)
      = R2 c := by
    unfold R2
    have hdh : (c + c) * (1 / (1 + 1)) = c := by
      have step : (c + c) * (1 / (1 + 1)) = c * (1 / (1 + 1) + 1 / (1 + 1)) := by mach_ring
      have hah : (1 : MachLib.Real) / (1 + 1) + 1 / (1 + 1) = 1 := by
        have hgen : ∀ h : MachLib.Real, h + h = (1 + 1) * h := by intro h; mach_ring
        rw [hgen (1 / (1 + 1))]; exact mul_inv (1 + 1) my_two_ne_zero
      rw [step, hah]; mach_ring
    have hy4simp : ((c + c) * (c * c) + (c * c) * (c + c)) * (1 / twentyfour : MachLib.Real) + (c * c * c * c) * 0
        = (c * c * c + c * c * c + c * c * c + c * c * c) * (1 / twentyfour) := by mach_ring
    rw [hy4simp, fourth_of_24 (c * c * c)]
    rw [show (-sin c - 0) + ((c + c) * (1 / (1 + 1)) + (c * c) * 0) - (c * c * c) * (1 / (1 + 1 + 1 + 1 + 1 + 1))
        = -sin c + (c + c) * (1 / (1 + 1)) - (c * c * c) * (1 / (1 + 1 + 1 + 1 + 1 + 1)) from by mach_ring]
    rw [hdh]
  exact hasDerivAt_congr_val hfull hclean

theorem R1_zero : R1 0 = 0 := by unfold R1; rw [cos_zero]; mach_ring

/-- `|cos(x) − 1 + x²/2 − x⁴/24| ≤ x⁵` for `x ≥ 0`. -/
theorem R1_bound (x : MachLib.Real) (hx0 : 0 ≤ x) : abs (R1 x) ≤ (((x * x) * x) * x) * x := by
  apply abs_mvt_step R1 R2 x (((x * x) * x) * x) hx0
    (mul_nonneg (mul_nonneg (mul_nonneg hx0 hx0) hx0) hx0) R1_deriv R1_zero
  intro t ht0 htx
  have h1 : abs (R2 t) ≤ ((t * t) * t) * t := R2_bound t ht0
  have h2 : ((t * t) * t) * t ≤ ((x * x) * x) * x := by
    have ha : t * t ≤ x * x :=
      le_trans (mul_le_mul_of_nonneg_right htx ht0) (mul_le_mul_of_nonneg_left htx hx0)
    have hb : (t * t) * t ≤ (x * x) * x :=
      le_trans (mul_le_mul_of_nonneg_right ha ht0) (mul_le_mul_of_nonneg_left htx (mul_nonneg hx0 hx0))
    exact le_trans (mul_le_mul_of_nonneg_right hb ht0)
      (mul_le_mul_of_nonneg_left htx (mul_nonneg (mul_nonneg hx0 hx0) hx0))
  exact le_trans h1 h2

/-- **`R0(y) = sin y − y + y³/6 − y⁵/120`** — exactly the hardware's actual forward-error remainder
(`eml_sin.v`'s Maclaurin truncation subtracted from the true `sin`). -/
noncomputable def R0 (y : MachLib.Real) : MachLib.Real :=
  sin y - y + y * y * y * ((1 / (1 + 1 + 1 + 1 + 1 + 1) : MachLib.Real))
    - y * y * y * y * y * ((1 / onetwenty : MachLib.Real))

theorem R0_deriv : ∀ c : MachLib.Real, HasDerivAt R0 (R1 c) c := by
  intro c
  have hy3 : HasDerivAt (fun y => y * y * y * ((1 / (1 + 1 + 1 + 1 + 1 + 1) : MachLib.Real)))
      ((c * c + c * c + c * c) * (1 / (1 + 1 + 1 + 1 + 1 + 1) : MachLib.Real) + (c * c * c) * 0) c :=
    HasDerivAt_mul (fun y => y * y * y) (fun _ => (1 / (1 + 1 + 1 + 1 + 1 + 1) : MachLib.Real))
      (c * c + c * c + c * c) 0 c (hD_y3 c) (HasDerivAt_const (1 / (1 + 1 + 1 + 1 + 1 + 1) : MachLib.Real) c)
  have hy5 : HasDerivAt (fun y => y * y * y * y * y * ((1 / onetwenty : MachLib.Real)))
      (((c + c) * (c * c * c) + (c * c) * (c * c + c * c + c * c)) * (1 / onetwenty : MachLib.Real)
        + (c * c * c * c * c) * 0) c :=
    HasDerivAt_mul (fun y => y * y * y * y * y) (fun _ => (1 / onetwenty : MachLib.Real))
      ((c + c) * (c * c * c) + (c * c) * (c * c + c * c + c * c)) 0 c (hD_y5 c)
      (HasDerivAt_const (1 / onetwenty : MachLib.Real) c)
  have h1 : HasDerivAt (fun y => sin y - y) (cos c - 1) c :=
    HasDerivAt_sub sin (fun y => y) (cos c) 1 c (HasDerivAt_sin c) (HasDerivAt_id c)
  have h2 : HasDerivAt (fun y => sin y - y + y * y * y * ((1 / (1 + 1 + 1 + 1 + 1 + 1) : MachLib.Real)))
      ((cos c - 1) + ((c * c + c * c + c * c) * (1 / (1 + 1 + 1 + 1 + 1 + 1) : MachLib.Real) + (c * c * c) * 0)) c :=
    HasDerivAt_add (fun y => sin y - y) (fun y => y * y * y * ((1 / (1 + 1 + 1 + 1 + 1 + 1) : MachLib.Real)))
      (cos c - 1) _ c h1 hy3
  have hfull := HasDerivAt_sub (fun y => sin y - y + y * y * y * ((1 / (1 + 1 + 1 + 1 + 1 + 1) : MachLib.Real)))
    (fun y => y * y * y * y * y * ((1 / onetwenty : MachLib.Real))) _ _ c h2 hy5
  have hclean : ((cos c - 1) + ((c * c + c * c + c * c) * (1 / (1 + 1 + 1 + 1 + 1 + 1) : MachLib.Real) + (c * c * c) * 0))
      - (((c + c) * (c * c * c) + (c * c) * (c * c + c * c + c * c)) * (1 / onetwenty : MachLib.Real)
        + (c * c * c * c * c) * 0)
      = R1 c := by
    unfold R1
    have hy3simp : (c * c + c * c + c * c) * (1 / (1 + 1 + 1 + 1 + 1 + 1) : MachLib.Real) + (c * c * c) * 0
        = (c * c) * (1 / (1 + 1)) := by
      rw [show (c * c + c * c + c * c) * (1 / (1 + 1 + 1 + 1 + 1 + 1) : MachLib.Real) + (c * c * c) * 0
          = (c * c + c * c + c * c) * (1 / (1 + 1 + 1 + 1 + 1 + 1) : MachLib.Real) from by mach_ring]
      exact sixth_thrice (c * c)
    have hy5simp : ((c + c) * (c * c * c) + (c * c) * (c * c + c * c + c * c)) * (1 / onetwenty : MachLib.Real)
        + (c * c * c * c * c) * 0 = (c * c * c * c) * (1 / twentyfour) := by
      rw [show ((c + c) * (c * c * c) + (c * c) * (c * c + c * c + c * c)) * (1 / onetwenty : MachLib.Real)
          + (c * c * c * c * c) * 0
          = (c * c * c * c + c * c * c * c + c * c * c * c + c * c * c * c + c * c * c * c) * (1 / onetwenty)
          from by mach_ring]
      exact fifth_of_120 (c * c * c * c)
    rw [hy3simp, hy5simp]
  exact hasDerivAt_congr_val hfull hclean

theorem R0_zero : R0 0 = 0 := by unfold R0; rw [sin_zero]; mach_ring

/-- **The main result.** `|sin(x) − (x − x³/6 + x⁵/120)| ≤ x⁶` for `x ≥ 0` — the real-valued
forward-error bound for `eml_sin.v`'s exact 3-term Maclaurin truncation. `sorryAx`-free. -/
theorem R0_bound (x : MachLib.Real) (hx0 : 0 ≤ x) :
    abs (R0 x) ≤ ((((x * x) * x) * x) * x) * x := by
  apply abs_mvt_step R0 R1 x ((((x * x) * x) * x) * x) hx0
    (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hx0 hx0) hx0) hx0) hx0) R0_deriv R0_zero
  intro t ht0 htx
  have h1 : abs (R1 t) ≤ (((t * t) * t) * t) * t := R1_bound t ht0
  have h2 : (((t * t) * t) * t) * t ≤ (((x * x) * x) * x) * x := by
    have ha : t * t ≤ x * x :=
      le_trans (mul_le_mul_of_nonneg_right htx ht0) (mul_le_mul_of_nonneg_left htx hx0)
    have hb : (t * t) * t ≤ (x * x) * x :=
      le_trans (mul_le_mul_of_nonneg_right ha ht0) (mul_le_mul_of_nonneg_left htx (mul_nonneg hx0 hx0))
    have hc : ((t * t) * t) * t ≤ ((x * x) * x) * x :=
      le_trans (mul_le_mul_of_nonneg_right hb ht0)
        (mul_le_mul_of_nonneg_left htx (mul_nonneg (mul_nonneg hx0 hx0) hx0))
    exact le_trans (mul_le_mul_of_nonneg_right hc ht0)
      (mul_le_mul_of_nonneg_left htx (mul_nonneg (mul_nonneg (mul_nonneg hx0 hx0) hx0) hx0))
  exact le_trans h1 h2
