import MachLib.SinTaylorRemainder
import MachLib.HyperbolicLipschitz

/-!
# The real-valued sinh Taylor-remainder bound — breadth: hyperbolic family, reusing sin's machinery

`eml_sinh.v` (Forge's hardware `sinh`) implements the SAME 3-term Maclaurin shape as `eml_sin.v` —
`sinh(x) ≈ x + x³/6 + x⁵/120`, valid on `[-1,1]` — but with every term `+` instead of alternating,
since `sinh` and `cosh` satisfy `sinh' = cosh`, `cosh' = sinh` (period 2, no sign flip anywhere),
unlike `sin'=cos`, `cos'=-sin` (period 4, alternating). This makes the MVT chain itself SIMPLER than
`SinTaylorRemainder` (no sign-flip `mach_ring` quirk to route around) but the base case is harder:
`sin`/`cos` are globally bounded by `1`, while `sinh`/`cosh` are unbounded, so the chain instead
carries a `sinh(x)` factor throughout (via `sinh_mono`/`sinh_nonneg`, already in `HyperbolicLipschitz`),
giving `|sinh(x) − (x+x³/6+x⁵/120)| ≤ sinh(x)·x⁶` rather than a pure monomial. Still an honest,
checkable, `sorryAx`-free bound — Python's `math.sinh` computes the extra factor exactly.

**Reuse from `SinTaylorRemainder`**: `abs_mvt_step`, `hD_y2..hD_y5`, `frac_reduce`,
`sixth_thrice`/`fourth_of_24`/`fifth_of_120`, `twentyfour`/`onetwenty` are all sign- and
function-independent (pure polynomial-derivative / fraction facts) and are reused verbatim —
zero new coefficient machinery needed.
-/

namespace MachLib.Real

/-- `Rsh5(y) = cosh y − 1`. -/
noncomputable def Rsh5 (y : Real) : Real := cosh y - 1

theorem Rsh5_deriv : ∀ c : Real, HasDerivAt Rsh5 (sinh c) c := by
  intro c
  exact hasDerivAt_congr_val
    (HasDerivAt_sub cosh (fun _ => 1) (sinh c) 0 c (HasDerivAt_cosh c) (HasDerivAt_const 1 c))
    (by mach_ring)

theorem Rsh5_zero : Rsh5 0 = 0 := by unfold Rsh5; rw [cosh_zero]; mach_ring

/-- `|cosh(x) − 1| ≤ sinh(x)·x` for `x ≥ 0`. -/
theorem Rsh5_bound (x : Real) (hx0 : 0 ≤ x) : abs (Rsh5 x) ≤ sinh x * x := by
  apply abs_mvt_step Rsh5 sinh x (sinh x) hx0 (sinh_nonneg hx0) Rsh5_deriv Rsh5_zero
  intro t ht0 htx
  rw [abs_of_nonneg (sinh_nonneg ht0)]
  exact sinh_mono htx

/-- `Rsh4(y) = sinh y − y`. -/
noncomputable def Rsh4 (y : Real) : Real := sinh y - y

theorem Rsh4_deriv : ∀ c : Real, HasDerivAt Rsh4 (Rsh5 c) c := by
  intro c
  exact hasDerivAt_congr_val
    (HasDerivAt_sub sinh (fun y => y) (cosh c) 1 c (HasDerivAt_sinh c) (HasDerivAt_id c))
    (by unfold Rsh5; mach_ring)

theorem Rsh4_zero : Rsh4 0 = 0 := by unfold Rsh4; rw [sinh_zero]; mach_ring

/-- `|sinh(x) − x| ≤ (sinh(x)·x)·x` for `x ≥ 0`. -/
theorem Rsh4_bound (x : Real) (hx0 : 0 ≤ x) : abs (Rsh4 x) ≤ (sinh x * x) * x := by
  apply abs_mvt_step Rsh4 Rsh5 x (sinh x * x) hx0 (mul_nonneg (sinh_nonneg hx0) hx0)
    Rsh4_deriv Rsh4_zero
  intro t ht0 htx
  have h1 : abs (Rsh5 t) ≤ sinh t * t := Rsh5_bound t ht0
  have h2 : sinh t * t ≤ sinh x * x :=
    le_trans (mul_le_mul_of_nonneg_right (sinh_mono htx) ht0)
      (mul_le_mul_of_nonneg_left htx (sinh_nonneg hx0))
  exact le_trans h1 h2

/-- `Rsh3(y) = cosh y − 1 − y²/2`. -/
noncomputable def Rsh3 (y : Real) : Real :=
  cosh y - 1 - y * y * ((1 / (1 + 1) : Real))

theorem Rsh3_deriv : ∀ c : Real, HasDerivAt Rsh3 (Rsh4 c) c := by
  intro c
  have hyy2 : HasDerivAt (fun y => y * y * ((1 / (1 + 1) : Real)))
      ((c + c) * ((1 / (1 + 1) : Real)) + (c * c) * 0) c :=
    HasDerivAt_mul (fun y => y * y) (fun _ => (1 / (1 + 1) : Real)) (c + c) 0 c
      (hD_y2 c) (HasDerivAt_const (1 / (1 + 1) : Real) c)
  have hsub1 : HasDerivAt (fun y => cosh y - 1) (sinh c - 0) c :=
    HasDerivAt_sub cosh (fun _ => 1) (sinh c) 0 c (HasDerivAt_cosh c) (HasDerivAt_const 1 c)
  have hfull := HasDerivAt_sub (fun y => cosh y - 1) (fun y => y * y * ((1 / (1 + 1) : Real)))
    (sinh c - 0) _ c hsub1 hyy2
  have hclean : (sinh c - 0) - ((c + c) * ((1 / (1 + 1) : Real)) + (c * c) * 0) = Rsh4 c := by
    unfold Rsh4
    have hdh : (c + c) * (1 / (1 + 1)) = c := by
      have step : (c + c) * (1 / (1 + 1)) = c * (1 / (1 + 1) + 1 / (1 + 1)) := by mach_ring
      have hah : (1 : Real) / (1 + 1) + 1 / (1 + 1) = 1 := by
        have hgen : ∀ h : Real, h + h = (1 + 1) * h := by intro h; mach_ring
        rw [hgen (1 / (1 + 1))]; exact mul_inv (1 + 1) my_two_ne_zero
      rw [step, hah]; mach_ring
    rw [show (sinh c - 0) - ((c + c) * (1 / (1 + 1)) + c * c * 0) = sinh c - (c + c) * (1 / (1 + 1))
        from by mach_ring, hdh]
  exact hasDerivAt_congr_val hfull hclean

theorem Rsh3_zero : Rsh3 0 = 0 := by unfold Rsh3; rw [cosh_zero]; mach_ring

/-- `|cosh(x) − 1 − x²/2| ≤ ((sinh(x)·x)·x)·x` for `x ≥ 0`. -/
theorem Rsh3_bound (x : Real) (hx0 : 0 ≤ x) : abs (Rsh3 x) ≤ ((sinh x * x) * x) * x := by
  apply abs_mvt_step Rsh3 Rsh4 x ((sinh x * x) * x) hx0
    (mul_nonneg (mul_nonneg (sinh_nonneg hx0) hx0) hx0) Rsh3_deriv Rsh3_zero
  intro t ht0 htx
  have h1 : abs (Rsh4 t) ≤ (sinh t * t) * t := Rsh4_bound t ht0
  have h2 : (sinh t * t) * t ≤ (sinh x * x) * x := by
    have ha : sinh t * t ≤ sinh x * x :=
      le_trans (mul_le_mul_of_nonneg_right (sinh_mono htx) ht0)
        (mul_le_mul_of_nonneg_left htx (sinh_nonneg hx0))
    exact le_trans (mul_le_mul_of_nonneg_right ha ht0)
      (mul_le_mul_of_nonneg_left htx (mul_nonneg (sinh_nonneg hx0) hx0))
  exact le_trans h1 h2

/-- `Rsh2(y) = sinh y − y − y³/6`. -/
noncomputable def Rsh2 (y : Real) : Real :=
  sinh y - y - y * y * y * ((1 / (1 + 1 + 1 + 1 + 1 + 1) : Real))

theorem Rsh2_deriv : ∀ c : Real, HasDerivAt Rsh2 (Rsh3 c) c := by
  intro c
  have hy3 : HasDerivAt (fun y => y * y * y * ((1 / (1 + 1 + 1 + 1 + 1 + 1) : Real)))
      ((c * c + c * c + c * c) * (1 / (1 + 1 + 1 + 1 + 1 + 1) : Real) + (c * c * c) * 0) c :=
    HasDerivAt_mul (fun y => y * y * y) (fun _ => (1 / (1 + 1 + 1 + 1 + 1 + 1) : Real))
      (c * c + c * c + c * c) 0 c (hD_y3 c)
      (HasDerivAt_const (1 / (1 + 1 + 1 + 1 + 1 + 1) : Real) c)
  have hsub : HasDerivAt (fun y => sinh y - y) (cosh c - 1) c :=
    HasDerivAt_sub sinh (fun y => y) (cosh c) 1 c (HasDerivAt_sinh c) (HasDerivAt_id c)
  have hfull := HasDerivAt_sub (fun y => sinh y - y)
    (fun y => y * y * y * (1 / (1 + 1 + 1 + 1 + 1 + 1) : Real)) (cosh c - 1) _ c hsub hy3
  have hclean : (cosh c - 1)
      - ((c * c + c * c + c * c) * (1 / (1 + 1 + 1 + 1 + 1 + 1) : Real) + (c * c * c) * 0)
      = Rsh3 c := by
    unfold Rsh3
    rw [show (c * c + c * c + c * c) * (1 / (1 + 1 + 1 + 1 + 1 + 1) : Real) + (c * c * c) * 0
        = (c * c + c * c + c * c) * (1 / (1 + 1 + 1 + 1 + 1 + 1) : Real) from by mach_ring]
    rw [sixth_thrice (c * c)]
  exact hasDerivAt_congr_val hfull hclean

theorem Rsh2_zero : Rsh2 0 = 0 := by unfold Rsh2; rw [sinh_zero]; mach_ring

/-- `|sinh(x) − x − x³/6| ≤ (((sinh(x)·x)·x)·x)·x` for `x ≥ 0`. -/
theorem Rsh2_bound (x : Real) (hx0 : 0 ≤ x) : abs (Rsh2 x) ≤ (((sinh x * x) * x) * x) * x := by
  apply abs_mvt_step Rsh2 Rsh3 x (((sinh x * x) * x) * x) hx0
    (mul_nonneg (mul_nonneg (mul_nonneg (sinh_nonneg hx0) hx0) hx0) hx0) Rsh2_deriv Rsh2_zero
  intro t ht0 htx
  have h1 : abs (Rsh3 t) ≤ ((sinh t * t) * t) * t := Rsh3_bound t ht0
  have h2 : ((sinh t * t) * t) * t ≤ ((sinh x * x) * x) * x := by
    have ha : sinh t * t ≤ sinh x * x :=
      le_trans (mul_le_mul_of_nonneg_right (sinh_mono htx) ht0)
        (mul_le_mul_of_nonneg_left htx (sinh_nonneg hx0))
    have hb : (sinh t * t) * t ≤ (sinh x * x) * x :=
      le_trans (mul_le_mul_of_nonneg_right ha ht0)
        (mul_le_mul_of_nonneg_left htx (mul_nonneg (sinh_nonneg hx0) hx0))
    exact le_trans (mul_le_mul_of_nonneg_right hb ht0)
      (mul_le_mul_of_nonneg_left htx (mul_nonneg (mul_nonneg (sinh_nonneg hx0) hx0) hx0))
  exact le_trans h1 h2

/-- `Rsh1(y) = cosh y − 1 − y²/2 − y⁴/24`. -/
noncomputable def Rsh1 (y : Real) : Real :=
  cosh y - 1 - y * y * ((1 / (1 + 1) : Real)) - y * y * y * y * ((1 / twentyfour : Real))

theorem Rsh1_deriv : ∀ c : Real, HasDerivAt Rsh1 (Rsh2 c) c := by
  intro c
  have hyy2 : HasDerivAt (fun y => y * y * ((1 / (1 + 1) : Real)))
      ((c + c) * ((1 / (1 + 1) : Real)) + (c * c) * 0) c :=
    HasDerivAt_mul (fun y => y * y) (fun _ => (1 / (1 + 1) : Real)) (c + c) 0 c (hD_y2 c)
      (HasDerivAt_const (1 / (1 + 1) : Real) c)
  have hy4 : HasDerivAt (fun y => y * y * y * y * ((1 / twentyfour : Real)))
      (((c + c) * (c * c) + (c * c) * (c + c)) * (1 / twentyfour : Real) + (c * c * c * c) * 0) c :=
    HasDerivAt_mul (fun y => y * y * y * y) (fun _ => (1 / twentyfour : Real))
      ((c + c) * (c * c) + (c * c) * (c + c)) 0 c (hD_y4 c)
      (HasDerivAt_const (1 / twentyfour : Real) c)
  have h1 : HasDerivAt (fun y => cosh y - 1) (sinh c - 0) c :=
    HasDerivAt_sub cosh (fun _ => 1) (sinh c) 0 c (HasDerivAt_cosh c) (HasDerivAt_const 1 c)
  have h2 : HasDerivAt (fun y => cosh y - 1 - y * y * ((1 / (1 + 1) : Real)))
      ((sinh c - 0) - ((c + c) * ((1 / (1 + 1) : Real)) + (c * c) * 0)) c :=
    HasDerivAt_sub (fun y => cosh y - 1) (fun y => y * y * ((1 / (1 + 1) : Real)))
      (sinh c - 0) _ c h1 hyy2
  have hfull := HasDerivAt_sub (fun y => cosh y - 1 - y * y * ((1 / (1 + 1) : Real)))
    (fun y => y * y * y * y * ((1 / twentyfour : Real))) _ _ c h2 hy4
  have hclean : ((sinh c - 0) - ((c + c) * ((1 / (1 + 1) : Real)) + (c * c) * 0))
      - (((c + c) * (c * c) + (c * c) * (c + c)) * (1 / twentyfour : Real) + (c * c * c * c) * 0)
      = Rsh2 c := by
    unfold Rsh2
    have hdh : (c + c) * (1 / (1 + 1)) = c := by
      have step : (c + c) * (1 / (1 + 1)) = c * (1 / (1 + 1) + 1 / (1 + 1)) := by mach_ring
      have hah : (1 : Real) / (1 + 1) + 1 / (1 + 1) = 1 := by
        have hgen : ∀ h : Real, h + h = (1 + 1) * h := by intro h; mach_ring
        rw [hgen (1 / (1 + 1))]; exact mul_inv (1 + 1) my_two_ne_zero
      rw [step, hah]; mach_ring
    have hy4simp : ((c + c) * (c * c) + (c * c) * (c + c)) * (1 / twentyfour : Real) + (c * c * c * c) * 0
        = (c * c * c + c * c * c + c * c * c + c * c * c) * (1 / twentyfour) := by mach_ring
    rw [hy4simp, fourth_of_24 (c * c * c)]
    rw [show (sinh c - 0) - ((c + c) * (1 / (1 + 1)) + (c * c) * 0) - (c * c * c) * (1 / (1 + 1 + 1 + 1 + 1 + 1))
        = sinh c - (c + c) * (1 / (1 + 1)) - (c * c * c) * (1 / (1 + 1 + 1 + 1 + 1 + 1)) from by mach_ring]
    rw [hdh]
  exact hasDerivAt_congr_val hfull hclean

theorem Rsh1_zero : Rsh1 0 = 0 := by unfold Rsh1; rw [cosh_zero]; mach_ring

/-- `|cosh(x) − 1 − x²/2 − x⁴/24| ≤ ((((sinh(x)·x)·x)·x)·x)·x` for `x ≥ 0`. -/
theorem Rsh1_bound (x : Real) (hx0 : 0 ≤ x) :
    abs (Rsh1 x) ≤ ((((sinh x * x) * x) * x) * x) * x := by
  apply abs_mvt_step Rsh1 Rsh2 x ((((sinh x * x) * x) * x) * x) hx0
    (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (sinh_nonneg hx0) hx0) hx0) hx0) hx0)
    Rsh1_deriv Rsh1_zero
  intro t ht0 htx
  have h1 : abs (Rsh2 t) ≤ (((sinh t * t) * t) * t) * t := Rsh2_bound t ht0
  have h2 : (((sinh t * t) * t) * t) * t ≤ (((sinh x * x) * x) * x) * x := by
    have ha : sinh t * t ≤ sinh x * x :=
      le_trans (mul_le_mul_of_nonneg_right (sinh_mono htx) ht0)
        (mul_le_mul_of_nonneg_left htx (sinh_nonneg hx0))
    have hb : (sinh t * t) * t ≤ (sinh x * x) * x :=
      le_trans (mul_le_mul_of_nonneg_right ha ht0)
        (mul_le_mul_of_nonneg_left htx (mul_nonneg (sinh_nonneg hx0) hx0))
    have hc : ((sinh t * t) * t) * t ≤ ((sinh x * x) * x) * x :=
      le_trans (mul_le_mul_of_nonneg_right hb ht0)
        (mul_le_mul_of_nonneg_left htx (mul_nonneg (mul_nonneg (sinh_nonneg hx0) hx0) hx0))
    exact le_trans (mul_le_mul_of_nonneg_right hc ht0)
      (mul_le_mul_of_nonneg_left htx (mul_nonneg (mul_nonneg (mul_nonneg (sinh_nonneg hx0) hx0) hx0) hx0))
  exact le_trans h1 h2

/-- **`Rsh0(y) = sinh y − y − y³/6 − y⁵/120`** — exactly `eml_sinh.v`'s forward-error remainder
against its true 3-term Maclaurin truncation. -/
noncomputable def Rsh0 (y : Real) : Real :=
  sinh y - y - y * y * y * ((1 / (1 + 1 + 1 + 1 + 1 + 1) : Real))
    - y * y * y * y * y * ((1 / onetwenty : Real))

theorem Rsh0_deriv : ∀ c : Real, HasDerivAt Rsh0 (Rsh1 c) c := by
  intro c
  have hy3 : HasDerivAt (fun y => y * y * y * ((1 / (1 + 1 + 1 + 1 + 1 + 1) : Real)))
      ((c * c + c * c + c * c) * (1 / (1 + 1 + 1 + 1 + 1 + 1) : Real) + (c * c * c) * 0) c :=
    HasDerivAt_mul (fun y => y * y * y) (fun _ => (1 / (1 + 1 + 1 + 1 + 1 + 1) : Real))
      (c * c + c * c + c * c) 0 c (hD_y3 c)
      (HasDerivAt_const (1 / (1 + 1 + 1 + 1 + 1 + 1) : Real) c)
  have hy5 : HasDerivAt (fun y => y * y * y * y * y * ((1 / onetwenty : Real)))
      (((c + c) * (c * c * c) + (c * c) * (c * c + c * c + c * c)) * (1 / onetwenty : Real)
        + (c * c * c * c * c) * 0) c :=
    HasDerivAt_mul (fun y => y * y * y * y * y) (fun _ => (1 / onetwenty : Real))
      ((c + c) * (c * c * c) + (c * c) * (c * c + c * c + c * c)) 0 c (hD_y5 c)
      (HasDerivAt_const (1 / onetwenty : Real) c)
  have h1 : HasDerivAt (fun y => sinh y - y) (cosh c - 1) c :=
    HasDerivAt_sub sinh (fun y => y) (cosh c) 1 c (HasDerivAt_sinh c) (HasDerivAt_id c)
  have hsuby3 := HasDerivAt_sub (fun y => sinh y - y)
    (fun y => y * y * y * (1 / (1 + 1 + 1 + 1 + 1 + 1) : Real)) (cosh c - 1) _ c h1 hy3
  have hfull := HasDerivAt_sub
    (fun y => sinh y - y - y * y * y * (1 / (1 + 1 + 1 + 1 + 1 + 1) : Real))
    (fun y => y * y * y * y * y * ((1 / onetwenty : Real))) _ _ c hsuby3 hy5
  have hclean : ((cosh c - 1) - ((c * c + c * c + c * c) * (1 / (1 + 1 + 1 + 1 + 1 + 1) : Real) + (c * c * c) * 0))
      - (((c + c) * (c * c * c) + (c * c) * (c * c + c * c + c * c)) * (1 / onetwenty : Real)
        + (c * c * c * c * c) * 0)
      = Rsh1 c := by
    unfold Rsh1
    have hy3simp : (c * c + c * c + c * c) * (1 / (1 + 1 + 1 + 1 + 1 + 1) : Real) + (c * c * c) * 0
        = (c * c) * (1 / (1 + 1)) := by
      rw [show (c * c + c * c + c * c) * (1 / (1 + 1 + 1 + 1 + 1 + 1) : Real) + (c * c * c) * 0
          = (c * c + c * c + c * c) * (1 / (1 + 1 + 1 + 1 + 1 + 1) : Real) from by mach_ring]
      exact sixth_thrice (c * c)
    have hy5simp : ((c + c) * (c * c * c) + (c * c) * (c * c + c * c + c * c)) * (1 / onetwenty : Real)
        + (c * c * c * c * c) * 0 = (c * c * c * c) * (1 / twentyfour) := by
      rw [show ((c + c) * (c * c * c) + (c * c) * (c * c + c * c + c * c)) * (1 / onetwenty : Real)
          + (c * c * c * c * c) * 0
          = (c * c * c * c + c * c * c * c + c * c * c * c + c * c * c * c + c * c * c * c) * (1 / onetwenty)
          from by mach_ring]
      exact fifth_of_120 (c * c * c * c)
    rw [hy3simp, hy5simp]
  exact hasDerivAt_congr_val hfull hclean

theorem Rsh0_zero : Rsh0 0 = 0 := by unfold Rsh0; rw [sinh_zero]; mach_ring

/-- **The main result.** `|sinh(x) − (x + x³/6 + x⁵/120)| ≤ sinh(x)·x⁶` for `x ≥ 0` — the
real-valued forward-error bound for `eml_sinh.v`'s exact 3-term Maclaurin truncation.
`sorryAx`-free. -/
theorem Rsh0_bound (x : Real) (hx0 : 0 ≤ x) :
    abs (Rsh0 x) ≤ (((((sinh x * x) * x) * x) * x) * x) * x := by
  apply abs_mvt_step Rsh0 Rsh1 x (((((sinh x * x) * x) * x) * x) * x) hx0
    (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (sinh_nonneg hx0) hx0) hx0) hx0) hx0) hx0)
    Rsh0_deriv Rsh0_zero
  intro t ht0 htx
  have h1 : abs (Rsh1 t) ≤ ((((sinh t * t) * t) * t) * t) * t := Rsh1_bound t ht0
  have h2 : ((((sinh t * t) * t) * t) * t) * t ≤ ((((sinh x * x) * x) * x) * x) * x := by
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
    exact le_trans (mul_le_mul_of_nonneg_right hd ht0)
      (mul_le_mul_of_nonneg_left htx
        (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (sinh_nonneg hx0) hx0) hx0) hx0) hx0))
  exact le_trans h1 h2

end MachLib.Real
