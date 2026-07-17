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

private theorem le_total' (a b : Real) : a ≤ b ∨ b ≤ a := by
  rcases lt_total a b with h | h | h
  · exact Or.inl (le_of_lt h)
  · exact Or.inl (le_of_eq h)
  · exact Or.inr (le_of_lt h)

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
      mean_value_theorem_ct tanh p q hpq (fun c _ _ => ⟨1 / (cosh c * cosh c), HasDerivAt_tanh c⟩)
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

/-! ## the amplifying hyperbolics: `sinh`, `cosh` (monotonicity + range-Lipschitz via MVT) -/

/-- `sinh` is monotone (`sinh' = cosh > 0`). -/
theorem sinh_mono {a b : Real} (hab : a ≤ b) : sinh a ≤ sinh b := by
  rcases lt_total a b with h | h | h
  · obtain ⟨c, f', _, _, hdc, hval⟩ :=
      mean_value_theorem_ct sinh a b h (fun c _ _ => ⟨cosh c, HasDerivAt_sinh c⟩)
    rw [HasDerivAt_unique sinh f' (cosh c) c hdc (HasDerivAt_sinh c)] at hval
    exact le_of_sub_nonneg (hval ▸ mul_nonneg (le_of_lt (cosh_pos c)) (le_of_lt (sub_pos_of_lt h)))
  · exact le_of_eq (congrArg sinh h)
  · exact absurd (lt_of_lt_of_le h hab) (lt_irrefl_ax b)

/-- `0 ≤ x → 0 ≤ sinh x`. -/
theorem sinh_nonneg {x : Real} (hx : 0 ≤ x) : 0 ≤ sinh x := by
  have := sinh_mono hx; rwa [sinh_zero] at this

/-- `cosh` is monotone on the nonnegatives (`cosh' = sinh ≥ 0` there). -/
theorem cosh_mono {a b : Real} (ha : 0 ≤ a) (hab : a ≤ b) : cosh a ≤ cosh b := by
  rcases lt_total a b with h | h | h
  · obtain ⟨c, f', hac, _, hdc, hval⟩ :=
      mean_value_theorem_ct cosh a b h (fun c _ _ => ⟨sinh c, HasDerivAt_cosh c⟩)
    rw [HasDerivAt_unique cosh f' (sinh c) c hdc (HasDerivAt_cosh c)] at hval
    exact le_of_sub_nonneg
      (hval ▸ mul_nonneg (sinh_nonneg (le_trans ha (le_of_lt hac))) (le_of_lt (sub_pos_of_lt h)))
  · exact le_of_eq (congrArg cosh h)
  · exact absurd (lt_of_lt_of_le h hab) (lt_irrefl_ax b)

/-- `cosh c = cosh |c|` (even). -/
theorem cosh_abs (c : Real) : cosh c = cosh (abs c) := by
  rcases le_total' 0 c with hc | hc
  · rw [abs_of_nonneg hc]
  · rw [abs_of_nonpos hc, cosh_neg]

/-- `|sinh c| = sinh |c|` (odd, nonneg on nonneg). -/
theorem abs_sinh (c : Real) : abs (sinh c) = sinh (abs c) := by
  rcases le_total' 0 c with hc | hc
  · rw [abs_of_nonneg hc, abs_of_nonneg (sinh_nonneg hc)]
  · rw [abs_of_nonpos hc, abs_of_nonpos (by have := sinh_mono hc; rwa [sinh_zero] at this),
        sinh_neg]

/-- `|c| ≤ R → cosh c ≤ cosh R`. -/
theorem cosh_le_of_abs_le {c R : Real} (h : abs c ≤ R) : cosh c ≤ cosh R := by
  rw [cosh_abs]; exact cosh_mono (abs_nonneg c) h

/-- `|c| ≤ R → |sinh c| ≤ sinh R`. -/
theorem abs_sinh_le_of_abs_le {c R : Real} (h : abs c ≤ R) : abs (sinh c) ≤ sinh R := by
  rw [abs_sinh]; exact sinh_mono h

/-- **`sinh` Lipschitz on `[−R, R]`** — `|sinh a − sinh b| ≤ cosh R · |a − b|` (`sinh' =
cosh ≤ cosh R` there). The amplifying-Lipschitz bound, via MVT. -/
theorem sinh_lipschitz_bound {a b R : Real} (ha : abs a ≤ R) (hb : abs b ≤ R) :
    abs (sinh a - sinh b) ≤ cosh R * abs (a - b) := by
  have step : ∀ p q : Real, abs p ≤ R → abs q ≤ R → p < q →
      abs (sinh q - sinh p) ≤ cosh R * (q - p) := by
    intro p q hpR hqR hpq
    obtain ⟨c, f', hpc, hcq, hdc, hval⟩ :=
      mean_value_theorem_ct sinh p q hpq (fun c _ _ => ⟨cosh c, HasDerivAt_sinh c⟩)
    have hcR : abs c ≤ R := abs_le_of
      (le_trans (le_of_lt hcq) (le_trans (le_abs_self q) hqR))
      (le_trans (neg_le_neg (le_of_lt hpc)) (le_trans (neg_le_abs p) hpR))
    rw [hval, HasDerivAt_unique sinh f' (cosh c) c hdc (HasDerivAt_sinh c), abs_mul,
        abs_of_nonneg (le_of_lt (sub_pos_of_lt hpq)), abs_of_nonneg (le_of_lt (cosh_pos c))]
    exact mul_le_mul_of_nonneg_right (cosh_le_of_abs_le hcR) (le_of_lt (sub_pos_of_lt hpq))
  rcases lt_total a b with h | h | h
  · rw [show abs (sinh a - sinh b) = abs (sinh b - sinh a) from by
          rw [show sinh a - sinh b = -(sinh b - sinh a) from by mach_ring, abs_neg],
        show abs (a - b) = b - a from by
          rw [show a - b = -(b - a) from by mach_ring, abs_neg,
              abs_of_nonneg (le_of_lt (sub_pos_of_lt h))]]
    exact step a b ha hb h
  · rw [h]; exact le_of_eq (by rw [show sinh b - sinh b = (0 : Real) from by mach_ring, abs_zero,
        show b - b = (0 : Real) from by mach_ring, abs_zero, mul_zero])
  · rw [abs_of_nonneg (le_of_lt (sub_pos_of_lt h))]; exact step b a hb ha h

/-- **`cosh` Lipschitz on `[−R, R]`** — `|cosh a − cosh b| ≤ sinh R · |a − b|` (`cosh' =
sinh`, `|sinh| ≤ sinh R` there). -/
theorem cosh_lipschitz_bound {a b R : Real} (ha : abs a ≤ R) (hb : abs b ≤ R) :
    abs (cosh a - cosh b) ≤ sinh R * abs (a - b) := by
  have step : ∀ p q : Real, abs p ≤ R → abs q ≤ R → p < q →
      abs (cosh q - cosh p) ≤ sinh R * (q - p) := by
    intro p q hpR hqR hpq
    obtain ⟨c, f', hpc, hcq, hdc, hval⟩ :=
      mean_value_theorem_ct cosh p q hpq (fun c _ _ => ⟨sinh c, HasDerivAt_cosh c⟩)
    have hcR : abs c ≤ R := abs_le_of
      (le_trans (le_of_lt hcq) (le_trans (le_abs_self q) hqR))
      (le_trans (neg_le_neg (le_of_lt hpc)) (le_trans (neg_le_abs p) hpR))
    rw [hval, HasDerivAt_unique cosh f' (sinh c) c hdc (HasDerivAt_cosh c), abs_mul,
        abs_of_nonneg (le_of_lt (sub_pos_of_lt hpq))]
    exact mul_le_mul_of_nonneg_right (abs_sinh_le_of_abs_le hcR) (le_of_lt (sub_pos_of_lt hpq))
  rcases lt_total a b with h | h | h
  · rw [show abs (cosh a - cosh b) = abs (cosh b - cosh a) from by
          rw [show cosh a - cosh b = -(cosh b - cosh a) from by mach_ring, abs_neg],
        show abs (a - b) = b - a from by
          rw [show a - b = -(b - a) from by mach_ring, abs_neg,
              abs_of_nonneg (le_of_lt (sub_pos_of_lt h))]]
    exact step a b ha hb h
  · rw [h]; exact le_of_eq (by rw [show cosh b - cosh b = (0 : Real) from by mach_ring, abs_zero,
        show b - b = (0 : Real) from by mach_ring, abs_zero, mul_zero])
  · rw [abs_of_nonneg (le_of_lt (sub_pos_of_lt h))]; exact step b a hb ha h

/-! ## `[lo,hi]`-shaped restatements, for `AbsoluteFoldLocal`'s pipeline

`sinh_lipschitz_bound`/`cosh_lipschitz_bound` are stated with `abs a ≤ R`/`abs b ≤ R` hypotheses;
the fold's `pipeline_tr1_of_arith_local` wants the `-R ≤ p → p ≤ R → ...` shape (matching
`sqrt_lip_local`/`log10_lip_local`/`arcsin_lip_local`). Straight `abs_le_iff` repackaging, no new
math. -/

/-- **`sinh` is `cosh R`-Lipschitz on `[-R,R]`** — the `pipeline_tr1_of_arith_local` hypothesis shape
for `sinh`. -/
theorem sinh_lip_local (R : Real) :
    ∀ p q : Real, -R ≤ p → p ≤ R → -R ≤ q → q ≤ R →
      abs (sinh p - sinh q) ≤ cosh R * abs (p - q) := by
  intro p q hRp hpR hRq hqR
  exact sinh_lipschitz_bound (abs_le_iff.mpr ⟨hRp, hpR⟩) (abs_le_iff.mpr ⟨hRq, hqR⟩)

/-- **`cosh` is `sinh R`-Lipschitz on `[-R,R]`** — the `pipeline_tr1_of_arith_local` hypothesis shape
for `cosh`. -/
theorem cosh_lip_local (R : Real) :
    ∀ p q : Real, -R ≤ p → p ≤ R → -R ≤ q → q ≤ R →
      abs (cosh p - cosh q) ≤ sinh R * abs (p - q) := by
  intro p q hRp hpR hRq hqR
  exact cosh_lipschitz_bound (abs_le_iff.mpr ⟨hRp, hpR⟩) (abs_le_iff.mpr ⟨hRq, hqR⟩)

end MachLib.Real
