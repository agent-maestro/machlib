import MachLib.TransNodes
import MachLib.TrigLipschitz

/-!
# `tan` is locally Lipschitz on `[-R,R]`, `R < π/2` — the one new axiom in this arc

Every other `Trans1` primitive (`exp,ln,sin,cos,sqrt,abs,asin,acos,atan,sinh,cosh,tanh,log10`) grounds
off Lipschitz math that either was globally true or was already derivable from the handful of
`sin`/`cos` facts `Trig.lean` axiomatizes (`cos_zero`, `cos_pi`, `pythagorean`, addition formulas,
`HasDerivAt_sin`/`HasDerivAt_cos`). `tan` is different: its derivative `1/cos²` blows up as `x → ±π/2`
(the same *shape* of problem as `arcsin`/`arccos` near `±1`), but unlike those, closing the domain
bound here needs a SIGN fact about `sin`/`cos` that nothing in the tree establishes — `MachLib.Real`
only axiomatizes `sin`/`cos` at isolated points (`cos_zero`, `cos_pi`, `cos_pi_div_two`, `sin_one_pos`),
never their sign over an interval. Confirmed with the user (AskUserQuestion, 2026-07-17) before adding:

**The one new axiom**: `sin_pos_of_pos_lt_pi_div_two` — `sin` is positive on the open interval
`(0, π/2)`. Universally accepted, elementary (every model of trigonometry satisfies it); the
trigonometric analogue of `cosh_pos`'s role on the hyperbolic side, and a direct generalisation of the
already-disclosed single-point `sin_one_pos`. Everything else in this file — `cos` positivity on
`[0,π/2)` and on `(-π/2,π/2)`, `cos`'s radial-antitone bound, `HasDerivAt_tan`, the Lipschitz bound,
the forward-error node — is DERIVED from it (plus the pre-existing `HasDerivAt_sin`/`HasDerivAt_cos`/
`HasDerivAt_congr`/`cos_pi_div_two`/`pythagorean`), 0 further axioms. `sorryAx`-free.
-/

namespace MachLib.Real

private theorem eq_div_of_mul_eq_tan {x z k : Real} (hk : k ≠ 0) (h : x * k = z) : x = z / k := by
  rw [← h, mul_comm x k, mul_div_cancel_left' hk]

private theorem le_total_tan (a b : Real) : a ≤ b ∨ b ≤ a := by
  rcases lt_total a b with h | h | h
  · exact Or.inl (le_of_lt h)
  · exact Or.inl (le_of_eq h)
  · exact Or.inr (le_of_lt h)

private theorem abs_sub_comm_tan (x y : Real) : abs (x - y) = abs (y - x) := by
  have h : y - x = -(x - y) := by mach_ring
  rw [h, abs_neg]

/-! ## The one new axiom -/

/-- **NEW AXIOM (2026-07-17, user-approved via AskUserQuestion).** `sin` is positive on the open
interval `(0, π/2)`. The single fact needed to unblock `tan`'s domain-bounded Lipschitz argument;
everything else below is derived from it. -/
axiom sin_pos_of_pos_lt_pi_div_two (x : Real) (hx0 : 0 < x) (hxp : x < pi / (1 + 1)) :
    0 < sin x

/-! ## `cos` positivity, derived -/

/-- **`cos` is positive on `[0, π/2)`.** MVT between `x` and `π/2` (using `cos_pi_div_two = 0` as the
right endpoint) + `sin_pos_of_pos_lt_pi_div_two`. -/
theorem cos_pos_of_lt_pi_div_two {x : Real} (hx0 : 0 ≤ x) (hxp : x < pi / (1 + 1)) :
    0 < cos x := by
  obtain ⟨c, f', hxc, hcp, hd, hval⟩ :=
    mean_value_theorem_ct cos x (pi / (1 + 1)) hxp (fun c _ _ => ⟨-sin c, HasDerivAt_cos c⟩)
  rw [HasDerivAt_unique cos f' (-sin c) c hd (HasDerivAt_cos c), cos_pi_div_two] at hval
  have hc0 : 0 < c := lt_of_le_of_lt hx0 hxc
  have hsinpos : 0 < sin c := sin_pos_of_pos_lt_pi_div_two c hc0 hcp
  have hgap : 0 < pi / (1 + 1) - x := sub_pos_of_lt hxp
  have hcosx : cos x = sin c * (pi / (1 + 1) - x) := by
    have h0 : cos x = -(0 - cos x) := by mach_ring
    rw [h0, hval]; mach_ring
  exact hcosx ▸ mul_pos hsinpos hgap

/-- **`cos` is positive on `(-π/2, π/2)`.** Extends `cos_pos_of_lt_pi_div_two` via `cos_neg`
(evenness). -/
theorem cos_pos_of_abs_lt_pi_div_two {x : Real} (hx : abs x < pi / (1 + 1)) : 0 < cos x := by
  rcases le_total_tan 0 x with h | h
  · exact cos_pos_of_lt_pi_div_two h (by rw [abs_of_nonneg h] at hx; exact hx)
  · have hax : abs x = -x := abs_of_nonpos h
    have hnx0 : 0 ≤ -x := by rw [← hax]; exact abs_nonneg x
    have hnxp : -x < pi / (1 + 1) := by rw [← hax]; exact hx
    have hcx := cos_pos_of_lt_pi_div_two hnx0 hnxp
    rwa [cos_neg] at hcx

/-- **`cos` is (weakly) antitone on `[0, π/2)`.** MVT + `sin_pos_of_pos_lt_pi_div_two` on the sign of
the derivative `-sin`, the trigonometric analogue of `cosh_mono`. -/
theorem cos_antitone {a b : Real} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b < pi / (1 + 1)) :
    cos b ≤ cos a := by
  rcases lt_total a b with h | h | h
  · obtain ⟨c, f', hac, hcb, hd, hval⟩ :=
      mean_value_theorem_ct cos a b h (fun c _ _ => ⟨-sin c, HasDerivAt_cos c⟩)
    rw [HasDerivAt_unique cos f' (-sin c) c hd (HasDerivAt_cos c)] at hval
    have hc0 : 0 < c := lt_of_le_of_lt ha hac
    have hcp2 : c < pi / (1 + 1) := lt_trans_ax hcb hb
    have hsinpos : 0 < sin c := sin_pos_of_pos_lt_pi_div_two c hc0 hcp2
    have hba : 0 < b - a := sub_pos_of_lt h
    have hval2 : cos a - cos b = sin c * (b - a) := by
      have hneg : cos a - cos b = -(cos b - cos a) := by mach_ring
      rw [hneg, hval]; mach_ring
    exact le_of_sub_nonneg (hval2 ▸ mul_nonneg (le_of_lt hsinpos) (le_of_lt hba))
  · exact le_of_eq (congrArg cos h.symm)
  · exact absurd (lt_of_lt_of_le h hab) (lt_irrefl_ax b)

/-- **Radial form of `cos_antitone`**: `abs c ≤ R < π/2 → cos R ≤ cos c` — the MVT-slope-domination
fact the Lipschitz bound below needs, matching `sqrt_mono`'s role in `arcsin_lip_lt`. -/
theorem cos_ge_of_abs_le {c R : Real} (hR : R < pi / (1 + 1)) (hcR : abs c ≤ R) :
    cos R ≤ cos c := by
  have h1 : cos R ≤ cos (abs c) := cos_antitone (abs_nonneg c) hcR hR
  rcases le_total_tan 0 c with h | h
  · rwa [abs_of_nonneg h] at h1
  · rwa [abs_of_nonpos h, cos_neg] at h1

/-! ## `tan`'s derivative, derived -/

/-- **`tan' = 1/cos²`, valid wherever `abs x < π/2`.** Derived (not axiomatized) as `(sin·cos⁻¹)'`,
simplified by `sin²+cos²=1` (`pythagorean`) exactly like `HasDerivAt_tanh`'s `(sinh·cosh⁻¹)'`
derivation — then transferred from the raw `sin·(1/cos)` lambda to `tan` itself via `HasDerivAt_congr`
(a LOCAL/δ-ball argument, not `HasDerivAt_of_eq`'s global one): `tan_def`'s identity only holds where
`cos ≠ 0`, so the two functions agree in a neighbourhood of `x`, not everywhere — unlike `tanh`, whose
`tanh_eq_sinh_div_cosh` is unconditional since `cosh` is never zero. -/
theorem HasDerivAt_tan {x : Real} (hx : abs x < pi / (1 + 1)) :
    HasDerivAt tan (1 / (cos x * cos x)) x := by
  have hcpos : 0 < cos x := cos_pos_of_abs_lt_pi_div_two hx
  have hcne : cos x ≠ 0 := ne_of_gt hcpos
  have hccne : cos x * cos x ≠ 0 := mul_ne_zero hcne hcne
  have hmul : HasDerivAt (fun y => sin y * (1 / cos y))
      (cos x * (1 / cos x) + sin x * (-(-sin x) / (cos x * cos x))) x :=
    HasDerivAt_mul sin (fun y => 1 / cos y) (cos x) (-(-sin x) / (cos x * cos x)) x
      (HasDerivAt_sin x) (HasDerivAt_inv cos (-sin x) x hcne (HasDerivAt_cos x))
  have key : (cos x * (1 / cos x) + sin x * (-(-sin x) / (cos x * cos x))) * (cos x * cos x)
      = 1 := by
    have e2 : (1 / (cos x * cos x)) * (cos x * cos x) = 1 := by
      rw [mul_comm]; exact mul_inv (cos x * cos x) hccne
    rw [show -(-sin x) = sin x from by mach_ring,
        div_def (sin x) (cos x * cos x) hccne,
        show (cos x * (1 / cos x) + sin x * (sin x * (1 / (cos x * cos x)))) * (cos x * cos x)
          = cos x * (1 / cos x) * (cos x * cos x)
            + sin x * sin x * ((1 / (cos x * cos x)) * (cos x * cos x)) from by
          mach_mpoly [cos x, sin x, 1 / cos x, (1 / (cos x * cos x) : Real)],
        mul_inv (cos x) hcne, e2,
        show (1 : Real) * (cos x * cos x) + sin x * sin x * 1
          = sin x * sin x + cos x * cos x from by mach_ring, pythagorean x]
  rw [eq_div_of_mul_eq_tan hccne key] at hmul
  have hδ : (0 : Real) < pi / (1 + 1) - abs x := sub_pos_of_lt hx
  refine HasDerivAt_congr (fun y => sin y * (1 / cos y)) tan (1 / (cos x * cos x)) x
    ⟨pi / (1 + 1) - abs x, hδ, fun y hy => ?_⟩ hmul
  have hyabs : abs y < pi / (1 + 1) := by
    have htri : abs y ≤ abs x + abs (y - x) := by
      have h := abs_add x (y - x)
      rwa [show x + (y - x) = y from by mach_mpoly [x, y]] at h
    have h2 := add_lt_add_left hy (abs x)
    rw [show abs x + (pi / (1 + 1) - abs x) = pi / (1 + 1) from by mach_ring] at h2
    exact lt_of_le_of_lt htri h2
  have hcyne : cos y ≠ 0 := ne_of_gt (cos_pos_of_abs_lt_pi_div_two hyabs)
  rw [tan_def y hcyne, div_def (sin y) (cos y) hcyne]

/-! ## Lipschitz bound and forward-error node -/

/-- One-sided MVT bound: for `-R ≤ a < b ≤ R` (`R < π/2`, `R ≥ 0`), `|tan b − tan a| ≤
(1/cos²R)·(b−a)`. Same shape as `arcsin_lip_lt`, with `cos_ge_of_abs_le` in place of `sqrt_mono`. -/
theorem tan_lip_lt {a b R : Real} (hR0 : 0 ≤ R) (hR : R < pi / (1 + 1))
    (haR : -R ≤ a) (hbR : b ≤ R) (hab : a < b) :
    abs (tan b - tan a) ≤ (1 / (cos R * cos R)) * (b - a) := by
  obtain ⟨c, f', hac, hcb, hd, heq⟩ :=
    mean_value_theorem_ct tan a b hab (fun c hca hcb =>
      ⟨1 / (cos c * cos c), HasDerivAt_tan
        (lt_of_le_of_lt (abs_le_iff.mpr ⟨le_trans haR hca, le_trans hcb hbR⟩) hR)⟩)
  have hcR : abs c ≤ R := abs_le_iff.mpr ⟨le_trans haR (le_of_lt hac), le_trans (le_of_lt hcb) hbR⟩
  have hf' : f' = 1 / (cos c * cos c) :=
    HasDerivAt_unique tan f' (1 / (cos c * cos c)) c hd
      (HasDerivAt_tan (lt_of_le_of_lt hcR hR))
  have hRpos : 0 < cos R := cos_pos_of_abs_lt_pi_div_two (by rw [abs_of_nonneg hR0]; exact hR)
  have hcpos : 0 < cos c := cos_pos_of_abs_lt_pi_div_two (lt_of_le_of_lt hcR hR)
  have hccge : cos R ≤ cos c := cos_ge_of_abs_le hR hcR
  have hsq : cos R * cos R ≤ cos c * cos c :=
    le_trans (mul_le_mul_of_nonneg_right hccge (le_of_lt hRpos))
             (mul_le_mul_of_nonneg_left hccge (le_of_lt hcpos))
  have hdiv : 1 / (cos c * cos c) ≤ 1 / (cos R * cos R) :=
    div_le_div_pos (le_of_lt zero_lt_one_ax) (le_refl 1) (mul_pos hRpos hRpos) hsq
  rw [heq, hf', abs_mul, abs_of_nonneg (sub_nonneg_of_le (le_of_lt hab)),
      abs_of_nonneg (le_of_lt (one_div_pos_of_pos (mul_pos hcpos hcpos)))]
  exact mul_le_mul_of_nonneg_right hdiv (le_of_lt (sub_pos_of_lt hab))

/-- **`tan` is `1/cos²R`-Lipschitz on `[-R,R]`** (`R < π/2`, `R ≥ 0`) — the `absenc_lip_local`
hypothesis for `tan`. -/
theorem tan_lip_local (R : Real) (hR0 : 0 ≤ R) (hR : R < pi / (1 + 1)) :
    ∀ p q : Real, -R ≤ p → p ≤ R → -R ≤ q → q ≤ R →
      abs (tan p - tan q) ≤ (1 / (cos R * cos R)) * abs (p - q) := by
  intro p q hRp hpR hRq hqR
  have hRpos : 0 < cos R := cos_pos_of_abs_lt_pi_div_two (by rw [abs_of_nonneg hR0]; exact hR)
  rcases lt_total p q with h | h | h
  · have hpq : abs (p - q) = q - p := by
      rw [abs_sub_comm_tan p q]; exact abs_of_nonneg (sub_nonneg_of_le (le_of_lt h))
    rw [abs_sub_comm_tan (tan p) (tan q), hpq]
    exact tan_lip_lt hR0 hR hRp hqR h
  · subst h
    rw [show tan p - tan p = (0 : Real) from by mach_ring, abs_zero]
    exact mul_nonneg (le_of_lt (one_div_pos_of_pos (mul_pos hRpos hRpos))) (abs_nonneg (p - p))
  · rw [show abs (p - q) = p - q from abs_of_nonneg (sub_nonneg_of_le (le_of_lt h))]
    exact tan_lip_lt hR0 hR hRq hpR h

/-- **The `tan` forward-error node.** Input within `Ex`, both in `[-R,R]` (`R < π/2`, `R ≥ 0`) ⟹
output within `Eround + (1/cos²R)·Ex`. -/
theorem absenc_tan_local {flx xe Ex flf Eround R : Real} (hR0 : 0 ≤ R) (hR : R < pi / (1 + 1))
    (hx : AbsEnc Ex flx xe) (hflx : abs flx ≤ R) (hxe : abs xe ≤ R)
    (hround : abs (flf - tan flx) ≤ Eround) :
    AbsEnc (Eround + (1 / (cos R * cos R)) * Ex) flf (tan xe) :=
  absenc_lip_local (lo := -R) (hi := R)
    (le_of_lt (one_div_pos_of_pos (mul_pos
      (cos_pos_of_abs_lt_pi_div_two (by rw [abs_of_nonneg hR0]; exact hR))
      (cos_pos_of_abs_lt_pi_div_two (by rw [abs_of_nonneg hR0]; exact hR)))))
    (tan_lip_local R hR0 hR) hx
    (abs_le_iff.mp hflx).1 (abs_le_iff.mp hflx).2 (abs_le_iff.mp hxe).1 (abs_le_iff.mp hxe).2 hround

end MachLib.Real
