import MachLib.GaussianImproperIntegral

/-!
# Stage 3 of the `√π` project: `∫₀^∞ r·exp(-r²) dr = ½`

Unlike `exp(-t²)` itself, `r·exp(-r²)` HAS an elementary antiderivative — `-½exp(-r²)` — so this
stage is a direct FTC application (no comparison-function detour like stage 2 needed), reusing
`GaussianIntegral.lean`'s `hasDerivAt_gaussian` for the inner chain-rule piece and
`GaussianImproperIntegral.lean`'s improper-integral `sup_exists` pattern for the `r → ∞` limit.
This is the radial factor Stage 6 (polar substitution) will need: `I² = ∫₀^{π/2}∫₀^∞ r·exp(-r²)
dr dθ`, and this file supplies the exact value of the inner integral.

`sorryAx`-free, no new axioms.
-/

namespace MachLib
namespace Real

/-! ## §1 — The antiderivative `-½exp(-r²)` of `r·exp(-r²)` -/

private theorem half_double (x : Real) : (1 / (1 + 1)) * (x + x) = x := by
  rw [show x + x = (1 + 1) * x from by mach_mpoly [x]]
  rw [show (1 / (1 + 1) : Real) * ((1 + 1) * x) = ((1 / (1 + 1)) * (1 + 1)) * x from by
    mach_mpoly [x, (1 / (1 + 1) : Real)]]
  rw [mul_comm (1 / (1 + 1) : Real) (1 + 1), mul_inv (1 + 1) two_ne_zero, one_mul_thm]

theorem hasDerivAt_half_exp_neg_r_sq (x : Real) :
    HasDerivAt (fun r => -(1 / (1 + 1)) * Real.exp (-(r * r))) (x * Real.exp (-(x * x))) x := by
  have h := HasDerivAt_mul (fun _ : Real => -(1 / (1 + 1))) (fun r => Real.exp (-(r * r))) 0
    (Real.exp (-(x * x)) * (-(x + x))) x (HasDerivAt_const (-(1 / (1 + 1))) x) (hasDerivAt_gaussian x)
  rwa [show (0 : Real) * Real.exp (-(x * x))
        + (-(1 / (1 + 1))) * (Real.exp (-(x * x)) * (-(x + x)))
      = (1 / (1 + 1)) * (x + x) * Real.exp (-(x * x)) from by
        mach_mpoly [x, Real.exp (-(x * x)), (1 / (1 + 1) : Real)],
    half_double] at h

theorem radial_continuous (x : Real) : ContinuousAt (fun r => r * Real.exp (-(r * r))) x := by
  have h := HasDerivAt_mul (fun r => r) (fun r => Real.exp (-(r * r))) 1
    (Real.exp (-(x * x)) * (-(x + x))) x (HasDerivAt_id x) (hasDerivAt_gaussian x)
  exact hasDerivAt_continuousAt h

/-! ## §2 — `∫₀ˣ r·exp(-r²) dr = ½(1 - exp(-x²))`, via FTC -/

theorem radial_integral_exists (x : Real) (hx : 0 ≤ x) :
    ∃ I : Real,
      (∀ k, lowerSumCont (fun r => r * Real.exp (-(r * r))) 0 x hx
          (fun z _ _ => radial_continuous z) (2 ^ k) (two_pow_pos k) ≤ I ∧
        I ≤ upperSumCont (fun r => r * Real.exp (-(r * r))) 0 x hx
          (fun z _ _ => radial_continuous z) (2 ^ k) (two_pow_pos k)) ∧
      (∀ ε : Real, 0 < ε → ∃ k,
        upperSumCont (fun r => r * Real.exp (-(r * r))) 0 x hx (fun z _ _ => radial_continuous z)
            (2 ^ k) (two_pow_pos k)
          - lowerSumCont (fun r => r * Real.exp (-(r * r))) 0 x hx
              (fun z _ _ => radial_continuous z) (2 ^ k) (two_pow_pos k) < ε) :=
  continuous_riemann_integrable (fun r => r * Real.exp (-(r * r))) 0 x hx
    (fun z _ _ => radial_continuous z)

noncomputable def radialIntegral (x : Real) (hx : 0 ≤ x) : Real :=
  Classical.choose (radial_integral_exists x hx)

theorem radialIntegral_eq (x : Real) (hx : 0 < x) :
    radialIntegral x (le_of_lt hx) = (1 / (1 + 1)) * (1 - Real.exp (-(x * x))) := by
  have hspec := Classical.choose_spec (radial_integral_exists x (le_of_lt hx))
  have heq := ftc_riemann (fun r => r * Real.exp (-(r * r)))
    (fun r => -(1 / (1 + 1)) * Real.exp (-(r * r))) 0 x hx (fun z _ _ => radial_continuous z)
    (fun z _ _ => hasDerivAt_half_exp_neg_r_sq z) (radialIntegral x (le_of_lt hx))
    (fun k => (hspec.1 k).1) (fun k => (hspec.1 k).2) hspec.2
  rw [heq]
  show -(1 / (1 + 1)) * Real.exp (-(x * x)) - -(1 / (1 + 1)) * Real.exp (-(0 * 0))
    = (1 / (1 + 1)) * (1 - Real.exp (-(x * x)))
  rw [show (0 : Real) * 0 = 0 from by mach_mpoly []]
  have hexp0 : Real.exp (-(0 : Real)) = 1 := by
    rw [show -(0 : Real) = 0 from by mach_mpoly [], Real.exp_zero]
  rw [hexp0]
  mach_mpoly [Real.exp (-(x * x)), (1 / (1 + 1) : Real)]

theorem radialIntegral_zero : radialIntegral 0 (le_refl 0) = 0 := by
  have hgspec := Classical.choose_spec (radial_integral_exists 0 (le_refl 0))
  have hupz : upperSumCont (fun r => r * Real.exp (-(r * r))) 0 0 (le_refl 0)
      (fun z _ _ => radial_continuous z) (2 ^ 0) (two_pow_pos 0) = 0 := by
    show partialSum (maxSub (fun r => r * Real.exp (-(r * r))) 0 0 (le_refl 0)
        (fun z _ _ => radial_continuous z) (2 ^ 0) (two_pow_pos 0)) (2 ^ 0)
        * meshWidth 0 0 (2 ^ 0) = 0
    have hw0 : meshWidth 0 0 (2 ^ 0) = 0 := by
      show ((0 : Real) - 0) / natCast (2 ^ 0) = 0
      rw [sub_self, zero_div]
    rw [hw0, mul_zero]
  have hlowz : lowerSumCont (fun r => r * Real.exp (-(r * r))) 0 0 (le_refl 0)
      (fun z _ _ => radial_continuous z) (2 ^ 0) (two_pow_pos 0) = 0 := by
    show partialSum (minSub (fun r => r * Real.exp (-(r * r))) 0 0 (le_refl 0)
        (fun z _ _ => radial_continuous z) (2 ^ 0) (two_pow_pos 0)) (2 ^ 0)
        * meshWidth 0 0 (2 ^ 0) = 0
    have hw0 : meshWidth 0 0 (2 ^ 0) = 0 := by
      show ((0 : Real) - 0) / natCast (2 ^ 0) = 0
      rw [sub_self, zero_div]
    rw [hw0, mul_zero]
  have h1 : lowerSumCont (fun r => r * Real.exp (-(r * r))) 0 0 (le_refl 0)
      (fun z _ _ => radial_continuous z) (2 ^ 0) (two_pow_pos 0)
      ≤ radialIntegral 0 (le_refl 0) := (hgspec.1 0).1
  have h2 : radialIntegral 0 (le_refl 0)
      ≤ upperSumCont (fun r => r * Real.exp (-(r * r))) 0 0 (le_refl 0)
        (fun z _ _ => radial_continuous z) (2 ^ 0) (two_pow_pos 0) := (hgspec.1 0).2
  rw [hupz] at h2
  rw [hlowz] at h1
  exact le_antisymm h2 h1

/-! ## §3 — `exp(-x²) → 0`, hence the improper radial integral equals exactly `½` -/

private theorem natCast_one_local : natCast 1 = 1 := by
  rw [natCast_succ, natCast_zero]; exact zero_add 1

theorem exp_neg_sq_small (ε : Real) (hε : 0 < ε) : ∃ x : Real, 0 < x ∧ Real.exp (-(x * x)) < ε := by
  have hεinv : 0 < 1 / ε := one_div_pos_of_pos hε
  obtain ⟨n, hn⟩ := archimedean (1 / ε)
  have hnpos : 0 < n := by
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · exfalso; rw [h0, natCast_zero] at hn; exact lt_irrefl_ax 0 (lt_trans_ax hεinv hn)
    · exact hpos
  have hx1 : (1 : Real) ≤ natCast n := by
    rw [← natCast_one_local]; exact natCast_le_of_nat_le hnpos
  have hxx : natCast n ≤ natCast n * natCast n := by
    have := mul_le_mul_of_nonneg_left hx1 (natCast_nonneg n)
    rwa [mul_one_ax] at this
  have hexpx : natCast n < Real.exp (natCast n) := exp_grows_strictly (natCast n)
  have hexpxx : Real.exp (natCast n) ≤ Real.exp (natCast n * natCast n) := exp_monotone hxx
  have hchain1 : natCast n < Real.exp (natCast n * natCast n) := lt_of_lt_of_le hexpx hexpxx
  have hcross : (1 : Real) < natCast n * ε := by
    have hmul := mul_lt_mul_of_pos_right hn hε
    rwa [div_mul_cancel (ne_of_gt hε)] at hmul
  have hcross' : (1 : Real) < ε * natCast n := by rwa [mul_comm] at hcross
  have hscale : ε * natCast n ≤ ε * Real.exp (natCast n * natCast n) :=
    mul_le_mul_of_nonneg_left (le_of_lt hchain1) (le_of_lt hε)
  have hfinal : (1 : Real) < ε * Real.exp (natCast n * natCast n) :=
    lt_of_lt_of_le hcross' hscale
  refine ⟨natCast n, lt_of_lt_of_le one_pos hx1, ?_⟩
  rw [exp_neg_inv]
  exact div_lt_of_lt_mul hfinal (exp_pos (natCast n * natCast n))

theorem radialIntegral_le_half (x : Real) (hx : 0 ≤ x) : radialIntegral x hx ≤ 1 / (1 + 1) := by
  rcases (le_iff_lt_or_eq 0 x).mp hx with hxpos | hxeq
  · have heq : radialIntegral x hx = (1 / (1 + 1)) * (1 - Real.exp (-(x * x))) :=
      radialIntegral_eq x hxpos
    rw [heq]
    have hep := exp_pos (-(x * x))
    have h1 : (1 / (1 + 1) : Real) * (1 - Real.exp (-(x * x))) ≤ (1 / (1 + 1)) * 1 := by
      apply mul_le_mul_of_nonneg_left _ (le_of_lt (one_div_pos_of_pos two_pos))
      have h2 := add_le_add_both (le_refl (1 : Real)) (neg_nonpos_of_nonneg (le_of_lt hep))
      rwa [show (1 : Real) + -Real.exp (-(x * x)) = 1 - Real.exp (-(x * x)) from by
        mach_mpoly [Real.exp (-(x * x))], add_zero] at h2
    rwa [mul_one_ax] at h1
  · subst hxeq
    rw [radialIntegral_zero]
    exact le_of_lt (one_div_pos_of_pos two_pos)

theorem radialImproperIntegral_exists :
    ∃ G : Real, (∀ x (hx : 0 ≤ x), radialIntegral x hx ≤ G) ∧
      (∀ ε : Real, 0 < ε → ∃ x, ∃ hx : 0 ≤ x, G - ε < radialIntegral x hx) := by
  have hne : ∃ y, ∃ x, ∃ hx : 0 ≤ x, y = radialIntegral x hx :=
    ⟨radialIntegral 0 (le_refl 0), 0, le_refl 0, rfl⟩
  have hbd : BoundedAbove (fun y => ∃ x, ∃ hx : 0 ≤ x, y = radialIntegral x hx) :=
    ⟨1 / (1 + 1), fun y hy => by
      obtain ⟨t, ht, heq⟩ := hy
      rw [heq]
      exact radialIntegral_le_half t ht⟩
  obtain ⟨G, hub, hlub⟩ :=
    sup_exists (fun y => ∃ x, ∃ hx : 0 ≤ x, y = radialIntegral x hx) hne hbd
  refine ⟨G, fun x hx => hub (radialIntegral x hx) ⟨x, hx, rfl⟩, ?_⟩
  intro ε hε
  apply Classical.byContradiction
  intro hcon
  have hbd' : ∀ y, (∃ x, ∃ hx : 0 ≤ x, y = radialIntegral x hx) → y ≤ G - ε := by
    intro y hy
    apply Classical.byContradiction
    intro hycon
    apply hcon
    obtain ⟨x, hx, heq⟩ := hy
    exact ⟨x, hx, heq ▸ lt_of_not_le hycon⟩
  have hle := hlub (G - ε) hbd'
  have hlt : G - ε < G := by
    have h2 := add_lt_add_left hε (G - ε)
    rwa [add_zero, show G - ε + ε = G from by mach_mpoly [G, ε]] at h2
  exact lt_irrefl_ax G (lt_of_le_of_lt hle hlt)

/-- **`∫₀^∞ r·exp(-r²) dr = ½` exactly.** The upper bound `≤ ½` (`radialIntegral_le_half`)
combined with getting arbitrarily close to `½` (via `exp_neg_sq_small`) pins the improper integral
to exactly `½` — this is the radial factor `√π`'s derivation needs at stage 6/7. -/
private theorem one_div_two_le_one : (1 / (1 + 1) : Real) ≤ 1 :=
  div_le_one_of_le_of_pos two_pos (le_add_of_nonneg_right (le_of_lt one_pos))

private theorem neg_lt_neg_radial {a b : Real} (h : a < b) : -b < -a := by
  have h2 := add_lt_add_left h (-a - b)
  rwa [show (-a - b) + a = -b from by mach_mpoly [a, b],
    show (-a - b) + b = -a from by mach_mpoly [a, b]] at h2

private theorem half_expand (y : Real) :
    (1 / (1 + 1) : Real) * (1 - y) = 1 / (1 + 1) - (1 / (1 + 1)) * y := by
  mach_mpoly [y, (1 / (1 + 1) : Real)]

private theorem half_recombine (y : Real) :
    (1 / (1 + 1) : Real) * y + (1 / (1 + 1) - (1 / (1 + 1)) * y) = 1 / (1 + 1) := by
  mach_mpoly [y, (1 / (1 + 1) : Real)]

theorem radialImproperIntegral_eq_half :
    ∃ G : Real, G = 1 / (1 + 1) ∧ (∀ x (hx : 0 ≤ x), radialIntegral x hx ≤ G) ∧
      (∀ ε : Real, 0 < ε → ∃ x, ∃ hx : 0 ≤ x, G - ε < radialIntegral x hx) := by
  obtain ⟨G, hub, hlub⟩ := radialImproperIntegral_exists
  refine ⟨G, ?_, hub, hlub⟩
  apply le_antisymm
  · -- G ≤ 1/(1+1): every value G-approximates is itself ≤ 1/(1+1)
    apply le_of_forall_pos_lt_add
    intro η hη
    obtain ⟨x, hx, hgt⟩ := hlub η hη
    have hgt2 : G < radialIntegral x hx + η := by
      have h := add_lt_add_left hgt η
      rwa [show η + (G - η) = G from by mach_mpoly [η, G],
        add_comm η (radialIntegral x hx)] at h
    exact lt_of_lt_of_le hgt2 (add_le_add_both (radialIntegral_le_half x hx) (le_refl η))
  · -- 1/(1+1) ≤ G: radialIntegral gets arbitrarily close to 1/(1+1), and is always ≤ G
    apply le_of_forall_pos_lt_add
    intro η hη
    obtain ⟨x, hxpos, hexp_small⟩ := exp_neg_sq_small η hη
    have heq : radialIntegral x (le_of_lt hxpos) = (1 / (1 + 1)) * (1 - Real.exp (-(x * x))) :=
      radialIntegral_eq x hxpos
    have hGge : radialIntegral x (le_of_lt hxpos) ≤ G := hub x (le_of_lt hxpos)
    rw [heq] at hGge
    have hstep1 : 1 - η < 1 - Real.exp (-(x * x)) := by
      have hneg := neg_lt_neg_radial hexp_small
      have hadd := add_lt_add_left hneg 1
      rwa [show (1 : Real) + -η = 1 - η from by mach_mpoly [η],
        show (1 : Real) + -Real.exp (-(x * x)) = 1 - Real.exp (-(x * x)) from by
          mach_mpoly [Real.exp (-(x * x))]] at hadd
    have hstep2 : (1 / (1 + 1) : Real) * (1 - η) < (1 / (1 + 1)) * (1 - Real.exp (-(x * x))) := by
      have h := mul_lt_mul_of_pos_right hstep1 (one_div_pos_of_pos two_pos)
      rwa [mul_comm (1 - η) (1 / (1 + 1) : Real),
        mul_comm (1 - Real.exp (-(x * x))) (1 / (1 + 1) : Real)] at h
    have hkey : (1 / (1 + 1) : Real) - (1 / (1 + 1)) * η < G := by
      rw [half_expand η] at hstep2
      exact lt_of_lt_of_le hstep2 hGge
    have hetashrink : (1 / (1 + 1) : Real) * η ≤ η := by
      have h := mul_le_mul_of_nonneg_right one_div_two_le_one (le_of_lt hη)
      rwa [one_mul_thm] at h
    have hkey2 : (1 / (1 + 1) : Real) < G + (1 / (1 + 1)) * η := by
      have h := add_lt_add_left hkey ((1 / (1 + 1) : Real) * η)
      rwa [half_recombine η, add_comm ((1 / (1 + 1) : Real) * η) G] at h
    exact lt_of_lt_of_le hkey2 (add_le_add_both (le_refl G) hetashrink)

end Real
end MachLib
