import MachLib.RiemannIntegralFTC
import MachLib.GaussianIntegral
import MachLib.Linarith

/-!
# Stage 2 of the `√π` project: the improper Gaussian integral exists

`∫₀^∞ exp(-t²) dt` — needs a uniform bound on `gaussianIntegral x` independent of `x`, then
`sup_exists`. The bound comes from `exp(-t²) ≤ exp(1-t)` for EVERY real `t` (a clean,
case-split-free algebraic fact: `(1-t) - (-t·t) = t² - t + 1 = (t - ½)² + ¾ > 0`), combined with
`RiemannIntegralFTC.lean`'s FTC to evaluate `∫₀ˣ exp(1-t) dt = exp 1 - exp(1-x) < exp 1` in closed
form (`exp(1-t)`, unlike `exp(-t²)`, has the elementary antiderivative `-exp(1-t)`) and a fresh
"the Riemann integral is monotone under pointwise ≤ of the integrand" lemma to transfer the bound.

`sorryAx`-free, no new axioms.
-/

namespace MachLib
namespace Real

/-! ## §1 — The Riemann integral is monotone under pointwise `≤` of the integrand -/

theorem minSub_mono (g h : Real → Real) (a b : Real) (hab : a ≤ b)
    (hcontg : ∀ z : Real, a ≤ z → z ≤ b → ContinuousAt g z)
    (hconth : ∀ z : Real, a ≤ z → z ≤ b → ContinuousAt h z)
    (hgh : ∀ t : Real, a ≤ t → t ≤ b → g t ≤ h t) (n : Nat) (hn : 0 < n) (i : Nat) (hi : i < n) :
    minSub g a b hab hcontg n hn i ≤ minSub h a b hab hconth n hn i := by
  have hmemH := minSub_mem h a b hab hconth n hn i hi
  have ha1 : a ≤ Classical.choose (evt_exists_min h a b hab hconth n hn i hi) :=
    le_trans (meshPoint_mem a b n i hab hn (Nat.le_of_lt hi)).1 hmemH.1
  have hb1 : Classical.choose (evt_exists_min h a b hab hconth n hn i hi) ≤ b :=
    le_trans hmemH.2 (meshPoint_mem a b n (i + 1) hab hn hi).2
  have hgc := hgh _ ha1 hb1
  have hminleq := minSub_spec g a b hab hcontg n hn i hi _ hmemH.1 hmemH.2
  rw [minSub_eq h a b hab hconth n hn i hi]
  exact le_trans hminleq hgc

theorem maxSub_mono (g h : Real → Real) (a b : Real) (hab : a ≤ b)
    (hcontg : ∀ z : Real, a ≤ z → z ≤ b → ContinuousAt g z)
    (hconth : ∀ z : Real, a ≤ z → z ≤ b → ContinuousAt h z)
    (hgh : ∀ t : Real, a ≤ t → t ≤ b → g t ≤ h t) (n : Nat) (hn : 0 < n) (i : Nat) (hi : i < n) :
    maxSub g a b hab hcontg n hn i ≤ maxSub h a b hab hconth n hn i := by
  have hmemG := maxSub_mem g a b hab hcontg n hn i hi
  have ha1 : a ≤ Classical.choose (evt_exists_max g a b hab hcontg n hn i hi) :=
    le_trans (meshPoint_mem a b n i hab hn (Nat.le_of_lt hi)).1 hmemG.1
  have hb1 : Classical.choose (evt_exists_max g a b hab hcontg n hn i hi) ≤ b :=
    le_trans hmemG.2 (meshPoint_mem a b n (i + 1) hab hn hi).2
  have hgc := hgh _ ha1 hb1
  have hmaxleq := maxSub_spec h a b hab hconth n hn i hi _ hmemG.1 hmemG.2
  rw [maxSub_eq g a b hab hcontg n hn i hi]
  exact le_trans hgc hmaxleq

theorem lowerSumCont_mono (g h : Real → Real) (a b : Real) (hab : a ≤ b)
    (hcontg : ∀ z : Real, a ≤ z → z ≤ b → ContinuousAt g z)
    (hconth : ∀ z : Real, a ≤ z → z ≤ b → ContinuousAt h z)
    (hgh : ∀ t : Real, a ≤ t → t ≤ b → g t ≤ h t) (n : Nat) (hn : 0 < n) :
    lowerSumCont g a b hab hcontg n hn ≤ lowerSumCont h a b hab hconth n hn := by
  show partialSum (minSub g a b hab hcontg n hn) n * meshWidth a b n
    ≤ partialSum (minSub h a b hab hconth n hn) n * meshWidth a b n
  apply mul_le_mul_of_nonneg_right _ (meshWidth_nonneg hab n)
  apply partialSum_le_of_termwise_le
  intro i hi
  exact minSub_mono g h a b hab hcontg hconth hgh n hn i hi

theorem upperSumCont_mono (g h : Real → Real) (a b : Real) (hab : a ≤ b)
    (hcontg : ∀ z : Real, a ≤ z → z ≤ b → ContinuousAt g z)
    (hconth : ∀ z : Real, a ≤ z → z ≤ b → ContinuousAt h z)
    (hgh : ∀ t : Real, a ≤ t → t ≤ b → g t ≤ h t) (n : Nat) (hn : 0 < n) :
    upperSumCont g a b hab hcontg n hn ≤ upperSumCont h a b hab hconth n hn := by
  show partialSum (maxSub g a b hab hcontg n hn) n * meshWidth a b n
    ≤ partialSum (maxSub h a b hab hconth n hn) n * meshWidth a b n
  apply mul_le_mul_of_nonneg_right _ (meshWidth_nonneg hab n)
  apply partialSum_le_of_termwise_le
  intro i hi
  exact maxSub_mono g h a b hab hcontg hconth hgh n hn i hi

/-- **Riemann integral value monotonicity.** If `g ≤ h` on `[a,b]`, `g`'s integral value is `≤`
`h`'s. -/
theorem riemann_integral_mono (g h : Real → Real) (a b : Real) (hab : a ≤ b)
    (hcontg : ∀ z : Real, a ≤ z → z ≤ b → ContinuousAt g z)
    (hconth : ∀ z : Real, a ≤ z → z ≤ b → ContinuousAt h z)
    (hgh : ∀ t : Real, a ≤ t → t ≤ b → g t ≤ h t) (Ig Ih : Real)
    (hIgup : ∀ k, Ig ≤ upperSumCont g a b hab hcontg (2 ^ k) (two_pow_pos k))
    (hIhlow : ∀ k, lowerSumCont h a b hab hconth (2 ^ k) (two_pow_pos k) ≤ Ih)
    (hgaph : ∀ ε : Real, 0 < ε → ∃ k, upperSumCont h a b hab hconth (2 ^ k) (two_pow_pos k)
      - lowerSumCont h a b hab hconth (2 ^ k) (two_pow_pos k) < ε) :
    Ig ≤ Ih := by
  apply le_of_forall_pos_lt_add
  intro η hη
  obtain ⟨k, hk⟩ := hgaph η hη
  have h1 : Ig ≤ upperSumCont g a b hab hcontg (2 ^ k) (two_pow_pos k) := hIgup k
  have h2 : upperSumCont g a b hab hcontg (2 ^ k) (two_pow_pos k)
      ≤ upperSumCont h a b hab hconth (2 ^ k) (two_pow_pos k) :=
    upperSumCont_mono g h a b hab hcontg hconth hgh (2 ^ k) (two_pow_pos k)
  have h3 : upperSumCont h a b hab hconth (2 ^ k) (two_pow_pos k)
      < lowerSumCont h a b hab hconth (2 ^ k) (two_pow_pos k) + η := by
    have hstep := add_lt_add_left hk (lowerSumCont h a b hab hconth (2 ^ k) (two_pow_pos k))
    rwa [show lowerSumCont h a b hab hconth (2 ^ k) (two_pow_pos k)
          + (upperSumCont h a b hab hconth (2 ^ k) (two_pow_pos k)
            - lowerSumCont h a b hab hconth (2 ^ k) (two_pow_pos k))
        = upperSumCont h a b hab hconth (2 ^ k) (two_pow_pos k) from by mach_ring] at hstep
  have h4 : lowerSumCont h a b hab hconth (2 ^ k) (two_pow_pos k) + η ≤ Ih + η :=
    add_le_add_both (hIhlow k) (le_refl η)
  exact lt_of_le_of_lt h1 (lt_of_le_of_lt h2 (lt_of_lt_of_le h3 h4))

/-! ## §2 — `exp(-t²) ≤ exp(1-t)` for every real `t` -/

/-- `1 - t + t² ≥ 0` for every real `t` — completing the square (`4(1-t+t²)=(2t-1)²+3`), no case
split needed. -/
theorem neg_sq_le_shift (t : Real) : -(t * t) ≤ 1 - t := by
  have hsq : 0 ≤ (t + t - 1) * (t + t - 1) := mul_self_nonneg _
  have h3pos : 0 ≤ (1 : Real) + 1 + 1 := by mach_positivity
  have hpos : 0 ≤ (t + t - 1) * (t + t - 1) + ((1 : Real) + 1 + 1) :=
    add_nonneg hsq h3pos
  have hident : (t + t - 1) * (t + t - 1) + ((1 : Real) + 1 + 1)
      = (1 + 1 + 1 + 1) * ((1 - t) - (-(t * t))) := by mach_mpoly [t]
  rw [hident] at hpos
  have h4pos : (0 : Real) < 1 + 1 + 1 + 1 := by mach_positivity
  have hfinal : 0 ≤ (1 - t) - (-(t * t)) := by
    apply le_of_mul_le_mul_right_pos _ h4pos
    rw [zero_mul, mul_comm]
    exact hpos
  exact le_of_sub_nonneg hfinal

theorem gaussian_le_exp_shift (t : Real) : Real.exp (-(t * t)) ≤ Real.exp (1 - t) :=
  exp_monotone (neg_sq_le_shift t)

/-! ## §3 — `∫₀ˣ exp(1-t) dt = exp 1 - exp(1-x)`, via FTC -/

theorem hasDerivAt_one_sub (x : Real) : HasDerivAt (fun t => 1 - t) (-1) x := by
  have h := HasDerivAt_sub (fun _ : Real => 1) (fun t => t) 0 1 x (HasDerivAt_const 1 x)
    (HasDerivAt_id x)
  rwa [show (0 : Real) - 1 = -1 from by mach_mpoly []] at h

theorem hasDerivAt_exp_one_sub (x : Real) :
    HasDerivAt (fun t => Real.exp (1 - t)) (Real.exp (1 - x) * (-1)) x :=
  HasDerivAt_comp Real.exp (fun t => 1 - t) (-1) (Real.exp (1 - x)) x
    (hasDerivAt_one_sub x) (HasDerivAt_exp (1 - x))

theorem hasDerivAt_neg_exp_one_sub (x : Real) :
    HasDerivAt (fun t => -Real.exp (1 - t)) (Real.exp (1 - x)) x := by
  have h := HasDerivAt_neg (fun t => Real.exp (1 - t)) (Real.exp (1 - x) * (-1)) x
    (hasDerivAt_exp_one_sub x)
  rwa [show -(Real.exp (1 - x) * (-1)) = Real.exp (1 - x) from by
    mach_mpoly [(Real.exp (1 - x) : Real)]] at h

theorem exp_one_sub_continuous (x : Real) : ContinuousAt (fun t => Real.exp (1 - t)) x :=
  hasDerivAt_continuousAt (hasDerivAt_exp_one_sub x)

theorem shift_exp_integral_exists (x : Real) (hx : 0 ≤ x) :
    ∃ I : Real,
      (∀ k, lowerSumCont (fun t => Real.exp (1 - t)) 0 x hx
          (fun z _ _ => exp_one_sub_continuous z) (2 ^ k) (two_pow_pos k) ≤ I ∧
        I ≤ upperSumCont (fun t => Real.exp (1 - t)) 0 x hx
          (fun z _ _ => exp_one_sub_continuous z) (2 ^ k) (two_pow_pos k)) ∧
      (∀ ε : Real, 0 < ε → ∃ k,
        upperSumCont (fun t => Real.exp (1 - t)) 0 x hx (fun z _ _ => exp_one_sub_continuous z)
            (2 ^ k) (two_pow_pos k)
          - lowerSumCont (fun t => Real.exp (1 - t)) 0 x hx
              (fun z _ _ => exp_one_sub_continuous z) (2 ^ k) (two_pow_pos k) < ε) :=
  continuous_riemann_integrable (fun t => Real.exp (1 - t)) 0 x hx
    (fun z _ _ => exp_one_sub_continuous z)

noncomputable def shiftExpIntegral (x : Real) (hx : 0 ≤ x) : Real :=
  Classical.choose (shift_exp_integral_exists x hx)

theorem shiftExpIntegral_eq (x : Real) (hx : 0 < x) :
    shiftExpIntegral x (le_of_lt hx) = Real.exp 1 - Real.exp (1 - x) := by
  have hspec := Classical.choose_spec (shift_exp_integral_exists x (le_of_lt hx))
  have heq := ftc_riemann (fun t => Real.exp (1 - t)) (fun t => -Real.exp (1 - t)) 0 x hx
    (fun z _ _ => exp_one_sub_continuous z) (fun z _ _ => hasDerivAt_neg_exp_one_sub z)
    (shiftExpIntegral x (le_of_lt hx)) (fun k => (hspec.1 k).1) (fun k => (hspec.1 k).2) hspec.2
  rw [heq]
  show -Real.exp (1 - x) - -Real.exp (1 - 0) = Real.exp 1 - Real.exp (1 - x)
  rw [show (1 : Real) - 0 = 1 from by mach_mpoly []]
  mach_mpoly [(Real.exp (1 - x) : Real), (Real.exp (1 : Real) : Real)]

/-! ## §4 — Uniform bound: `gaussianIntegral x ≤ exp 1` for every `x ≥ 0` -/

theorem gaussianIntegral_le_shiftExpIntegral (x : Real) (hx : 0 ≤ x) :
    gaussianIntegral x hx ≤ shiftExpIntegral x hx := by
  have hgspec := Classical.choose_spec (gaussian_integral_exists x hx)
  have hhspec := Classical.choose_spec (shift_exp_integral_exists x hx)
  exact riemann_integral_mono (fun t => Real.exp (-(t * t))) (fun t => Real.exp (1 - t)) 0 x hx
    (fun z _ _ => gaussian_continuous z) (fun z _ _ => exp_one_sub_continuous z)
    (fun t _ _ => gaussian_le_exp_shift t) (gaussianIntegral x hx) (shiftExpIntegral x hx)
    (fun k => (hgspec.1 k).2) (fun k => (hhspec.1 k).1) hhspec.2

theorem gaussianIntegral_le_exp_one (x : Real) (hx : 0 ≤ x) :
    gaussianIntegral x hx ≤ Real.exp 1 := by
  rcases (le_iff_lt_or_eq 0 x).mp hx with hxpos | hxeq
  · have h1 := gaussianIntegral_le_shiftExpIntegral x hx
    have h2 : shiftExpIntegral x hx = Real.exp 1 - Real.exp (1 - x) := shiftExpIntegral_eq x hxpos
    rw [h2] at h1
    have hep := exp_pos (1 - x)
    have h3 := add_lt_add_left hep (Real.exp 1 - Real.exp (1 - x))
    rw [add_zero, show Real.exp 1 - Real.exp (1 - x) + Real.exp (1 - x) = Real.exp 1 from by
      mach_mpoly [(Real.exp 1 : Real), (Real.exp (1 - x) : Real)]] at h3
    exact le_trans h1 (le_of_lt h3)
  · have hgspec := Classical.choose_spec (gaussian_integral_exists x hx)
    have hupz : upperSumCont (fun t => Real.exp (-(t * t))) 0 x hx
        (fun z _ _ => gaussian_continuous z) (2 ^ 0) (two_pow_pos 0) = 0 := by
      show partialSum (maxSub (fun t => Real.exp (-(t * t))) 0 x hx
          (fun z _ _ => gaussian_continuous z) (2 ^ 0) (two_pow_pos 0)) (2 ^ 0)
          * meshWidth 0 x (2 ^ 0) = 0
      have hw0 : meshWidth 0 x (2 ^ 0) = 0 := by
        show (x - 0) / natCast (2 ^ 0) = 0
        rw [← hxeq, sub_self, zero_div]
      rw [hw0, mul_zero]
    have h1' : gaussianIntegral x hx ≤ upperSumCont (fun t => Real.exp (-(t * t))) 0 x hx
        (fun z _ _ => gaussian_continuous z) (2 ^ 0) (two_pow_pos 0) := (hgspec.1 0).2
    rw [hupz] at h1'
    exact le_trans h1' (le_of_lt (exp_pos 1))

/-! ## §5 — The improper Gaussian integral `∫₀^∞ exp(-t²) dt` exists -/

/-- **The improper Gaussian integral exists.** `G` is the LEAST upper bound of `{gaussianIntegral x
| x ≥ 0}` — every finite integral is `≤ G`, and `G` is approached arbitrarily closely. This is
`∫₀^∞ exp(-t²) dt` as a genuine real number, for the first time in MachLib. -/
theorem gaussianImproperIntegral_exists :
    ∃ G : Real, (∀ x (hx : 0 ≤ x), gaussianIntegral x hx ≤ G) ∧
      (∀ ε : Real, 0 < ε → ∃ x, ∃ hx : 0 ≤ x, G - ε < gaussianIntegral x hx) := by
  have hne : ∃ y, ∃ x, ∃ hx : 0 ≤ x, y = gaussianIntegral x hx :=
    ⟨gaussianIntegral 0 (le_refl 0), 0, le_refl 0, rfl⟩
  have hbd : BoundedAbove (fun y => ∃ x, ∃ hx : 0 ≤ x, y = gaussianIntegral x hx) :=
    ⟨Real.exp 1, fun y hy => by
      obtain ⟨t, ht, heq⟩ := hy
      rw [heq]
      exact gaussianIntegral_le_exp_one t ht⟩
  obtain ⟨G, hub, hlub⟩ :=
    sup_exists (fun y => ∃ x, ∃ hx : 0 ≤ x, y = gaussianIntegral x hx) hne hbd
  refine ⟨G, fun x hx => hub (gaussianIntegral x hx) ⟨x, hx, rfl⟩, ?_⟩
  intro ε hε
  apply Classical.byContradiction
  intro hcon
  have hbd' : ∀ y, (∃ x, ∃ hx : 0 ≤ x, y = gaussianIntegral x hx) → y ≤ G - ε := by
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

end Real
end MachLib
