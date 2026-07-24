import MachLib.RiemannIntegralContinuous
import MachLib.Rolle
import MachLib.WeierstrassTermByTerm

/-!
# Fundamental Theorem of Calculus, for MachLib's Riemann integral

Stage 1 of the `√π` Gaussian-normalization project (see `GaussianIntegral.lean`'s header for the
full staged plan: FTC → 1D improper integrals → 2D Riemann integration → Fubini → polar
substitution → assembly). This stage is self-contained and reuses machinery already in the
library: `Rolle.lean`'s `mean_value_theorem_ct` (the closed-interval, soundly-grounded Mean Value
Theorem) and `Differentiation.lean`'s `HasDerivAt_unique`.

`continuous_riemann_integrable` only proves EXISTENCE of a value sandwiched by every dyadic
Darboux pair with a shrinking gap — it says nothing about what that value equals in closed form.
This file closes that gap: if `F` is an antiderivative of `f` on `[a,b]` (`HasDerivAt F (f z) z`
for every `z ∈ [a,b]`), the Riemann integral of `f` over `[a,b]` equals `F b - F a`.

**Proof idea**: (1) `F b - F a` telescopes into `Σᵢ (F(xᵢ₊₁) - F(xᵢ))` over the mesh points. (2) MVT
gives, for each subinterval, a point `c` with `F(xᵢ₊₁) - F(xᵢ) = f(c)·width`, and since `c` is IN
the subinterval, `minSub ≤ f(c) ≤ maxSub` there — so each telescoped term is sandwiched exactly
the way each Darboux-sum term is. (3) Sum the sandwich termwise: `F b - F a` satisfies the SAME
`lowerSumCont ≤ · ≤ upperSumCont` property that characterizes the (unique) Riemann integral value.
(4) A value trapped between the same shrinking dyadic brackets as another value must equal it.

`sorryAx`-free, no new axioms.
-/

namespace MachLib
namespace Real

/-! ## §1 — Uniqueness of the Riemann integral value -/

private theorem sandwich_gap_lt (f : Real → Real) (a b : Real) (hab : a ≤ b)
    (hcont : ∀ z : Real, a ≤ z → z ≤ b → ContinuousAt f z) (I J η : Real) (k : Nat)
    (hIup : I ≤ upperSumCont f a b hab hcont (2 ^ k) (two_pow_pos k))
    (hJlow : lowerSumCont f a b hab hcont (2 ^ k) (two_pow_pos k) ≤ J)
    (hk : upperSumCont f a b hab hcont (2 ^ k) (two_pow_pos k)
      - lowerSumCont f a b hab hcont (2 ^ k) (two_pow_pos k) < η) :
    I < J + η := by
  have h3 : upperSumCont f a b hab hcont (2 ^ k) (two_pow_pos k)
      < lowerSumCont f a b hab hcont (2 ^ k) (two_pow_pos k) + η := by
    have hstep := add_lt_add_left hk (lowerSumCont f a b hab hcont (2 ^ k) (two_pow_pos k))
    rwa [show lowerSumCont f a b hab hcont (2 ^ k) (two_pow_pos k)
          + (upperSumCont f a b hab hcont (2 ^ k) (two_pow_pos k)
            - lowerSumCont f a b hab hcont (2 ^ k) (two_pow_pos k))
        = upperSumCont f a b hab hcont (2 ^ k) (two_pow_pos k) from by mach_ring] at hstep
  exact lt_of_le_of_lt hIup (lt_of_lt_of_le h3 (add_le_add_both hJlow (le_refl η)))

/-- **The Riemann integral value is unique.** Any two values sandwiched by every dyadic Darboux
pair, with the gap shrinking below any `ε > 0`, are equal. -/
theorem riemann_integral_unique (f : Real → Real) (a b : Real) (hab : a ≤ b)
    (hcont : ∀ z : Real, a ≤ z → z ≤ b → ContinuousAt f z) (I J : Real)
    (hIlow : ∀ k, lowerSumCont f a b hab hcont (2 ^ k) (two_pow_pos k) ≤ I)
    (hIup : ∀ k, I ≤ upperSumCont f a b hab hcont (2 ^ k) (two_pow_pos k))
    (hJlow : ∀ k, lowerSumCont f a b hab hcont (2 ^ k) (two_pow_pos k) ≤ J)
    (hJup : ∀ k, J ≤ upperSumCont f a b hab hcont (2 ^ k) (two_pow_pos k))
    (hgap : ∀ ε : Real, 0 < ε → ∃ k, upperSumCont f a b hab hcont (2 ^ k) (two_pow_pos k)
      - lowerSumCont f a b hab hcont (2 ^ k) (two_pow_pos k) < ε) :
    I = J := by
  apply le_antisymm
  · apply le_of_forall_pos_lt_add
    intro η hη
    obtain ⟨k, hk⟩ := hgap η hη
    exact sandwich_gap_lt f a b hab hcont I J η k (hIup k) (hJlow k) hk
  · apply le_of_forall_pos_lt_add
    intro η hη
    obtain ⟨k, hk⟩ := hgap η hη
    exact sandwich_gap_lt f a b hab hcont J I η k (hJup k) (hIlow k) hk

/-! ## §2 — FTC proper: `F b - F a` satisfies the same sandwich as the integral -/

private theorem lt_of_sub_pos_ftc {x y : Real} (h : 0 < y - x) : x < y := by
  have h2 := add_lt_add_left h x
  rwa [add_zero, show x + (y - x) = y from by mach_mpoly [x, y]] at h2

theorem meshPoint_lt_succ (a b : Real) (n i : Nat) (hab : a < b) (hn : 0 < n) :
    meshPoint a b n i < meshPoint a b n (i + 1) := by
  have hw : 0 < meshWidth a b n := div_pos_of_pos_pos (sub_pos_of_lt hab) (natCast_pos hn)
  apply lt_of_sub_pos_ftc
  rwa [meshPoint_succ_sub a b n i]

/-- **Per-subinterval MVT sandwich.** On each subinterval, `F` gains exactly `f(c)·width` for some
`c` IN the subinterval, hence between `minSub` and `maxSub` there. -/
theorem ftc_subinterval_sandwich (f F : Real → Real) (a b : Real) (hab : a < b)
    (hcont : ∀ z : Real, a ≤ z → z ≤ b → ContinuousAt f z)
    (hF : ∀ z : Real, a ≤ z → z ≤ b → HasDerivAt F (f z) z)
    (n : Nat) (hn : 0 < n) (i : Nat) (hi : i < n) :
    minSub f a b (le_of_lt hab) hcont n hn i * meshWidth a b n
      ≤ F (meshPoint a b n (i + 1)) - F (meshPoint a b n i)
    ∧ F (meshPoint a b n (i + 1)) - F (meshPoint a b n i)
      ≤ maxSub f a b (le_of_lt hab) hcont n hn i * meshWidth a b n := by
  have hlt : meshPoint a b n i < meshPoint a b n (i + 1) := meshPoint_lt_succ a b n i hab hn
  have hmemL : a ≤ meshPoint a b n i := (meshPoint_mem a b n i (le_of_lt hab) hn (Nat.le_of_lt hi)).1
  have hmemR : meshPoint a b n (i + 1) ≤ b := (meshPoint_mem a b n (i + 1) (le_of_lt hab) hn hi).2
  have hdiff : ∀ c : Real, meshPoint a b n i ≤ c → c ≤ meshPoint a b n (i + 1) → ∃ f' : Real,
      HasDerivAt F f' c := fun c hc1 hc2 =>
    ⟨f c, hF c (le_trans hmemL hc1) (le_trans hc2 hmemR)⟩
  obtain ⟨c, f', hc1, hc2, hderiv, heq⟩ :=
    mean_value_theorem_ct F (meshPoint a b n i) (meshPoint a b n (i + 1)) hlt hdiff
  have hca : a ≤ c := le_trans hmemL (le_of_lt hc1)
  have hcb : c ≤ b := le_trans (le_of_lt hc2) hmemR
  have hfc : HasDerivAt F (f c) c := hF c hca hcb
  have hfeq : f' = f c := HasDerivAt_unique F f' (f c) c hderiv hfc
  rw [hfeq, meshPoint_succ_sub a b n i] at heq
  have hclow : meshPoint a b n i ≤ c := le_of_lt hc1
  have hcup : c ≤ meshPoint a b n (i + 1) := le_of_lt hc2
  have hminle : minSub f a b (le_of_lt hab) hcont n hn i ≤ f c :=
    minSub_spec f a b (le_of_lt hab) hcont n hn i hi c hclow hcup
  have hlemax : f c ≤ maxSub f a b (le_of_lt hab) hcont n hn i :=
    maxSub_spec f a b (le_of_lt hab) hcont n hn i hi c hclow hcup
  rw [heq]
  refine ⟨?_, ?_⟩
  · exact mul_le_mul_of_nonneg_right hminle (meshWidth_nonneg (le_of_lt hab) n)
  · exact mul_le_mul_of_nonneg_right hlemax (meshWidth_nonneg (le_of_lt hab) n)

/-! ## §3 — Summed: `F b - F a` satisfies the SAME sandwich as the integral, at every level `n` -/

/-- **FTC, at a fixed partition level.** `F b - F a` is sandwiched between the lower and upper
Darboux sums of `f`, the same way the (unique) Riemann integral value is. -/
theorem ftc_sandwiched (f F : Real → Real) (a b : Real) (hab : a < b)
    (hcont : ∀ z : Real, a ≤ z → z ≤ b → ContinuousAt f z)
    (hF : ∀ z : Real, a ≤ z → z ≤ b → HasDerivAt F (f z) z) (n : Nat) (hn : 0 < n) :
    lowerSumCont f a b (le_of_lt hab) hcont n hn ≤ F b - F a
    ∧ F b - F a ≤ upperSumCont f a b (le_of_lt hab) hcont n hn := by
  have htel : partialSum (fun i => F (meshPoint a b n (i + 1)) - F (meshPoint a b n i)) n
      = F b - F a := by
    rw [partialSum_sub (fun i => F (meshPoint a b n (i + 1))) (fun i => F (meshPoint a b n i)) n]
    have h := partialSum_shift_sub (fun i => F (meshPoint a b n i)) n
    rwa [meshPoint_n a b n hn, meshPoint_zero a b n] at h
  constructor
  · show partialSum (minSub f a b (le_of_lt hab) hcont n hn) n * meshWidth a b n ≤ F b - F a
    rw [← htel]
    have hpair : ∀ i, i < n →
        meshWidth a b n * minSub f a b (le_of_lt hab) hcont n hn i
          ≤ F (meshPoint a b n (i + 1)) - F (meshPoint a b n i) := by
      intro i hi
      have hs := (ftc_subinterval_sandwich f F a b hab hcont hF n hn i hi).1
      rwa [mul_comm] at hs
    have hsum := partialSum_le_of_termwise_le n hpair
    rw [partialSum_const_mul (meshWidth a b n) (minSub f a b (le_of_lt hab) hcont n hn) n] at hsum
    rwa [mul_comm]
  · show F b - F a ≤ partialSum (maxSub f a b (le_of_lt hab) hcont n hn) n * meshWidth a b n
    rw [← htel]
    have hpair : ∀ i, i < n →
        F (meshPoint a b n (i + 1)) - F (meshPoint a b n i)
          ≤ meshWidth a b n * maxSub f a b (le_of_lt hab) hcont n hn i := by
      intro i hi
      have hs := (ftc_subinterval_sandwich f F a b hab hcont hF n hn i hi).2
      rwa [mul_comm] at hs
    have hsum := partialSum_le_of_termwise_le n hpair
    rw [partialSum_const_mul (meshWidth a b n) (maxSub f a b (le_of_lt hab) hcont n hn) n] at hsum
    rwa [mul_comm]

/-! ## §4 — Headline: `∫ₐᵇ f = F b - F a` -/

/-- **Fundamental Theorem of Calculus.** If `F` is an antiderivative of `f` on `[a,b]` and `I` is
the (unique) Riemann integral value of `f` over `[a,b]`, then `I = F b - F a`. -/
theorem ftc_riemann (f F : Real → Real) (a b : Real) (hab : a < b)
    (hcont : ∀ z : Real, a ≤ z → z ≤ b → ContinuousAt f z)
    (hF : ∀ z : Real, a ≤ z → z ≤ b → HasDerivAt F (f z) z) (I : Real)
    (hIlow : ∀ k, lowerSumCont f a b (le_of_lt hab) hcont (2 ^ k) (two_pow_pos k) ≤ I)
    (hIup : ∀ k, I ≤ upperSumCont f a b (le_of_lt hab) hcont (2 ^ k) (two_pow_pos k))
    (hgap : ∀ ε : Real, 0 < ε → ∃ k, upperSumCont f a b (le_of_lt hab) hcont (2 ^ k) (two_pow_pos k)
      - lowerSumCont f a b (le_of_lt hab) hcont (2 ^ k) (two_pow_pos k) < ε) :
    I = F b - F a :=
  riemann_integral_unique f a b (le_of_lt hab) hcont I (F b - F a) hIlow hIup
    (fun k => (ftc_sandwiched f F a b hab hcont hF (2 ^ k) (two_pow_pos k)).1)
    (fun k => (ftc_sandwiched f F a b hab hcont hF (2 ^ k) (two_pow_pos k)).2) hgap

end Real
end MachLib
