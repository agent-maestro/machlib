/-
`RiemannIntegralTranslation.lean` — the Riemann integral is translation-invariant: for `f`
continuous on `[a,b]`, the integral of `f` over `[a,b]` equals the integral of the SHIFTED function
`g(t) := f(a+t)` over `[0,b-a]`.

Why: this is the first piece toward interval additivity (`∫₀ᵃf + ∫ₐᵇf = ∫₀ᵇf`), itself needed for
"FTC part 1" (the integral, as a function of its upper limit, has derivative equal to the
integrand) — which the √π project's disk/square sandwich turns out to need, discovered while
designing that construction. All of MachLib's existing Riemann-integral machinery is specialized to
base point `0` (`meshPoint_zero_base` etc. in `RiemannIntervalMonotone.lean`); translation lets a
`[a,b]`-interval argument be REDUCED to a `[0,b-a]`-interval one instead of re-deriving everything
for a general base point.
-/
import MachLib.RiemannIntegralFTC

namespace MachLib
namespace Real

/-! ## §1 — shifting continuity -/

private theorem shift_diff_eq (p y x : Real) : p + y - (p + x) = y - x := by mach_mpoly [p, y, x]

theorem continuousAt_shift {f : Real → Real} {p x : Real} (h : ContinuousAt f (p + x)) :
    ContinuousAt (fun t => f (p + t)) x := by
  show ∀ ε : Real, 0 < ε → ∃ δ : Real, 0 < δ ∧ ∀ y : Real, abs (y - x) < δ →
    abs (f (p + y) - f (p + x)) < ε
  intro ε hε
  obtain ⟨δ, hδpos, hδ⟩ := h ε hε
  refine ⟨δ, hδpos, ?_⟩
  intro y hy
  exact hδ (p + y) (by rw [shift_diff_eq p y x]; exact hy)

/-! ## §2 — shifting mesh points -/

private theorem sub_zero_local_t (x : Real) : x - 0 = x := by mach_mpoly [x]

theorem meshPoint_shift (a b : Real) (n i : Nat) :
    meshPoint a b n i = a + meshPoint 0 (b - a) n i := by
  show a + natCast i * ((b - a) / natCast n) = a + (0 + natCast i * ((b - a - 0) / natCast n))
  rw [sub_zero_local_t (b - a)]
  mach_mpoly [a, natCast i, (b - a) / natCast n]

private theorem sub_le_sub_right_local {x y : Real} (h : x ≤ y) (c : Real) : x - c ≤ y - c := by
  have h1 := add_le_add_both h (le_refl (-c))
  rwa [← sub_def x c, ← sub_def y c] at h1

theorem meshPoint_shift_sub (a b : Real) (n i : Nat) :
    meshPoint a b n i - a = meshPoint 0 (b - a) n i := by
  rw [meshPoint_shift a b n i]
  mach_mpoly [a, meshPoint 0 (b - a) n i]

/-! ## §3 — shifting `minSub`/`maxSub` -/

theorem minSub_shift (f : Real → Real) (a b : Real) (hab : a ≤ b)
    (hcont : ∀ z : Real, a ≤ z → z ≤ b → ContinuousAt f z)
    (hab' : (0:Real) ≤ b - a)
    (hcont' : ∀ z : Real, 0 ≤ z → z ≤ b - a → ContinuousAt (fun t => f (a + t)) z)
    (n : Nat) (hn : 0 < n) (i : Nat) (hi : i < n) :
    minSub f a b hab hcont n hn i = minSub (fun t => f (a + t)) 0 (b - a) hab' hcont' n hn i := by
  apply le_antisymm
  · rw [minSub_eq (fun t => f (a + t)) 0 (b - a) hab' hcont' n hn i hi]
    have hmemg := minSub_mem (fun t => f (a + t)) 0 (b - a) hab' hcont' n hn i hi
    have h1 : meshPoint a b n i ≤ a + Classical.choose
        (evt_exists_min (fun t => f (a + t)) 0 (b - a) hab' hcont' n hn i hi) := by
      rw [meshPoint_shift a b n i]
      exact add_le_add_left hmemg.1 a
    have h2 : a + Classical.choose
        (evt_exists_min (fun t => f (a + t)) 0 (b - a) hab' hcont' n hn i hi)
        ≤ meshPoint a b n (i + 1) := by
      rw [meshPoint_shift a b n (i + 1)]
      exact add_le_add_left hmemg.2 a
    exact minSub_spec f a b hab hcont n hn i hi _ h1 h2
  · rw [minSub_eq f a b hab hcont n hn i hi]
    have hmemf := minSub_mem f a b hab hcont n hn i hi
    have h1 : meshPoint 0 (b - a) n i
        ≤ Classical.choose (evt_exists_min f a b hab hcont n hn i hi) - a := by
      rw [← meshPoint_shift_sub a b n i]
      exact sub_le_sub_right_local hmemf.1 a
    have h2 : Classical.choose (evt_exists_min f a b hab hcont n hn i hi) - a
        ≤ meshPoint 0 (b - a) n (i + 1) := by
      rw [← meshPoint_shift_sub a b n (i + 1)]
      exact sub_le_sub_right_local hmemf.2 a
    have hspec : minSub (fun t => f (a + t)) 0 (b - a) hab' hcont' n hn i
        ≤ f (a + (Classical.choose (evt_exists_min f a b hab hcont n hn i hi) - a)) :=
      minSub_spec (fun t => f (a + t)) 0 (b - a) hab' hcont' n hn i hi _ h1 h2
    have heq : a + (Classical.choose (evt_exists_min f a b hab hcont n hn i hi) - a)
        = Classical.choose (evt_exists_min f a b hab hcont n hn i hi) := by
      mach_mpoly [a, Classical.choose (evt_exists_min f a b hab hcont n hn i hi)]
    rwa [heq] at hspec

theorem maxSub_shift (f : Real → Real) (a b : Real) (hab : a ≤ b)
    (hcont : ∀ z : Real, a ≤ z → z ≤ b → ContinuousAt f z)
    (hab' : (0:Real) ≤ b - a)
    (hcont' : ∀ z : Real, 0 ≤ z → z ≤ b - a → ContinuousAt (fun t => f (a + t)) z)
    (n : Nat) (hn : 0 < n) (i : Nat) (hi : i < n) :
    maxSub f a b hab hcont n hn i = maxSub (fun t => f (a + t)) 0 (b - a) hab' hcont' n hn i := by
  apply le_antisymm
  · rw [maxSub_eq f a b hab hcont n hn i hi]
    have hmemf := maxSub_mem f a b hab hcont n hn i hi
    have h1 : meshPoint 0 (b - a) n i
        ≤ Classical.choose (evt_exists_max f a b hab hcont n hn i hi) - a := by
      rw [← meshPoint_shift_sub a b n i]
      exact sub_le_sub_right_local hmemf.1 a
    have h2 : Classical.choose (evt_exists_max f a b hab hcont n hn i hi) - a
        ≤ meshPoint 0 (b - a) n (i + 1) := by
      rw [← meshPoint_shift_sub a b n (i + 1)]
      exact sub_le_sub_right_local hmemf.2 a
    have hspec : f (a + (Classical.choose (evt_exists_max f a b hab hcont n hn i hi) - a))
        ≤ maxSub (fun t => f (a + t)) 0 (b - a) hab' hcont' n hn i :=
      maxSub_spec (fun t => f (a + t)) 0 (b - a) hab' hcont' n hn i hi _ h1 h2
    have heq : a + (Classical.choose (evt_exists_max f a b hab hcont n hn i hi) - a)
        = Classical.choose (evt_exists_max f a b hab hcont n hn i hi) := by
      mach_mpoly [a, Classical.choose (evt_exists_max f a b hab hcont n hn i hi)]
    rwa [heq] at hspec
  · rw [maxSub_eq (fun t => f (a + t)) 0 (b - a) hab' hcont' n hn i hi]
    have hmemg := maxSub_mem (fun t => f (a + t)) 0 (b - a) hab' hcont' n hn i hi
    have h1 : meshPoint a b n i ≤ a + Classical.choose
        (evt_exists_max (fun t => f (a + t)) 0 (b - a) hab' hcont' n hn i hi) := by
      rw [meshPoint_shift a b n i]
      exact add_le_add_left hmemg.1 a
    have h2 : a + Classical.choose
        (evt_exists_max (fun t => f (a + t)) 0 (b - a) hab' hcont' n hn i hi)
        ≤ meshPoint a b n (i + 1) := by
      rw [meshPoint_shift a b n (i + 1)]
      exact add_le_add_left hmemg.2 a
    exact maxSub_spec f a b hab hcont n hn i hi _ h1 h2

/-! ## §4 — shifting `lowerSumCont`/`upperSumCont` and the integral value -/

theorem meshWidth_shift (a b : Real) (n : Nat) : meshWidth a b n = meshWidth 0 (b - a) n := by
  show (b - a) / natCast n = (b - a - 0) / natCast n
  rw [sub_zero_local_t (b - a)]

private theorem partialSum_congr_bounded {g h : Nat → Real} (n : Nat) (heq : ∀ i, i < n → h i = g i) :
    partialSum h n = partialSum g n := by
  apply le_antisymm
  · exact partialSum_le_of_termwise_le n (fun i hi => le_of_eq (heq i hi))
  · exact partialSum_le_of_termwise_le n (fun i hi => le_of_eq (heq i hi).symm)

theorem lowerSumCont_shift (f : Real → Real) (a b : Real) (hab : a ≤ b)
    (hcont : ∀ z : Real, a ≤ z → z ≤ b → ContinuousAt f z)
    (hab' : (0:Real) ≤ b - a)
    (hcont' : ∀ z : Real, 0 ≤ z → z ≤ b - a → ContinuousAt (fun t => f (a + t)) z)
    (n : Nat) (hn : 0 < n) :
    lowerSumCont f a b hab hcont n hn
      = lowerSumCont (fun t => f (a + t)) 0 (b - a) hab' hcont' n hn := by
  show partialSum (minSub f a b hab hcont n hn) n * meshWidth a b n
    = partialSum (minSub (fun t => f (a + t)) 0 (b - a) hab' hcont' n hn) n * meshWidth 0 (b - a) n
  rw [partialSum_congr_bounded n (fun i hi => minSub_shift f a b hab hcont hab' hcont' n hn i hi)]
  rw [meshWidth_shift a b n]

theorem upperSumCont_shift (f : Real → Real) (a b : Real) (hab : a ≤ b)
    (hcont : ∀ z : Real, a ≤ z → z ≤ b → ContinuousAt f z)
    (hab' : (0:Real) ≤ b - a)
    (hcont' : ∀ z : Real, 0 ≤ z → z ≤ b - a → ContinuousAt (fun t => f (a + t)) z)
    (n : Nat) (hn : 0 < n) :
    upperSumCont f a b hab hcont n hn
      = upperSumCont (fun t => f (a + t)) 0 (b - a) hab' hcont' n hn := by
  show partialSum (maxSub f a b hab hcont n hn) n * meshWidth a b n
    = partialSum (maxSub (fun t => f (a + t)) 0 (b - a) hab' hcont' n hn) n * meshWidth 0 (b - a) n
  rw [partialSum_congr_bounded n (fun i hi => maxSub_shift f a b hab hcont hab' hcont' n hn i hi)]
  rw [meshWidth_shift a b n]

/-- **Headline**: the Riemann integral value is translation-invariant. `I` (the integral of `f`
over `[a,b]`) equals `J` (the integral of the shifted `g(t):=f(a+t)` over `[0,b-a]`). -/
theorem riemann_integral_shift (f : Real → Real) (a b : Real) (hab : a ≤ b)
    (hcont : ∀ z : Real, a ≤ z → z ≤ b → ContinuousAt f z)
    (hab' : (0:Real) ≤ b - a)
    (hcont' : ∀ z : Real, 0 ≤ z → z ≤ b - a → ContinuousAt (fun t => f (a + t)) z)
    (I J : Real)
    (hIlow : ∀ k, lowerSumCont f a b hab hcont (2 ^ k) (two_pow_pos k) ≤ I)
    (hIup : ∀ k, I ≤ upperSumCont f a b hab hcont (2 ^ k) (two_pow_pos k))
    (hJlow : ∀ k, lowerSumCont (fun t => f (a + t)) 0 (b - a) hab' hcont' (2 ^ k) (two_pow_pos k)
      ≤ J)
    (hJup : ∀ k, J ≤ upperSumCont (fun t => f (a + t)) 0 (b - a) hab' hcont' (2 ^ k) (two_pow_pos k))
    (hgap : ∀ ε : Real, 0 < ε → ∃ k, upperSumCont f a b hab hcont (2 ^ k) (two_pow_pos k)
      - lowerSumCont f a b hab hcont (2 ^ k) (two_pow_pos k) < ε) :
    I = J := by
  apply riemann_integral_unique f a b hab hcont I J hIlow hIup
  · intro k
    rw [lowerSumCont_shift f a b hab hcont hab' hcont' (2 ^ k) (two_pow_pos k)]
    exact hJlow k
  · intro k
    rw [upperSumCont_shift f a b hab hcont hab' hcont' (2 ^ k) (two_pow_pos k)]
    exact hJup k
  · exact hgap

end Real
end MachLib
