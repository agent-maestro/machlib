import MachLib.RiemannIntegralMonotone
import MachLib.HeineCantorUniformContinuity
import MachLib.ExtremeValueAttainment
import MachLib.UniformConvergence
import MachLib.Sign

/-!
# Riemann integral for continuous integrands

Extends `RiemannIntegralMonotone.lean` from monotone to arbitrary CONTINUOUS integrands, reusing
its `meshPoint`/`meshWidth`/`partialSum` substrate directly. Two ingredients that didn't exist when
that file was written now do: `ExtremeValueAttainment.lean` supplies per-subinterval Darboux
extrema (a continuous function attains its max/min on a compact subinterval — no `Classical.choose`
gymnastics needed beyond extracting the witness point), and `HeineCantorUniformContinuity.lean`
supplies a DIRECT, mesh-uniform gap bound. This means the construction here is actually SIMPLER
than the monotone file's: no dyadic-doubling refinement is needed at all, since uniform continuity
bounds `upperSum − lowerSum` by `ε·(b−a)` for ANY uniform partition fine enough (mesh `< δ`), not
just a doubling subsequence.

`sorryAx`-free, no new axioms — `Classical.choice` (already used pervasively, e.g.
`UniformConvergence.lean`'s `Gsum`/`Hsum`) plus `sup_exists`/`archimedean`.
-/

namespace MachLib
namespace Real

/-! ## §1 — Per-subinterval Darboux extrema, via EVT -/

private theorem hcont_sub (f : Real → Real) (a b : Real) (hab : a ≤ b)
    (hcont : ∀ z : Real, a ≤ z → z ≤ b → ContinuousAt f z) (n : Nat) (hn : 0 < n) (i : Nat)
    (hi : i < n) :
    ∀ z, meshPoint a b n i ≤ z → z ≤ meshPoint a b n (i + 1) → ContinuousAt f z :=
  fun z hz1 hz2 => hcont z
    (le_trans (meshPoint_mem a b n i hab hn (Nat.le_of_lt hi)).1 hz1)
    (le_trans hz2 (meshPoint_mem a b n (i + 1) hab hn hi).2)

theorem evt_exists_max (f : Real → Real) (a b : Real) (hab : a ≤ b)
    (hcont : ∀ z : Real, a ≤ z → z ≤ b → ContinuousAt f z) (n : Nat) (hn : 0 < n) (i : Nat)
    (hi : i < n) :
    ∃ c, meshPoint a b n i ≤ c ∧ c ≤ meshPoint a b n (i + 1) ∧
      ∀ x, meshPoint a b n i ≤ x → x ≤ meshPoint a b n (i + 1) → f x ≤ f c :=
  continuousAt_attains_max_Icc f (meshPoint a b n i) (meshPoint a b n (i + 1))
    (meshPoint_le_succ a b n i hab) (hcont_sub f a b hab hcont n hn i hi)

theorem evt_exists_min (f : Real → Real) (a b : Real) (hab : a ≤ b)
    (hcont : ∀ z : Real, a ≤ z → z ≤ b → ContinuousAt f z) (n : Nat) (hn : 0 < n) (i : Nat)
    (hi : i < n) :
    ∃ c, meshPoint a b n i ≤ c ∧ c ≤ meshPoint a b n (i + 1) ∧
      ∀ x, meshPoint a b n i ≤ x → x ≤ meshPoint a b n (i + 1) → f c ≤ f x :=
  continuousAt_attains_min_Icc f (meshPoint a b n i) (meshPoint a b n (i + 1))
    (meshPoint_le_succ a b n i hab) (hcont_sub f a b hab hcont n hn i hi)

/-- The value of `f` at the (chosen) point where `f` attains its max on subinterval `i`; `f a` for
`i` out of range (never summed, only needed for totality). -/
noncomputable def maxSub (f : Real → Real) (a b : Real) (hab : a ≤ b)
    (hcont : ∀ z : Real, a ≤ z → z ≤ b → ContinuousAt f z) (n : Nat) (hn : 0 < n) (i : Nat) : Real :=
  if hi : i < n then f (Classical.choose (evt_exists_max f a b hab hcont n hn i hi)) else f a

noncomputable def minSub (f : Real → Real) (a b : Real) (hab : a ≤ b)
    (hcont : ∀ z : Real, a ≤ z → z ≤ b → ContinuousAt f z) (n : Nat) (hn : 0 < n) (i : Nat) : Real :=
  if hi : i < n then f (Classical.choose (evt_exists_min f a b hab hcont n hn i hi)) else f a

theorem maxSub_eq (f : Real → Real) (a b : Real) (hab : a ≤ b)
    (hcont : ∀ z : Real, a ≤ z → z ≤ b → ContinuousAt f z) (n : Nat) (hn : 0 < n) (i : Nat)
    (hi : i < n) :
    maxSub f a b hab hcont n hn i = f (Classical.choose (evt_exists_max f a b hab hcont n hn i hi)) := by
  unfold maxSub; rw [dif_pos hi]

theorem minSub_eq (f : Real → Real) (a b : Real) (hab : a ≤ b)
    (hcont : ∀ z : Real, a ≤ z → z ≤ b → ContinuousAt f z) (n : Nat) (hn : 0 < n) (i : Nat)
    (hi : i < n) :
    minSub f a b hab hcont n hn i = f (Classical.choose (evt_exists_min f a b hab hcont n hn i hi)) := by
  unfold minSub; rw [dif_pos hi]

theorem maxSub_spec (f : Real → Real) (a b : Real) (hab : a ≤ b)
    (hcont : ∀ z : Real, a ≤ z → z ≤ b → ContinuousAt f z) (n : Nat) (hn : 0 < n) (i : Nat)
    (hi : i < n) :
    ∀ x, meshPoint a b n i ≤ x → x ≤ meshPoint a b n (i + 1) → f x ≤ maxSub f a b hab hcont n hn i := by
  rw [maxSub_eq f a b hab hcont n hn i hi]
  exact (Classical.choose_spec (evt_exists_max f a b hab hcont n hn i hi)).2.2

theorem minSub_spec (f : Real → Real) (a b : Real) (hab : a ≤ b)
    (hcont : ∀ z : Real, a ≤ z → z ≤ b → ContinuousAt f z) (n : Nat) (hn : 0 < n) (i : Nat)
    (hi : i < n) :
    ∀ x, meshPoint a b n i ≤ x → x ≤ meshPoint a b n (i + 1) → minSub f a b hab hcont n hn i ≤ f x := by
  rw [minSub_eq f a b hab hcont n hn i hi]
  exact (Classical.choose_spec (evt_exists_min f a b hab hcont n hn i hi)).2.2

theorem maxSub_mem (f : Real → Real) (a b : Real) (hab : a ≤ b)
    (hcont : ∀ z : Real, a ≤ z → z ≤ b → ContinuousAt f z) (n : Nat) (hn : 0 < n) (i : Nat)
    (hi : i < n) :
    meshPoint a b n i ≤ Classical.choose (evt_exists_max f a b hab hcont n hn i hi) ∧
      Classical.choose (evt_exists_max f a b hab hcont n hn i hi) ≤ meshPoint a b n (i + 1) :=
  ⟨(Classical.choose_spec (evt_exists_max f a b hab hcont n hn i hi)).1,
    (Classical.choose_spec (evt_exists_max f a b hab hcont n hn i hi)).2.1⟩

theorem minSub_mem (f : Real → Real) (a b : Real) (hab : a ≤ b)
    (hcont : ∀ z : Real, a ≤ z → z ≤ b → ContinuousAt f z) (n : Nat) (hn : 0 < n) (i : Nat)
    (hi : i < n) :
    meshPoint a b n i ≤ Classical.choose (evt_exists_min f a b hab hcont n hn i hi) ∧
      Classical.choose (evt_exists_min f a b hab hcont n hn i hi) ≤ meshPoint a b n (i + 1) :=
  ⟨(Classical.choose_spec (evt_exists_min f a b hab hcont n hn i hi)).1,
    (Classical.choose_spec (evt_exists_min f a b hab hcont n hn i hi)).2.1⟩

theorem minSub_le_maxSub (f : Real → Real) (a b : Real) (hab : a ≤ b)
    (hcont : ∀ z : Real, a ≤ z → z ≤ b → ContinuousAt f z) (n : Nat) (hn : 0 < n) (i : Nat) :
    minSub f a b hab hcont n hn i ≤ maxSub f a b hab hcont n hn i := by
  by_cases hi : i < n
  · have hmem := maxSub_mem f a b hab hcont n hn i hi
    have h1 : minSub f a b hab hcont n hn i
        ≤ f (Classical.choose (evt_exists_max f a b hab hcont n hn i hi)) :=
      minSub_spec f a b hab hcont n hn i hi _ hmem.1 hmem.2
    rwa [← maxSub_eq f a b hab hcont n hn i hi] at h1
  · unfold maxSub minSub; rw [dif_neg hi, dif_neg hi]; exact le_refl _

/-! ## §2 — Darboux sums and the uniform-continuity gap bound -/

noncomputable def lowerSumCont (f : Real → Real) (a b : Real) (hab : a ≤ b)
    (hcont : ∀ z : Real, a ≤ z → z ≤ b → ContinuousAt f z) (n : Nat) (hn : 0 < n) : Real :=
  partialSum (minSub f a b hab hcont n hn) n * meshWidth a b n

noncomputable def upperSumCont (f : Real → Real) (a b : Real) (hab : a ≤ b)
    (hcont : ∀ z : Real, a ≤ z → z ≤ b → ContinuousAt f z) (n : Nat) (hn : 0 < n) : Real :=
  partialSum (maxSub f a b hab hcont n hn) n * meshWidth a b n

theorem lowerSumCont_le_upperSumCont (f : Real → Real) (a b : Real) (hab : a ≤ b)
    (hcont : ∀ z : Real, a ≤ z → z ≤ b → ContinuousAt f z) (n : Nat) (hn : 0 < n) :
    lowerSumCont f a b hab hcont n hn ≤ upperSumCont f a b hab hcont n hn := by
  unfold lowerSumCont upperSumCont
  apply mul_le_mul_of_nonneg_right _ (meshWidth_nonneg hab n)
  apply partialSum_le_of_le
  intro i
  exact minSub_le_maxSub f a b hab hcont n hn i

theorem meshPoint_succ_sub (a b : Real) (n i : Nat) :
    meshPoint a b n (i + 1) - meshPoint a b n i = meshWidth a b n := by
  show (a + natCast (i + 1) * meshWidth a b n) - (a + natCast i * meshWidth a b n) = meshWidth a b n
  rw [natCast_succ]
  mach_mpoly [a, natCast i, (meshWidth a b n : Real)]

private theorem abs_sub_le_of_mem (x y lo hiv : Real) (hx1 : lo ≤ x) (hx2 : x ≤ hiv) (hy1 : lo ≤ y)
    (hy2 : y ≤ hiv) : abs (x - y) ≤ hiv - lo := by
  apply abs_le_of
  · have h1 := add_le_add_both hx2 (neg_le_neg hy1)
    rwa [show hiv + -lo = hiv - lo from by mach_mpoly [hiv, lo],
      show x + -y = x - y from by mach_mpoly [x, y]] at h1
  · show -(x - y) ≤ hiv - lo
    have h2 := add_le_add_both hy2 (neg_le_neg hx1)
    rw [show hiv + -lo = hiv - lo from by mach_mpoly [hiv, lo],
      show y + -x = y - x from by mach_mpoly [x, y]] at h2
    rwa [show -(x - y) = y - x from by mach_mpoly [x, y]]

/-- **The gap bound.** If the mesh is fine enough that any two points within a subinterval land
inside `f`'s `ε`-modulus `δ`, the Darboux gap on THAT subinterval is `< ε`. -/
theorem maxSub_sub_minSub_lt (f : Real → Real) (a b : Real) (hab : a ≤ b)
    (hcont : ∀ z : Real, a ≤ z → z ≤ b → ContinuousAt f z) (n : Nat) (hn : 0 < n) (i : Nat)
    (hi : i < n) {δ ε : Real}
    (hδ : ∀ y z : Real, a ≤ y → y ≤ b → a ≤ z → z ≤ b → abs (y - z) < δ → abs (f y - f z) < ε)
    (hw : meshWidth a b n < δ) :
    maxSub f a b hab hcont n hn i - minSub f a b hab hcont n hn i < ε := by
  have hmemMax := maxSub_mem f a b hab hcont n hn i hi
  have hmemMin := minSub_mem f a b hab hcont n hn i hi
  have hbound : abs (Classical.choose (evt_exists_max f a b hab hcont n hn i hi)
      - Classical.choose (evt_exists_min f a b hab hcont n hn i hi)) ≤ meshWidth a b n := by
    have := abs_sub_le_of_mem _ _ _ _ hmemMax.1 hmemMax.2 hmemMin.1 hmemMin.2
    rwa [meshPoint_succ_sub a b n i] at this
  have hlt : abs (Classical.choose (evt_exists_max f a b hab hcont n hn i hi)
      - Classical.choose (evt_exists_min f a b hab hcont n hn i hi)) < δ :=
    lt_of_le_of_lt hbound hw
  have hmaxa : a ≤ Classical.choose (evt_exists_max f a b hab hcont n hn i hi) :=
    le_trans (meshPoint_mem a b n i hab hn (Nat.le_of_lt hi)).1 hmemMax.1
  have hmaxb : Classical.choose (evt_exists_max f a b hab hcont n hn i hi) ≤ b :=
    le_trans hmemMax.2 (meshPoint_mem a b n (i + 1) hab hn hi).2
  have hmina : a ≤ Classical.choose (evt_exists_min f a b hab hcont n hn i hi) :=
    le_trans (meshPoint_mem a b n i hab hn (Nat.le_of_lt hi)).1 hmemMin.1
  have hminb : Classical.choose (evt_exists_min f a b hab hcont n hn i hi) ≤ b :=
    le_trans hmemMin.2 (meshPoint_mem a b n (i + 1) hab hn hi).2
  have hflt := hδ _ _ hmaxa hmaxb hmina hminb hlt
  rw [← maxSub_eq f a b hab hcont n hn i hi, ← minSub_eq f a b hab hcont n hn i hi] at hflt
  have hnn := minSub_le_maxSub f a b hab hcont n hn i
  rwa [abs_of_nonneg (sub_nonneg_of_le hnn)] at hflt

/-! ## §3 — Dyadic doubling: the coarse extremum bounds both fine halves -/

theorem minSub_coarse_le_fine_even (f : Real → Real) (a b : Real) (hab : a ≤ b)
    (hcont : ∀ z : Real, a ≤ z → z ≤ b → ContinuousAt f z) (n : Nat) (hn : 0 < n) (i : Nat)
    (hi : i < n) (hn2 : 0 < 2 * n) :
    minSub f a b hab hcont n hn i ≤ minSub f a b hab hcont (2 * n) hn2 (2 * i) := by
  have hi2 : 2 * i < 2 * n := by omega
  have hmemFine := minSub_mem f a b hab hcont (2 * n) hn2 (2 * i) hi2
  have hleft : meshPoint a b n i
      ≤ Classical.choose (evt_exists_min f a b hab hcont (2 * n) hn2 (2 * i) hi2) := by
    rw [← meshPoint_double_even a b n i hn]; exact hmemFine.1
  have hright : Classical.choose (evt_exists_min f a b hab hcont (2 * n) hn2 (2 * i) hi2)
      ≤ meshPoint a b n (i + 1) :=
    le_trans hmemFine.2 (meshPoint_double_odd_le a b n i hab hn)
  have h := minSub_spec f a b hab hcont n hn i hi _ hleft hright
  rwa [← minSub_eq f a b hab hcont (2 * n) hn2 (2 * i) hi2] at h

theorem minSub_coarse_le_fine_odd (f : Real → Real) (a b : Real) (hab : a ≤ b)
    (hcont : ∀ z : Real, a ≤ z → z ≤ b → ContinuousAt f z) (n : Nat) (hn : 0 < n) (i : Nat)
    (hi : i < n) (hn2 : 0 < 2 * n) :
    minSub f a b hab hcont n hn i ≤ minSub f a b hab hcont (2 * n) hn2 (2 * i + 1) := by
  have hi2 : 2 * i + 1 < 2 * n := by omega
  have hmemFine := minSub_mem f a b hab hcont (2 * n) hn2 (2 * i + 1) hi2
  have hleft : meshPoint a b n i
      ≤ Classical.choose (evt_exists_min f a b hab hcont (2 * n) hn2 (2 * i + 1) hi2) :=
    le_trans (meshPoint_double_odd_ge a b n i hab hn) hmemFine.1
  have hright : Classical.choose (evt_exists_min f a b hab hcont (2 * n) hn2 (2 * i + 1) hi2)
      ≤ meshPoint a b n (i + 1) := by
    have heq : meshPoint a b (2 * n) (2 * i + 1 + 1) = meshPoint a b n (i + 1) := by
      rw [show 2 * i + 1 + 1 = 2 * (i + 1) from by omega]
      exact meshPoint_double_even a b n (i + 1) hn
    rw [← heq]; exact hmemFine.2
  have h := minSub_spec f a b hab hcont n hn i hi _ hleft hright
  rwa [← minSub_eq f a b hab hcont (2 * n) hn2 (2 * i + 1) hi2] at h

theorem fine_even_le_maxSub_coarse (f : Real → Real) (a b : Real) (hab : a ≤ b)
    (hcont : ∀ z : Real, a ≤ z → z ≤ b → ContinuousAt f z) (n : Nat) (hn : 0 < n) (i : Nat)
    (hi : i < n) (hn2 : 0 < 2 * n) :
    maxSub f a b hab hcont (2 * n) hn2 (2 * i) ≤ maxSub f a b hab hcont n hn i := by
  have hi2 : 2 * i < 2 * n := by omega
  have hmemFine := maxSub_mem f a b hab hcont (2 * n) hn2 (2 * i) hi2
  have hleft : meshPoint a b n i
      ≤ Classical.choose (evt_exists_max f a b hab hcont (2 * n) hn2 (2 * i) hi2) := by
    rw [← meshPoint_double_even a b n i hn]; exact hmemFine.1
  have hright : Classical.choose (evt_exists_max f a b hab hcont (2 * n) hn2 (2 * i) hi2)
      ≤ meshPoint a b n (i + 1) :=
    le_trans hmemFine.2 (meshPoint_double_odd_le a b n i hab hn)
  have h := maxSub_spec f a b hab hcont n hn i hi _ hleft hright
  rwa [← maxSub_eq f a b hab hcont (2 * n) hn2 (2 * i) hi2] at h

theorem fine_odd_le_maxSub_coarse (f : Real → Real) (a b : Real) (hab : a ≤ b)
    (hcont : ∀ z : Real, a ≤ z → z ≤ b → ContinuousAt f z) (n : Nat) (hn : 0 < n) (i : Nat)
    (hi : i < n) (hn2 : 0 < 2 * n) :
    maxSub f a b hab hcont (2 * n) hn2 (2 * i + 1) ≤ maxSub f a b hab hcont n hn i := by
  have hi2 : 2 * i + 1 < 2 * n := by omega
  have hmemFine := maxSub_mem f a b hab hcont (2 * n) hn2 (2 * i + 1) hi2
  have hleft : meshPoint a b n i
      ≤ Classical.choose (evt_exists_max f a b hab hcont (2 * n) hn2 (2 * i + 1) hi2) :=
    le_trans (meshPoint_double_odd_ge a b n i hab hn) hmemFine.1
  have hright : Classical.choose (evt_exists_max f a b hab hcont (2 * n) hn2 (2 * i + 1) hi2)
      ≤ meshPoint a b n (i + 1) := by
    have heq : meshPoint a b (2 * n) (2 * i + 1 + 1) = meshPoint a b n (i + 1) := by
      rw [show 2 * i + 1 + 1 = 2 * (i + 1) from by omega]
      exact meshPoint_double_even a b n (i + 1) hn
    rw [← heq]; exact hmemFine.2
  have h := maxSub_spec f a b hab hcont n hn i hi _ hleft hright
  rwa [← maxSub_eq f a b hab hcont (2 * n) hn2 (2 * i + 1) hi2] at h

private theorem half_mul_double_local (X : Real) : (1 + 1) * X = X + X := by mach_ring

theorem lowerSumCont_double_ge (f : Real → Real) (a b : Real) (hab : a ≤ b)
    (hcont : ∀ z : Real, a ≤ z → z ≤ b → ContinuousAt f z) (n : Nat) (hn : 0 < n)
    (hn2 : 0 < 2 * n) :
    lowerSumCont f a b hab hcont n hn ≤ lowerSumCont f a b hab hcont (2 * n) hn2 := by
  show partialSum (minSub f a b hab hcont n hn) n * meshWidth a b n
    ≤ partialSum (minSub f a b hab hcont (2 * n) hn2) (2 * n) * meshWidth a b (2 * n)
  rw [partialSum_pair_split (minSub f a b hab hcont (2 * n) hn2) n, meshWidth_double a b n hn]
  have hpair : ∀ i, i < n →
      (1 + 1) * minSub f a b hab hcont n hn i
        ≤ minSub f a b hab hcont (2 * n) hn2 (2 * i)
          + minSub f a b hab hcont (2 * n) hn2 (2 * i + 1) := by
    intro i hi
    rw [half_mul_double_local]
    exact add_le_add_both (minSub_coarse_le_fine_even f a b hab hcont n hn i hi hn2)
      (minSub_coarse_le_fine_odd f a b hab hcont n hn i hi hn2)
  have hsum_le := partialSum_le_of_termwise_le n hpair
  rw [partialSum_const_mul (1 + 1) (minSub f a b hab hcont n hn) n] at hsum_le
  have hcancel :
      ((1 + 1) * partialSum (minSub f a b hab hcont n hn) n) * (meshWidth a b n / (1 + 1))
      = partialSum (minSub f a b hab hcont n hn) n * meshWidth a b n := by
    rw [div_def (meshWidth a b n) (1 + 1) two_ne_zero]
    rw [show (1 + 1) * partialSum (minSub f a b hab hcont n hn) n
          * (meshWidth a b n * (1 / (1 + 1)))
        = partialSum (minSub f a b hab hcont n hn) n * meshWidth a b n
          * ((1 + 1) * (1 / (1 + 1))) from by mach_ring]
    rw [mul_inv (1 + 1) two_ne_zero, mul_one_ax]
  rw [← hcancel]
  exact mul_le_mul_of_nonneg_right hsum_le (div_nonneg (meshWidth_nonneg hab n) (le_of_lt two_pos))

theorem upperSumCont_double_le (f : Real → Real) (a b : Real) (hab : a ≤ b)
    (hcont : ∀ z : Real, a ≤ z → z ≤ b → ContinuousAt f z) (n : Nat) (hn : 0 < n)
    (hn2 : 0 < 2 * n) :
    upperSumCont f a b hab hcont (2 * n) hn2 ≤ upperSumCont f a b hab hcont n hn := by
  show partialSum (maxSub f a b hab hcont (2 * n) hn2) (2 * n) * meshWidth a b (2 * n)
    ≤ partialSum (maxSub f a b hab hcont n hn) n * meshWidth a b n
  rw [partialSum_pair_split (maxSub f a b hab hcont (2 * n) hn2) n, meshWidth_double a b n hn]
  have hpair : ∀ i, i < n →
      maxSub f a b hab hcont (2 * n) hn2 (2 * i) + maxSub f a b hab hcont (2 * n) hn2 (2 * i + 1)
        ≤ (1 + 1) * maxSub f a b hab hcont n hn i := by
    intro i hi
    rw [half_mul_double_local]
    exact add_le_add_both (fine_even_le_maxSub_coarse f a b hab hcont n hn i hi hn2)
      (fine_odd_le_maxSub_coarse f a b hab hcont n hn i hi hn2)
  have hsum_le := partialSum_le_of_termwise_le n hpair
  rw [partialSum_const_mul (1 + 1) (maxSub f a b hab hcont n hn) n] at hsum_le
  have hcancel :
      ((1 + 1) * partialSum (maxSub f a b hab hcont n hn) n) * (meshWidth a b n / (1 + 1))
      = partialSum (maxSub f a b hab hcont n hn) n * meshWidth a b n := by
    rw [div_def (meshWidth a b n) (1 + 1) two_ne_zero]
    rw [show (1 + 1) * partialSum (maxSub f a b hab hcont n hn) n
          * (meshWidth a b n * (1 / (1 + 1)))
        = partialSum (maxSub f a b hab hcont n hn) n * meshWidth a b n
          * ((1 + 1) * (1 / (1 + 1))) from by mach_ring]
    rw [mul_inv (1 + 1) two_ne_zero, mul_one_ax]
  rw [← hcancel]
  exact mul_le_mul_of_nonneg_right hsum_le (div_nonneg (meshWidth_nonneg hab n) (le_of_lt two_pos))

/-! ## §4 — Existence, via `sup_exists` on the dyadic family + `archimedean` -/

theorem lowerSumCont_dyadic_mono (f : Real → Real) (a b : Real) (hab : a ≤ b)
    (hcont : ∀ z : Real, a ≤ z → z ≤ b → ContinuousAt f z) : ∀ k j (hk : 0 < 2 ^ k),
    lowerSumCont f a b hab hcont (2 ^ k) hk
      ≤ lowerSumCont f a b hab hcont (2 ^ (k + j)) (two_pow_pos (k + j))
  | k, 0, hk => le_refl _
  | k, j + 1, hk => by
      have ih := lowerSumCont_dyadic_mono f a b hab hcont k j hk
      have hstep : lowerSumCont f a b hab hcont (2 ^ (k + j)) (two_pow_pos (k + j))
          ≤ lowerSumCont f a b hab hcont (2 ^ (k + j + 1)) (two_pow_pos (k + j + 1)) := by
        have heq : (2:Nat) ^ (k + j + 1) = 2 * 2 ^ (k + j) := two_pow_succ (k + j)
        have hgoal := lowerSumCont_double_ge f a b hab hcont (2 ^ (k + j)) (two_pow_pos (k + j))
          (heq ▸ two_pow_pos (k + j + 1))
        simpa [← heq] using hgoal
      exact le_trans ih hstep

theorem upperSumCont_dyadic_anti (f : Real → Real) (a b : Real) (hab : a ≤ b)
    (hcont : ∀ z : Real, a ≤ z → z ≤ b → ContinuousAt f z) : ∀ k j (hk : 0 < 2 ^ k),
    upperSumCont f a b hab hcont (2 ^ (k + j)) (two_pow_pos (k + j))
      ≤ upperSumCont f a b hab hcont (2 ^ k) hk
  | k, 0, hk => le_refl _
  | k, j + 1, hk => by
      have ih := upperSumCont_dyadic_anti f a b hab hcont k j hk
      have hstep : upperSumCont f a b hab hcont (2 ^ (k + j + 1)) (two_pow_pos (k + j + 1))
          ≤ upperSumCont f a b hab hcont (2 ^ (k + j)) (two_pow_pos (k + j)) := by
        have heq : (2:Nat) ^ (k + j + 1) = 2 * 2 ^ (k + j) := two_pow_succ (k + j)
        have hgoal := upperSumCont_double_le f a b hab hcont (2 ^ (k + j)) (two_pow_pos (k + j))
          (heq ▸ two_pow_pos (k + j + 1))
        simpa [← heq] using hgoal
      exact le_trans hstep ih

theorem lowerSumCont_le_upperSumCont_cross (f : Real → Real) (a b : Real) (hab : a ≤ b)
    (hcont : ∀ z : Real, a ≤ z → z ≤ b → ContinuousAt f z) (j k : Nat) :
    lowerSumCont f a b hab hcont (2 ^ j) (two_pow_pos j)
      ≤ upperSumCont f a b hab hcont (2 ^ k) (two_pow_pos k) := by
  rcases Nat.le_total j k with hjk | hkj
  · obtain ⟨d, hd⟩ := Nat.le.dest hjk
    have h1 := lowerSumCont_dyadic_mono f a b hab hcont j d (two_pow_pos j)
    rw [hd] at h1
    exact le_trans h1 (lowerSumCont_le_upperSumCont f a b hab hcont (2 ^ k) (two_pow_pos k))
  · obtain ⟨d, hd⟩ := Nat.le.dest hkj
    have h2 := upperSumCont_dyadic_anti f a b hab hcont k d (two_pow_pos k)
    rw [hd] at h2
    exact le_trans (lowerSumCont_le_upperSumCont f a b hab hcont (2 ^ j) (two_pow_pos j)) h2

private theorem sub_mul_common (x y w : Real) : x * w - y * w = (x - y) * w := by
  mach_mpoly [x, y, w]

private theorem partialSum_const (c : Real) : ∀ n, partialSum (fun _ => c) n = natCast n * c
  | 0 => by show (0 : Real) = natCast 0 * c; rw [natCast_zero, zero_mul]
  | k + 1 => by
      show partialSum (fun _ => c) k + c = natCast (k + 1) * c
      rw [partialSum_const c k, natCast_succ]
      mach_mpoly [natCast k, c]

theorem natCast_mul_meshWidth (a b : Real) (n : Nat) (hn : 0 < n) :
    natCast n * meshWidth a b n = b - a := by
  show natCast n * ((b - a) / natCast n) = b - a
  exact mul_div_cancel_left (natCast_ne_zero hn)

/-- **Continuous functions are Riemann integrable.** There is a value `I` sandwiched between every
dyadic lower and upper sum, with the gap shrinking below any `ε > 0`. -/
theorem continuous_riemann_integrable (f : Real → Real) (a b : Real) (hab : a ≤ b)
    (hcont : ∀ z : Real, a ≤ z → z ≤ b → ContinuousAt f z) :
    ∃ I : Real,
      (∀ k, lowerSumCont f a b hab hcont (2 ^ k) (two_pow_pos k) ≤ I ∧
        I ≤ upperSumCont f a b hab hcont (2 ^ k) (two_pow_pos k)) ∧
      (∀ ε : Real, 0 < ε → ∃ k, upperSumCont f a b hab hcont (2 ^ k) (two_pow_pos k)
        - lowerSumCont f a b hab hcont (2 ^ k) (two_pow_pos k) < ε) := by
  have hne : ∃ x, ∃ k, x = lowerSumCont f a b hab hcont (2 ^ k) (two_pow_pos k) :=
    ⟨lowerSumCont f a b hab hcont (2 ^ 0) (two_pow_pos 0), 0, rfl⟩
  have hbd : BoundedAbove (fun x => ∃ k, x = lowerSumCont f a b hab hcont (2 ^ k) (two_pow_pos k)) :=
    ⟨upperSumCont f a b hab hcont (2 ^ 0) (two_pow_pos 0), fun x hx => by
      obtain ⟨k, hk⟩ := hx; rw [hk]; exact lowerSumCont_le_upperSumCont_cross f a b hab hcont k 0⟩
  obtain ⟨I, hIub, hIlub⟩ :=
    sup_exists (fun x => ∃ k, x = lowerSumCont f a b hab hcont (2 ^ k) (two_pow_pos k)) hne hbd
  refine ⟨I, fun k => ⟨hIub _ ⟨k, rfl⟩, ?_⟩, ?_⟩
  · apply hIlub
    intro x hx
    obtain ⟨j, hj⟩ := hx
    rw [hj]
    exact lowerSumCont_le_upperSumCont_cross f a b hab hcont j k
  · intro ε hε
    have hab1pos : 0 < (b - a) + 1 := by
      have h1 : 0 ≤ b - a := sub_nonneg_of_le hab
      have h2 := add_le_add_both h1 (le_refl (1:Real))
      rw [zero_add] at h2
      exact lt_of_lt_of_le one_pos h2
    have hε' : 0 < ε / ((b - a) + 1) := div_pos_of_pos_pos hε hab1pos
    obtain ⟨δ, hδpos, hδ⟩ := heine_cantor_uniform_continuity hab hcont (ε / ((b - a) + 1)) hε'
    obtain ⟨N, hN⟩ := archimedean ((b - a) / δ)
    have hNpos : 0 < N := by
      rcases Nat.eq_zero_or_pos N with h0 | hpos
      · exfalso
        have hnn : 0 ≤ (b - a) / δ := div_nonneg (sub_nonneg_of_le hab) (le_of_lt hδpos)
        rw [h0, natCast_zero] at hN
        exact lt_irrefl_ax 0 (lt_of_le_of_lt hnn hN)
      · exact hpos
    have hNle2N : N ≤ 2 ^ N := nat_le_two_pow N
    have h2Npos : 0 < natCast (2 ^ N) := natCast_pos (two_pow_pos N)
    have hNcast : natCast N ≤ natCast (2 ^ N) := natCast_le_of_nat_le hNle2N
    have hwidth : meshWidth a b (2 ^ N) < δ := by
      show (b - a) / natCast (2 ^ N) < δ
      have hstep1 : (b - a) / natCast (2 ^ N) ≤ (b - a) / natCast N := by
        apply div_le_div_pos (sub_nonneg_of_le hab) (le_refl _) (natCast_pos hNpos) hNcast
      have hstep2 : (b - a) / natCast N < δ := by
        have hcross : (b - a) < δ * natCast N := by
          have hmul := mul_lt_mul_of_pos_right hN hδpos
          rw [div_mul_cancel (ne_of_gt hδpos)] at hmul
          rwa [mul_comm (natCast N) δ] at hmul
        exact div_lt_of_lt_mul hcross (natCast_pos hNpos)
      exact lt_of_le_of_lt hstep1 hstep2
    refine ⟨N, ?_⟩
    have hgapbound : ∀ i, maxSub f a b hab hcont (2 ^ N) (two_pow_pos N) i
        - minSub f a b hab hcont (2 ^ N) (two_pow_pos N) i ≤ ε / ((b - a) + 1) := by
      intro i
      by_cases hi : i < 2 ^ N
      · exact le_of_lt (maxSub_sub_minSub_lt f a b hab hcont (2 ^ N) (two_pow_pos N) i hi hδ hwidth)
      · unfold maxSub minSub
        rw [dif_neg hi, dif_neg hi, sub_self]
        exact le_of_lt hε'
    have hgapsum : partialSum (fun i => maxSub f a b hab hcont (2 ^ N) (two_pow_pos N) i
        - minSub f a b hab hcont (2 ^ N) (two_pow_pos N) i) (2 ^ N)
        ≤ partialSum (fun _ => ε / ((b - a) + 1)) (2 ^ N) :=
      partialSum_le_of_le hgapbound (2 ^ N)
    rw [partialSum_const (ε / ((b - a) + 1))] at hgapsum
    show partialSum (maxSub f a b hab hcont (2 ^ N) (two_pow_pos N)) (2 ^ N) * meshWidth a b (2 ^ N)
      - partialSum (minSub f a b hab hcont (2 ^ N) (two_pow_pos N)) (2 ^ N) * meshWidth a b (2 ^ N)
      < ε
    rw [sub_mul_common]
    rw [show partialSum (maxSub f a b hab hcont (2 ^ N) (two_pow_pos N)) (2 ^ N)
          - partialSum (minSub f a b hab hcont (2 ^ N) (two_pow_pos N)) (2 ^ N)
        = partialSum (fun i => maxSub f a b hab hcont (2 ^ N) (two_pow_pos N) i
            - minSub f a b hab hcont (2 ^ N) (two_pow_pos N) i) (2 ^ N) from
          (partialSum_sub _ _ (2 ^ N)).symm]
    have hfinal := mul_le_mul_of_nonneg_right hgapsum (meshWidth_nonneg hab (2 ^ N))
    have heqwidth : natCast (2 ^ N) * (ε / ((b - a) + 1)) * meshWidth a b (2 ^ N)
        = ε / ((b - a) + 1) * (natCast (2 ^ N) * meshWidth a b (2 ^ N)) := by
      mach_ring
    rw [heqwidth, natCast_mul_meshWidth a b (2 ^ N) (two_pow_pos N)] at hfinal
    have hlast : ε / ((b - a) + 1) * (b - a) < ε := by
      have h1 : (b - a) < (b - a) + 1 := by
        have := add_lt_add_left one_pos (b - a)
        rwa [add_zero] at this
      have h2 : (b - a) * (ε / ((b - a) + 1)) < ((b - a) + 1) * (ε / ((b - a) + 1)) :=
        mul_lt_mul_of_pos_right h1 hε'
      rw [mul_comm (b - a) (ε / ((b - a) + 1)), mul_comm ((b - a) + 1) (ε / ((b - a) + 1))] at h2
      rwa [div_mul_cancel (ne_of_gt hab1pos)] at h2
    exact lt_of_le_of_lt hfinal hlast

end Real
end MachLib
