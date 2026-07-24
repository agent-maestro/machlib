/-
`RiemannIntegralRefine.lean` — arbitrary-factor partition refinement for the continuous-integrand
Riemann integral (`RiemannIntegralContinuous.lean`).

`lowerSumCont_double_ge`/`upperSumCont_double_le` only relate an `n`-partition to its `2n`
refinement. That is enough to build the dyadic family used by `continuous_riemann_integrable`,
but it is NOT enough to compare `[0,a]` to `[0,b]` for two different real endpoints `a ≤ b`: their
uniform partitions have different mesh widths (`a/n` vs `b/n`) that never align except at the
endpoints. The fix is to generalize "refine by 2" to "refine by an arbitrary factor `m`", which
lets any two partition counts `n₁, n₂` be compared via the common refinement `n₁ * n₂`. This file
builds that generalization and packages it as `sandwich_any_n`: the dyadic-only sandwich from
`continuous_riemann_integrable` actually holds at every partition size, not just powers of 2.

Downstream motivation: the √π project's disk/square sandwich (Stage 4/5) needs to compare
`∫₀ᵃ f` to `∫₀ᵇ f` for real `a ≤ b`, which is exactly this kind of arbitrary-mesh comparison.
-/
import MachLib.RiemannIntegralContinuous
import MachLib.WeierstrassTermByTerm

namespace MachLib
namespace Real

/-! ## §1 — Block decomposition of `partialSum` -/

/-- Splitting a `partialSum` at an arbitrary point `p`. -/
theorem partialSum_add (g : Nat → Real) (p : Nat) : ∀ q : Nat,
    partialSum g (p + q) = partialSum g p + partialSum (fun j => g (p + j)) q
  | 0 => by show partialSum g p = partialSum g p + 0; mach_mpoly [partialSum g p]
  | k + 1 => by
      show partialSum g (p + k + 1) = partialSum g p + (partialSum (fun j => g (p + j)) k + g (p + k))
      rw [show partialSum g (p + k + 1) = partialSum g (p + k) + g (p + k) from partialSum_succ g (p + k)]
      rw [partialSum_add g p k]
      exact add_assoc _ _ _

/-- **Block-split**: summing `m * n` terms equals summing `n` consecutive blocks of `m`. -/
theorem partialSum_block_split (g : Nat → Real) (m : Nat) : ∀ n : Nat,
    partialSum g (m * n) = partialSum (fun i => partialSum (fun j => g (m * i + j)) m) n
  | 0 => by show partialSum g (m * 0) = 0; rw [Nat.mul_zero]; rfl
  | k + 1 => by
      show partialSum g (m * (k + 1)) = partialSum (fun i => partialSum (fun j => g (m * i + j)) m) k
        + partialSum (fun j => g (m * k + j)) m
      rw [Nat.mul_succ, partialSum_add g (m * k) m, partialSum_block_split g m k]

/-- Commuted-count variant: matches `n * m`-shaped goals (`n` coarse blocks of size `m`). -/
theorem partialSum_block_split' (g : Nat → Real) (n m : Nat) :
    partialSum g (n * m) = partialSum (fun i => partialSum (fun j => g (m * i + j)) m) n := by
  rw [Nat.mul_comm n m]; exact partialSum_block_split g m n

/-! ## §2 — Fine mesh points lie inside their parent coarse subinterval -/

private theorem natCast_mul_add_local (m i j : Nat) :
    natCast (m * i + j) = natCast m * natCast i + natCast j := by
  rw [natCast_add (m * i) j, natCast_mul m i]

private theorem natCast_one_local : natCast 1 = 1 := by
  rw [natCast_succ, natCast_zero]; exact zero_add 1

private theorem one_div_mul_refine {p q : Real} (hp : p ≠ 0) (hq : q ≠ 0) :
    1 / p * (1 / q) = 1 / (p * q) := by
  apply mul_left_cancel (mul_ne_zero hp hq)
  rw [show (p * q) * (1 / p * (1 / q)) = (p * (1 / p)) * (q * (1 / q))
      from by mach_mpoly [p, q, 1 / p, 1 / q],
    mul_inv p hp, mul_inv q hq, mul_one_ax, mul_inv (p * q) (mul_ne_zero hp hq)]

/-- `n` fine-widths of the `n*m`-partition equal one coarse-width of the `n`-partition. -/
theorem meshWidth_scale (a b : Real) (n m : Nat) (hn : 0 < n) (hm : 0 < m) :
    meshWidth a b n = natCast m * meshWidth a b (n * m) := by
  show (b - a) / natCast n = natCast m * ((b - a) / natCast (n * m))
  rw [natCast_mul n m]
  have hnne : natCast n ≠ 0 := ne_of_gt (natCast_pos hn)
  have hmne : natCast m ≠ 0 := ne_of_gt (natCast_pos hm)
  rw [div_def (b - a) (natCast n) hnne, div_def (b - a) (natCast n * natCast m) (mul_ne_zero hnne hmne)]
  rw [← one_div_mul_refine hnne hmne]
  rw [show natCast m * ((b - a) * (1 / natCast n * (1 / natCast m)))
      = (b - a) * (1 / natCast n) * (natCast m * (1 / natCast m))
      from by mach_mpoly [natCast m, b - a, 1 / natCast n, 1 / natCast m]]
  rw [mul_inv (natCast m) hmne, mul_one_ax]

/-- The fine mesh point `m*i+j` sits `j` fine-widths past the coarse mesh point `i`. -/
theorem meshPoint_block_eq (a b : Real) (n m i j : Nat) (hn : 0 < n) (hm : 0 < m) :
    meshPoint a b (n * m) (m * i + j) = meshPoint a b n i + natCast j * meshWidth a b (n * m) := by
  show a + natCast (m * i + j) * meshWidth a b (n * m) = a + natCast i * meshWidth a b n
    + natCast j * meshWidth a b (n * m)
  rw [natCast_mul_add_local m i j, meshWidth_scale a b n m hn hm]
  mach_mpoly [a, natCast i, natCast j, meshWidth a b (n * m), natCast m]

theorem meshPoint_block_ge (a b : Real) (n m i j : Nat) (hab : a ≤ b) (hn : 0 < n) (hm : 0 < m) :
    meshPoint a b n i ≤ meshPoint a b (n * m) (m * i + j) := by
  rw [meshPoint_block_eq a b n m i j hn hm]
  have h1 : (0:Real) ≤ natCast j * meshWidth a b (n * m) :=
    mul_nonneg (natCast_nonneg j) (meshWidth_nonneg hab (n * m))
  have h2 := add_le_add_both (le_refl (meshPoint a b n i)) h1
  rwa [show meshPoint a b n i + 0 = meshPoint a b n i from by mach_mpoly [meshPoint a b n i]] at h2

private theorem meshPoint_succ_eq_refine (a b : Real) (n i : Nat) :
    meshPoint a b n i + meshWidth a b n = meshPoint a b n (i + 1) := by
  show a + natCast i * meshWidth a b n + meshWidth a b n = a + natCast (i + 1) * meshWidth a b n
  rw [natCast_add i 1, natCast_one_local]
  mach_mpoly [a, natCast i, meshWidth a b n]

theorem meshPoint_block_le (a b : Real) (n m i j : Nat) (hab : a ≤ b) (hn : 0 < n) (hm : 0 < m)
    (hj : j < m) :
    meshPoint a b (n * m) (m * i + j + 1) ≤ meshPoint a b n (i + 1) := by
  have hstep : m * i + j + 1 = m * i + (j + 1) := by omega
  rw [hstep, meshPoint_block_eq a b n m i (j + 1) hn hm]
  have hjm : natCast (j + 1) ≤ natCast m := natCast_le_of_nat_le (by omega)
  have h1 : natCast (j + 1) * meshWidth a b (n * m) ≤ natCast m * meshWidth a b (n * m) :=
    mul_le_mul_of_nonneg_right hjm (meshWidth_nonneg hab (n * m))
  have h2 := add_le_add_both (le_refl (meshPoint a b n i)) h1
  rw [← meshWidth_scale a b n m hn hm] at h2
  rwa [meshPoint_succ_eq_refine a b n i] at h2

/-! ## §3 — The coarse extremum bounds every fine extremum inside its subinterval -/

private theorem block_index_lt (n m i j : Nat) (hi : i < n) (hj : j < m) : m * i + j < n * m := by
  have h1 : m * (i + 1) ≤ m * n := Nat.mul_le_mul (Nat.le_refl m) (by omega)
  rw [Nat.mul_add, Nat.mul_one] at h1
  rw [Nat.mul_comm n m]
  omega

theorem minSub_coarse_le_fine_block (f : Real → Real) (a b : Real) (hab : a ≤ b)
    (hcont : ∀ z : Real, a ≤ z → z ≤ b → ContinuousAt f z) (n : Nat) (hn : 0 < n) (i : Nat)
    (hi : i < n) (m : Nat) (hm : 0 < m) (j : Nat) (hj : j < m) (hnm : 0 < n * m) :
    minSub f a b hab hcont n hn i ≤ minSub f a b hab hcont (n * m) hnm (m * i + j) := by
  have hij := block_index_lt n m i j hi hj
  have hmemFine := minSub_mem f a b hab hcont (n * m) hnm (m * i + j) hij
  have hleft : meshPoint a b n i
      ≤ Classical.choose (evt_exists_min f a b hab hcont (n * m) hnm (m * i + j) hij) :=
    le_trans (meshPoint_block_ge a b n m i j hab hn hm) hmemFine.1
  have hright : Classical.choose (evt_exists_min f a b hab hcont (n * m) hnm (m * i + j) hij)
      ≤ meshPoint a b n (i + 1) :=
    le_trans hmemFine.2 (meshPoint_block_le a b n m i j hab hn hm hj)
  have h := minSub_spec f a b hab hcont n hn i hi _ hleft hright
  rwa [← minSub_eq f a b hab hcont (n * m) hnm (m * i + j) hij] at h

theorem fine_block_le_maxSub_coarse (f : Real → Real) (a b : Real) (hab : a ≤ b)
    (hcont : ∀ z : Real, a ≤ z → z ≤ b → ContinuousAt f z) (n : Nat) (hn : 0 < n) (i : Nat)
    (hi : i < n) (m : Nat) (hm : 0 < m) (j : Nat) (hj : j < m) (hnm : 0 < n * m) :
    maxSub f a b hab hcont (n * m) hnm (m * i + j) ≤ maxSub f a b hab hcont n hn i := by
  have hij := block_index_lt n m i j hi hj
  have hmemFine := maxSub_mem f a b hab hcont (n * m) hnm (m * i + j) hij
  have hleft : meshPoint a b n i
      ≤ Classical.choose (evt_exists_max f a b hab hcont (n * m) hnm (m * i + j) hij) :=
    le_trans (meshPoint_block_ge a b n m i j hab hn hm) hmemFine.1
  have hright : Classical.choose (evt_exists_max f a b hab hcont (n * m) hnm (m * i + j) hij)
      ≤ meshPoint a b n (i + 1) :=
    le_trans hmemFine.2 (meshPoint_block_le a b n m i j hab hn hm hj)
  have h := maxSub_spec f a b hab hcont n hn i hi _ hleft hright
  rwa [← maxSub_eq f a b hab hcont (n * m) hnm (m * i + j) hij] at h

/-! ## §4 — Refining a Darboux sum by an arbitrary factor `m` -/

private theorem partialSum_const_refine (c : Real) : ∀ n : Nat, partialSum (fun _ => c) n = natCast n * c
  | 0 => by show (0:Real) = natCast 0 * c; rw [natCast_zero]; mach_mpoly [c]
  | k + 1 => by
      show partialSum (fun _ => c) k + c = natCast (k + 1) * c
      rw [partialSum_const_refine c k, natCast_add k 1, natCast_one_local]
      mach_mpoly [natCast k, c]

theorem lowerSumCont_refine_ge (f : Real → Real) (a b : Real) (hab : a ≤ b)
    (hcont : ∀ z : Real, a ≤ z → z ≤ b → ContinuousAt f z) (n : Nat) (hn : 0 < n) (m : Nat)
    (hm : 0 < m) (hnm : 0 < n * m) :
    lowerSumCont f a b hab hcont n hn ≤ lowerSumCont f a b hab hcont (n * m) hnm := by
  show partialSum (minSub f a b hab hcont n hn) n * meshWidth a b n
    ≤ partialSum (minSub f a b hab hcont (n * m) hnm) (n * m) * meshWidth a b (n * m)
  rw [partialSum_block_split' (minSub f a b hab hcont (n * m) hnm) n m, meshWidth_scale a b n m hn hm]
  rw [show partialSum (minSub f a b hab hcont n hn) n * (natCast m * meshWidth a b (n * m))
      = (natCast m * partialSum (minSub f a b hab hcont n hn) n) * meshWidth a b (n * m)
      from by mach_mpoly [partialSum (minSub f a b hab hcont n hn) n, natCast m, meshWidth a b (n * m)]]
  have hblock : ∀ i, i < n →
      natCast m * minSub f a b hab hcont n hn i
        ≤ partialSum (fun j => minSub f a b hab hcont (n * m) hnm (m * i + j)) m := by
    intro i hi
    rw [← partialSum_const_refine (minSub f a b hab hcont n hn i) m]
    apply partialSum_le_of_termwise_le
    intro j hj
    exact minSub_coarse_le_fine_block f a b hab hcont n hn i hi m hm j hj hnm
  have hsum_le := partialSum_le_of_termwise_le n hblock
  rw [partialSum_const_mul (natCast m) (minSub f a b hab hcont n hn) n] at hsum_le
  exact mul_le_mul_of_nonneg_right hsum_le (meshWidth_nonneg hab (n * m))

theorem upperSumCont_refine_le (f : Real → Real) (a b : Real) (hab : a ≤ b)
    (hcont : ∀ z : Real, a ≤ z → z ≤ b → ContinuousAt f z) (n : Nat) (hn : 0 < n) (m : Nat)
    (hm : 0 < m) (hnm : 0 < n * m) :
    upperSumCont f a b hab hcont (n * m) hnm ≤ upperSumCont f a b hab hcont n hn := by
  show partialSum (maxSub f a b hab hcont (n * m) hnm) (n * m) * meshWidth a b (n * m)
    ≤ partialSum (maxSub f a b hab hcont n hn) n * meshWidth a b n
  rw [partialSum_block_split' (maxSub f a b hab hcont (n * m) hnm) n m, meshWidth_scale a b n m hn hm]
  rw [show partialSum (maxSub f a b hab hcont n hn) n * (natCast m * meshWidth a b (n * m))
      = (natCast m * partialSum (maxSub f a b hab hcont n hn) n) * meshWidth a b (n * m)
      from by mach_mpoly [partialSum (maxSub f a b hab hcont n hn) n, natCast m, meshWidth a b (n * m)]]
  have hblock : ∀ i, i < n →
      partialSum (fun j => maxSub f a b hab hcont (n * m) hnm (m * i + j)) m
        ≤ natCast m * maxSub f a b hab hcont n hn i := by
    intro i hi
    rw [← partialSum_const_refine (maxSub f a b hab hcont n hn i) m]
    apply partialSum_le_of_termwise_le
    intro j hj
    exact fine_block_le_maxSub_coarse f a b hab hcont n hn i hi m hm j hj hnm
  have hsum_le := partialSum_le_of_termwise_le n hblock
  rw [partialSum_const_mul (natCast m) (maxSub f a b hab hcont n hn) n] at hsum_le
  exact mul_le_mul_of_nonneg_right hsum_le (meshWidth_nonneg hab (n * m))

/-! ## §5 — `sandwich_any_n`: the dyadic-only sandwich extends to every partition size -/

private theorem add_sub_cancel_refine (X Y : Real) : Y + (X - Y) = X := by mach_mpoly [X, Y]

/-- `lowerSumCont`/`upperSumCont` at a count only depend on its *value*, not on how the
positivity witness or the count expression was written (proof irrelevance handles the witness;
this handles two syntactically different but equal count expressions, e.g. `n*2^k` vs `2^k*n`). -/
private theorem lowerSumCont_congr (f : Real → Real) (a b : Real) (hab : a ≤ b)
    (hcont : ∀ z : Real, a ≤ z → z ≤ b → ContinuousAt f z) :
    ∀ {N1 N2 : Nat}, N1 = N2 → ∀ (h1 : 0 < N1) (h2 : 0 < N2),
      lowerSumCont f a b hab hcont N1 h1 = lowerSumCont f a b hab hcont N2 h2
  | _, _, rfl, _, _ => rfl

private theorem upperSumCont_congr (f : Real → Real) (a b : Real) (hab : a ≤ b)
    (hcont : ∀ z : Real, a ≤ z → z ≤ b → ContinuousAt f z) :
    ∀ {N1 N2 : Nat}, N1 = N2 → ∀ (h1 : 0 < N1) (h2 : 0 < N2),
      upperSumCont f a b hab hcont N1 h1 = upperSumCont f a b hab hcont N2 h2
  | _, _, rfl, _, _ => rfl

theorem lowerSumCont_le_any (f : Real → Real) (a b : Real) (hab : a ≤ b)
    (hcont : ∀ z : Real, a ≤ z → z ≤ b → ContinuousAt f z) (I : Real)
    (hIlow : ∀ k, lowerSumCont f a b hab hcont (2 ^ k) (two_pow_pos k) ≤ I)
    (hgap : ∀ ε : Real, 0 < ε → ∃ k, upperSumCont f a b hab hcont (2 ^ k) (two_pow_pos k)
      - lowerSumCont f a b hab hcont (2 ^ k) (two_pow_pos k) < ε)
    (n : Nat) (hn : 0 < n) :
    lowerSumCont f a b hab hcont n hn ≤ I := by
  apply le_of_forall_pos_lt_add
  intro ε hε
  obtain ⟨k, hk⟩ := hgap ε hε
  have hnm : 0 < n * 2 ^ k := Nat.mul_pos hn (two_pow_pos k)
  have hnm2 : 0 < 2 ^ k * n := Nat.mul_pos (two_pow_pos k) hn
  have hcomm : n * 2 ^ k = 2 ^ k * n := Nat.mul_comm n (2 ^ k)
  have hstep1 : lowerSumCont f a b hab hcont n hn ≤ lowerSumCont f a b hab hcont (n * 2 ^ k) hnm :=
    lowerSumCont_refine_ge f a b hab hcont n hn (2 ^ k) (two_pow_pos k) hnm
  have e1 : lowerSumCont f a b hab hcont (n * 2 ^ k) hnm = lowerSumCont f a b hab hcont (2 ^ k * n) hnm2 :=
    lowerSumCont_congr f a b hab hcont hcomm hnm hnm2
  have hstep2 : lowerSumCont f a b hab hcont (2 ^ k * n) hnm2
      ≤ upperSumCont f a b hab hcont (2 ^ k * n) hnm2 :=
    lowerSumCont_le_upperSumCont f a b hab hcont (2 ^ k * n) hnm2
  have hstep3 : upperSumCont f a b hab hcont (2 ^ k * n) hnm2
      ≤ upperSumCont f a b hab hcont (2 ^ k) (two_pow_pos k) :=
    upperSumCont_refine_le f a b hab hcont (2 ^ k) (two_pow_pos k) n hn hnm2
  have hchain : lowerSumCont f a b hab hcont n hn ≤ upperSumCont f a b hab hcont (2 ^ k) (two_pow_pos k) :=
    le_trans hstep1 (le_trans (le_of_eq e1) (le_trans hstep2 hstep3))
  have hgt : upperSumCont f a b hab hcont (2 ^ k) (two_pow_pos k)
      < lowerSumCont f a b hab hcont (2 ^ k) (two_pow_pos k) + ε := by
    have h := add_lt_add_left hk (lowerSumCont f a b hab hcont (2 ^ k) (two_pow_pos k))
    rwa [add_sub_cancel_refine (upperSumCont f a b hab hcont (2 ^ k) (two_pow_pos k))
      (lowerSumCont f a b hab hcont (2 ^ k) (two_pow_pos k))] at h
  have hfinal : upperSumCont f a b hab hcont (2 ^ k) (two_pow_pos k) < I + ε :=
    lt_of_lt_of_le hgt (add_le_add_both (hIlow k) (le_refl ε))
  exact lt_of_le_of_lt hchain hfinal

theorem le_upperSumCont_any (f : Real → Real) (a b : Real) (hab : a ≤ b)
    (hcont : ∀ z : Real, a ≤ z → z ≤ b → ContinuousAt f z) (I : Real)
    (hIup : ∀ k, I ≤ upperSumCont f a b hab hcont (2 ^ k) (two_pow_pos k))
    (hgap : ∀ ε : Real, 0 < ε → ∃ k, upperSumCont f a b hab hcont (2 ^ k) (two_pow_pos k)
      - lowerSumCont f a b hab hcont (2 ^ k) (two_pow_pos k) < ε)
    (n : Nat) (hn : 0 < n) :
    I ≤ upperSumCont f a b hab hcont n hn := by
  apply le_of_forall_pos_lt_add
  intro ε hε
  obtain ⟨k, hk⟩ := hgap ε hε
  have hnm : 0 < n * 2 ^ k := Nat.mul_pos hn (two_pow_pos k)
  have hnm2 : 0 < 2 ^ k * n := Nat.mul_pos (two_pow_pos k) hn
  have hcomm : n * 2 ^ k = 2 ^ k * n := Nat.mul_comm n (2 ^ k)
  have hstep1 : upperSumCont f a b hab hcont (n * 2 ^ k) hnm ≤ upperSumCont f a b hab hcont n hn :=
    upperSumCont_refine_le f a b hab hcont n hn (2 ^ k) (two_pow_pos k) hnm
  have e1 : upperSumCont f a b hab hcont (n * 2 ^ k) hnm = upperSumCont f a b hab hcont (2 ^ k * n) hnm2 :=
    upperSumCont_congr f a b hab hcont hcomm hnm hnm2
  have hstep2 : lowerSumCont f a b hab hcont (2 ^ k * n) hnm2
      ≤ upperSumCont f a b hab hcont (2 ^ k * n) hnm2 :=
    lowerSumCont_le_upperSumCont f a b hab hcont (2 ^ k * n) hnm2
  have hstep0 : lowerSumCont f a b hab hcont (2 ^ k) (two_pow_pos k)
      ≤ lowerSumCont f a b hab hcont (2 ^ k * n) hnm2 :=
    lowerSumCont_refine_ge f a b hab hcont (2 ^ k) (two_pow_pos k) n hn hnm2
  have hstep1' : upperSumCont f a b hab hcont (2 ^ k * n) hnm2 ≤ upperSumCont f a b hab hcont n hn :=
    le_trans (le_of_eq (Eq.symm e1)) hstep1
  have hchain : lowerSumCont f a b hab hcont (2 ^ k) (two_pow_pos k)
      ≤ upperSumCont f a b hab hcont n hn :=
    le_trans hstep0 (le_trans hstep2 hstep1')
  have hgt : upperSumCont f a b hab hcont (2 ^ k) (two_pow_pos k)
      < lowerSumCont f a b hab hcont (2 ^ k) (two_pow_pos k) + ε := by
    have h := add_lt_add_left hk (lowerSumCont f a b hab hcont (2 ^ k) (two_pow_pos k))
    rwa [add_sub_cancel_refine (upperSumCont f a b hab hcont (2 ^ k) (two_pow_pos k))
      (lowerSumCont f a b hab hcont (2 ^ k) (two_pow_pos k))] at h
  have hIk : I < lowerSumCont f a b hab hcont (2 ^ k) (two_pow_pos k) + ε :=
    lt_of_le_of_lt (hIup k) hgt
  exact lt_of_lt_of_le hIk (add_le_add_both hchain (le_refl ε))

/-- **Headline**: the dyadic-only sandwich characterizing `continuous_riemann_integrable`'s witness
actually holds at *every* partition size `n`, not just powers of `2`. -/
theorem sandwich_any_n (f : Real → Real) (a b : Real) (hab : a ≤ b)
    (hcont : ∀ z : Real, a ≤ z → z ≤ b → ContinuousAt f z) (n : Nat) (hn : 0 < n) :
    ∃ I : Real, lowerSumCont f a b hab hcont n hn ≤ I ∧ I ≤ upperSumCont f a b hab hcont n hn := by
  obtain ⟨I, hIsand, hIgap⟩ := continuous_riemann_integrable f a b hab hcont
  refine ⟨I, ?_, ?_⟩
  · exact lowerSumCont_le_any f a b hab hcont I (fun k => (hIsand k).1) hIgap n hn
  · exact le_upperSumCont_any f a b hab hcont I (fun k => (hIsand k).2) hIgap n hn

end Real
end MachLib
