/-
`RiemannIntervalMonotone.lean` — monotonicity of the Riemann integral in its upper limit:
`0 ≤ a ≤ b`, `f` nonnegative & continuous on `[0,b]` ⟹ `∫₀ᵃf ≤ ∫₀ᵇf`.

This is the piece the √π project's disk/square sandwich (Stage 4/5) actually consumes.
`sandwich_any_n` (RiemannIntegralRefine.lean) lets any partition size stand in for the dyadic
family on a SINGLE interval, but `[0,a]` and `[0,b]` are different intervals whose uniform
partitions never align for general real `a,b` — comparing them needs a genuine "nearby points have
nearby f-values" argument, i.e. uniform continuity, not just partition refinement.

Proof idea: fix ε>0. Get a fine dyadic mesh `q` on `[0,b]` (mesh < uniform-continuity's δ, and with
gap < ε on `[0,b]`). Let `i* = m+1` be the least count with `a < i*·q` (so `m·q ≤ a`, i.e. `[0,a]`'s
own `i*`-piece partition has width `a/i* ≤ q`, close to `q`). For `j < i*`, `[0,a]`'s j-th
subinterval sits within `q` of `[0,b]`'s j-th q-width subinterval (both endpoints), so uniform
continuity transfers `maxSub` values: `maxSub_a(j) ≤ maxSub_b(j) + ε'`. Summing gives
`upperSumCont(f,0,a,i*) ≤ upperSumCont(f,0,b,2^K) + ε'·a`, and `I_a ≤ upperSumCont(f,0,a,i*)`
(`sandwich_any_n`) while `upperSumCont(f,0,b,2^K) < I_b + gap` (the defining dyadic property).
Chaining gives `I_a < I_b + ε` for every ε.
-/
import MachLib.RiemannIntegralRefine
import MachLib.HeineCantorUniformContinuity

namespace MachLib
namespace Real

/-! ## §1 — small Nat/Real helpers -/

private theorem le_of_not_lt_mono {x y : Real} (h : ¬ x < y) : y ≤ x := by
  obtain h1 | h1 | h1 := lt_total x y
  · exact absurd h1 h
  · rw [le_iff_lt_or_eq]; exact Or.inr h1.symm
  · rw [le_iff_lt_or_eq]; exact Or.inl h1

/-- Bounded search for the least `n ≤ N` with `a < n·q`: either `n = 0` works trivially, or
`n-1` fails (`(n-1)·q ≤ a`) while `n` succeeds. -/
private theorem least_nq_gt (a q : Real) : ∀ N : Nat, a < natCast N * q →
    ∃ n : Nat, n ≤ N ∧ a < natCast n * q ∧ (n = 0 ∨ natCast (n - 1) * q ≤ a)
  | 0, h => ⟨0, Nat.le_refl 0, h, Or.inl rfl⟩
  | (k + 1), h => by
      by_cases hk : a < natCast k * q
      · obtain ⟨n, hnk, hn1, hn2⟩ := least_nq_gt a q k hk
        exact ⟨n, by omega, hn1, hn2⟩
      · refine ⟨k + 1, Nat.le_refl (k + 1), h, Or.inr ?_⟩
        show natCast (k + 1 - 1) * q ≤ a
        rw [Nat.add_sub_cancel]
        exact le_of_not_lt_mono hk

private theorem natCast_one_local2 : natCast 1 = 1 := by
  rw [natCast_succ, natCast_zero]; exact zero_add 1

private theorem partialSum_add_const (g : Nat → Real) (c : Real) : ∀ n : Nat,
    partialSum (fun j => g j + c) n = partialSum g n + natCast n * c
  | 0 => by show (0:Real) = 0 + natCast 0 * c; rw [natCast_zero]; mach_mpoly [c]
  | k + 1 => by
      show partialSum (fun j => g j + c) k + (g k + c) = (partialSum g k + g k) + natCast (k + 1) * c
      rw [partialSum_add_const g c k, natCast_add k 1, natCast_one_local2]
      mach_mpoly [partialSum g k, natCast k, c, g k]

/-! ## §2 — the drift bound: `[0,a]`'s j-th mesh point is within `q` of `[0,b]`'s -/

private theorem natCast_m_succ (m : Nat) : natCast (m + 1) = natCast m + 1 := by
  rw [natCast_add m 1, natCast_one_local2]

/-- `(m+1)·(a/(m+1)) = a`, i.e. dividing by `m+1` and multiplying back cancels. -/
private theorem mul_div_self_cancel (a : Real) (m : Nat) :
    natCast (m + 1) * (a / natCast (m + 1)) = a := by
  have hne : natCast (m + 1) ≠ 0 := ne_of_gt (natCast_pos (by omega))
  rw [div_def a (natCast (m + 1)) hne]
  rw [show natCast (m + 1) * (a * (1 / natCast (m + 1)))
      = a * (natCast (m + 1) * (1 / natCast (m + 1)))
      from by mach_mpoly [natCast (m + 1), a, 1 / natCast (m + 1)]]
  rw [mul_inv (natCast (m + 1)) hne, mul_one_ax]

private theorem a_div_le_q (a q : Real) (m : Nat) (hratio : a ≤ natCast (m + 1) * q) :
    a / natCast (m + 1) ≤ q := by
  have hne : natCast (m + 1) ≠ 0 := ne_of_gt (natCast_pos (by omega))
  have h1 : a * (1 / natCast (m + 1)) ≤ (natCast (m + 1) * q) * (1 / natCast (m + 1)) :=
    mul_le_mul_of_nonneg_right hratio (one_div_nonneg_of_pos (natCast_pos (show 0 < m+1 by omega)))
  rw [show (natCast (m + 1) * q) * (1 / natCast (m + 1))
      = q * (natCast (m + 1) * (1 / natCast (m + 1)))
      from by mach_mpoly [natCast (m + 1), q, 1 / natCast (m + 1)]] at h1
  rw [mul_inv (natCast (m + 1)) hne, mul_one_ax] at h1
  rwa [div_def a (natCast (m + 1)) hne]

private theorem drift_bound (a q : Real) (m j : Nat) (hj : j ≤ m)
    (hcross : natCast m * q ≤ a) (hratio : a ≤ natCast (m + 1) * q) :
    natCast j * q - natCast j * (a / natCast (m + 1)) ≤ q := by
  have hnn : (0:Real) ≤ q - a / natCast (m + 1) := sub_nonneg_of_le (a_div_le_q a q m hratio)
  have hjm : natCast j ≤ natCast m := natCast_le_of_nat_le hj
  have step1 : natCast j * (q - a / natCast (m + 1)) ≤ natCast m * (q - a / natCast (m + 1)) :=
    mul_le_mul_of_nonneg_right hjm hnn
  have hm1 : natCast m ≤ natCast (m + 1) := by
    rw [natCast_m_succ]
    have h := add_le_add_both (le_refl (natCast m)) (le_of_lt zero_lt_one_ax)
    rwa [show natCast m + 0 = natCast m from by mach_mpoly [natCast m]] at h
  have step2 : natCast m * (q - a / natCast (m + 1)) ≤ natCast (m + 1) * (q - a / natCast (m + 1)) :=
    mul_le_mul_of_nonneg_right hm1 hnn
  have step3 : natCast (m + 1) * (q - a / natCast (m + 1)) = natCast (m + 1) * q - a := by
    rw [show natCast (m + 1) * (q - a / natCast (m + 1))
        = natCast (m + 1) * q - natCast (m + 1) * (a / natCast (m + 1))
        from by mach_mpoly [natCast (m + 1), q, a / natCast (m + 1)]]
    rw [mul_div_self_cancel a m]
  have step4 : natCast (m + 1) * q - a ≤ q := by
    have h5 := add_le_add_both hcross (le_refl q)
    rw [show natCast m * q + q = natCast (m + 1) * q
        from by rw [natCast_m_succ]; mach_mpoly [natCast m, q]] at h5
    have h6 := add_le_add_both h5 (le_refl (-a))
    rwa [show natCast (m + 1) * q + -a = natCast (m + 1) * q - a
        from by mach_mpoly [natCast (m + 1), q, a],
      show a + q + -a = q from by mach_mpoly [a, q]] at h6
  have hchain12 : natCast j * (q - a / natCast (m + 1))
      ≤ natCast (m + 1) * (q - a / natCast (m + 1)) := le_trans step1 step2
  rw [step3] at hchain12
  have hchain : natCast j * (q - a / natCast (m + 1)) ≤ q := le_trans hchain12 step4
  rwa [show natCast j * (q - a / natCast (m + 1))
      = natCast j * q - natCast j * (a / natCast (m + 1))
      from by mach_mpoly [natCast j, q, a / natCast (m + 1)]] at hchain

/-! ## §3 — the coarse `[0,b]` extremum bounds the nearby fine `[0,a]` extremum -/

private theorem sub_zero_local (x : Real) : x - 0 = x := by mach_mpoly [x]

private theorem meshWidth_zero_base (c : Real) (n : Nat) : meshWidth 0 c n = c / natCast n := by
  show (c - 0) / natCast n = c / natCast n
  rw [sub_zero_local c]

private theorem meshPoint_zero_base (c : Real) (n i : Nat) :
    meshPoint 0 c n i = natCast i * (c / natCast n) := by
  show (0:Real) + natCast i * meshWidth 0 c n = natCast i * (c / natCast n)
  rw [meshWidth_zero_base c n]
  mach_mpoly [natCast i, c / natCast n]

private theorem lt_zero_of_not_nonneg (X : Real) (h : ¬ 0 ≤ X) : X < 0 := by
  obtain h1 | h1 | h1 := lt_total X 0
  · exact h1
  · exact absurd ((le_iff_lt_or_eq 0 X).mpr (Or.inr h1.symm)) h
  · exact absurd ((le_iff_lt_or_eq 0 X).mpr (Or.inl h1)) h

private theorem lt_of_not_le_mono {x y : Real} (h : ¬ x ≤ y) : y < x := by
  obtain h1 | h1 | h1 := lt_total x y
  · exact absurd ((le_iff_lt_or_eq x y).mpr (Or.inl h1)) h
  · exact absurd ((le_iff_lt_or_eq x y).mpr (Or.inr h1)) h
  · exact h1

/-- Extract a one-sided bound from an `abs`-difference bound: the standard "closeness in absolute
value gives a closeness in each direction" transfer, specialized to the direction this file needs. -/
private theorem lt_add_of_abs_sub_lt (X Y ε' : Real) (hε'nn : 0 ≤ ε') (h : abs (X - Y) < ε') :
    X < Y + ε' := by
  unfold abs at h
  by_cases hs : 0 ≤ X - Y
  · rw [if_pos hs] at h
    have h2 := add_lt_add_left h Y
    rwa [show Y + (X - Y) = X from by mach_mpoly [X, Y]] at h2
  · have hlt : X - Y < 0 := lt_zero_of_not_nonneg (X - Y) hs
    have h3 : X < Y := by
      have h4 := add_lt_add_left hlt Y
      rwa [show Y + (X - Y) = X from by mach_mpoly [X, Y],
        show Y + 0 = Y from by mach_mpoly [Y]] at h4
    have h5 : Y ≤ Y + ε' := by
      have h6 := add_le_add_both (le_refl Y) hε'nn
      rwa [show Y + 0 = Y from by mach_mpoly [Y]] at h6
    exact lt_of_lt_of_le h3 h5

/-- The coarse `[0,b]` extremum (mesh `q`, count `2^K`) bounds the nearby fine `[0,a]` extremum
(mesh `a/(m+1)`, count `m+1`), up to the uniform-continuity slack `ε'`. -/
theorem maxSub_transfer (f : Real → Real) (a b : Real) (hab0 : 0 ≤ a) (hab : a ≤ b)
    (hab0b : 0 ≤ b)
    (hcont : ∀ z : Real, 0 ≤ z → z ≤ b → ContinuousAt f z)
    (hcont_a : ∀ z : Real, 0 ≤ z → z ≤ a → ContinuousAt f z)
    (m K : Nat) (hK : 0 < 2 ^ K) (j : Nat) (hj : j ≤ m) (hjK : m + 1 ≤ 2 ^ K)
    (q : Real) (hq : meshWidth 0 b (2 ^ K) = q) (hqnn : 0 ≤ q)
    (hcross : natCast m * q ≤ a) (hratio : a ≤ natCast (m + 1) * q)
    (δ ε' : Real) (hδpos : 0 < δ) (hwidth : q < δ) (hε'nn : 0 ≤ ε')
    (hδ : ∀ y z : Real, 0 ≤ y → y ≤ b → 0 ≤ z → z ≤ b → abs (y - z) < δ → abs (f y - f z) < ε') :
    maxSub f 0 a hab0 hcont_a (m + 1) (by omega) j
      ≤ maxSub f 0 b hab0b hcont (2 ^ K) hK j + ε' := by
  have hjm1 : j < m + 1 := by omega
  have hjstar : j < 2 ^ K := by omega
  have hmem := maxSub_mem f 0 a hab0 hcont_a (m + 1) (by omega) j hjm1
  let x := Classical.choose (evt_exists_max f 0 a hab0 hcont_a (m + 1) (by omega) j hjm1)
  have hxeq : maxSub f 0 a hab0 hcont_a (m + 1) (by omega) j = f x :=
    maxSub_eq f 0 a hab0 hcont_a (m + 1) (by omega) j hjm1
  have hx1 : meshPoint 0 a (m + 1) j ≤ x := hmem.1
  have hx2 : x ≤ meshPoint 0 a (m + 1) (j + 1) := hmem.2
  rw [meshPoint_zero_base a (m + 1) j] at hx1
  rw [meshPoint_zero_base a (m + 1) (j + 1)] at hx2
  have hax : 0 ≤ a / natCast (m + 1) := div_nonneg hab0 (le_of_lt (natCast_pos (by omega)))
  have hx2a : x ≤ a := by
    have hjm1' : natCast (j + 1) ≤ natCast (m + 1) := natCast_le_of_nat_le (by omega)
    have h1 : natCast (j + 1) * (a / natCast (m + 1)) ≤ natCast (m + 1) * (a / natCast (m + 1)) :=
      mul_le_mul_of_nonneg_right hjm1' hax
    rw [mul_div_self_cancel a m] at h1
    exact le_trans hx2 h1
  have hxb : x ≤ b := le_trans hx2a hab
  have hx0 : 0 ≤ x := by
    have h1 : (0:Real) ≤ natCast j * (a / natCast (m + 1)) := mul_nonneg (natCast_nonneg j) hax
    exact le_trans h1 hx1
  have hratioj1 : natCast (j + 1) * (a / natCast (m + 1)) ≤ natCast (j + 1) * q :=
    mul_le_mul_of_nonneg_left (a_div_le_q a q m hratio) (natCast_nonneg (j + 1))
  have hxleq : x ≤ natCast (j + 1) * q := le_trans hx2 hratioj1
  have hbeq0 : meshPoint 0 b (2 ^ K) j = natCast j * q := by
    show (0:Real) + natCast j * meshWidth 0 b (2 ^ K) = natCast j * q
    rw [hq]; mach_mpoly [natCast j, q]
  have hbeq1 : meshPoint 0 b (2 ^ K) (j + 1) = natCast (j + 1) * q := by
    show (0:Real) + natCast (j + 1) * meshWidth 0 b (2 ^ K) = natCast (j + 1) * q
    rw [hq]; mach_mpoly [natCast (j + 1), q]
  have hzb : natCast j * q ≤ b := by
    have h2Kb : natCast (2 ^ K) * meshWidth 0 b (2 ^ K) = b - 0 := natCast_mul_meshWidth 0 b (2 ^ K) hK
    rw [hq, sub_zero_local b] at h2Kb
    have hjle : natCast j ≤ natCast (2 ^ K) := natCast_le_of_nat_le (by omega)
    have h1 : natCast j * q ≤ natCast (2 ^ K) * q := mul_le_mul_of_nonneg_right hjle hqnn
    rwa [h2Kb] at h1
  have hz0 : (0:Real) ≤ natCast j * q := mul_nonneg (natCast_nonneg j) hqnn
  by_cases hcase : natCast j * q ≤ x
  · have hxb1 : meshPoint 0 b (2 ^ K) j ≤ x := by rw [hbeq0]; exact hcase
    have hxb2 : x ≤ meshPoint 0 b (2 ^ K) (j + 1) := by rw [hbeq1]; exact hxleq
    have hspec := maxSub_spec f 0 b hab0b hcont (2 ^ K) hK j hjstar x hxb1 hxb2
    rw [hxeq]
    have h1 := add_le_add_both hspec hε'nn
    rwa [show f x + 0 = f x from by mach_mpoly [f x]] at h1
  · have hcase := lt_of_not_le_mono hcase
    have hposdiff : (0:Real) ≤ natCast j * q - x := sub_nonneg_of_le (le_of_lt hcase)
    have hdrift := drift_bound a q m j hj hcross hratio
    have hdriftx : natCast j * q - x ≤ natCast j * q - natCast j * (a / natCast (m + 1)) := by
      have h1 := add_le_add_both (le_refl (natCast j * q)) (neg_le_neg hx1)
      rwa [← sub_def (natCast j * q) x,
        ← sub_def (natCast j * q) (natCast j * (a / natCast (m + 1)))] at h1
    have hdriftx2 : natCast j * q - x < δ := lt_of_le_of_lt (le_trans hdriftx hdrift) hwidth
    have habsjq : abs (natCast j * q - x) < δ := by rw [abs_of_nonneg hposdiff]; exact hdriftx2
    have habsx : abs (x - natCast j * q) < δ := by rw [abs_sub_comm]; exact habsjq
    have hzmem1 : meshPoint 0 b (2 ^ K) j ≤ natCast j * q := by rw [hbeq0]; exact le_refl _
    have hzmem2 : natCast j * q ≤ meshPoint 0 b (2 ^ K) (j + 1) := by
      rw [hbeq1]
      exact mul_le_mul_of_nonneg_right (natCast_le_of_nat_le (by omega)) hqnn
    have hzspec := maxSub_spec f 0 b hab0b hcont (2 ^ K) hK j hjstar (natCast j * q)
      hzmem1 hzmem2
    have hftrans := hδ x (natCast j * q) hx0 hxb hz0 hzb habsx
    have hflt := lt_add_of_abs_sub_lt (f x) (f (natCast j * q)) ε' hε'nn hftrans
    rw [hxeq]
    have h2 := lt_of_lt_of_le hflt (add_le_add_both hzspec (le_refl ε'))
    exact le_of_lt h2

/-! ## §4 — summing the per-term transfer into an upper-sum bound -/

theorem maxSub_nonneg (f : Real → Real) (a b : Real) (hab : a ≤ b)
    (hcont : ∀ z : Real, a ≤ z → z ≤ b → ContinuousAt f z)
    (hnonneg : ∀ z : Real, a ≤ z → z ≤ b → 0 ≤ f z) (n : Nat) (hn : 0 < n) (i : Nat) :
    0 ≤ maxSub f a b hab hcont n hn i := by
  by_cases hi : i < n
  · rw [maxSub_eq f a b hab hcont n hn i hi]
    have hmem := maxSub_mem f a b hab hcont n hn i hi
    apply hnonneg
    · exact le_trans (meshPoint_mem a b n i hab hn (Nat.le_of_lt hi)).1 hmem.1
    · exact le_trans hmem.2 (meshPoint_mem a b n (i + 1) hab hn hi).2
  · unfold maxSub
    rw [dif_neg hi]
    exact hnonneg a (le_refl a) hab

theorem upperSumCont_transfer (f : Real → Real) (a b : Real) (hab0 : 0 ≤ a) (hab : a ≤ b)
    (hab0b : 0 ≤ b)
    (hcont : ∀ z : Real, 0 ≤ z → z ≤ b → ContinuousAt f z)
    (hcont_a : ∀ z : Real, 0 ≤ z → z ≤ a → ContinuousAt f z)
    (hnonneg : ∀ z : Real, 0 ≤ z → z ≤ b → 0 ≤ f z)
    (m K : Nat) (hK : 0 < 2 ^ K) (hjK : m + 1 ≤ 2 ^ K)
    (q : Real) (hq : meshWidth 0 b (2 ^ K) = q) (hqnn : 0 ≤ q)
    (hcross : natCast m * q ≤ a) (hratio : a ≤ natCast (m + 1) * q)
    (δ ε' : Real) (hδpos : 0 < δ) (hwidth : q < δ) (hε'nn : 0 ≤ ε')
    (hδ : ∀ y z : Real, 0 ≤ y → y ≤ b → 0 ≤ z → z ≤ b → abs (y - z) < δ → abs (f y - f z) < ε') :
    upperSumCont f 0 a hab0 hcont_a (m + 1) (by omega)
      ≤ upperSumCont f 0 b hab0b hcont (2 ^ K) hK + ε' * a := by
  show partialSum (maxSub f 0 a hab0 hcont_a (m + 1) (by omega)) (m + 1) * meshWidth 0 a (m + 1)
    ≤ partialSum (maxSub f 0 b hab0b hcont (2 ^ K) hK) (2 ^ K) * meshWidth 0 b (2 ^ K) + ε' * a
  rw [hq, meshWidth_zero_base a (m + 1)]
  have htermwise : ∀ j, j < m + 1 →
      maxSub f 0 a hab0 hcont_a (m + 1) (by omega) j
        ≤ (fun j => maxSub f 0 b hab0b hcont (2 ^ K) hK j + ε') j := by
    intro j hj
    exact maxSub_transfer f a b hab0 hab hab0b hcont hcont_a m K hK j (by omega) hjK q hq hqnn
      hcross hratio δ ε' hδpos hwidth hε'nn hδ
  have hstep1 := partialSum_le_of_termwise_le (m + 1) htermwise
  rw [partialSum_add_const (maxSub f 0 b hab0b hcont (2 ^ K) hK) ε' (m + 1)] at hstep1
  have hann : (0:Real) ≤ a / natCast (m + 1) := div_nonneg hab0 (le_of_lt (natCast_pos (by omega)))
  have hstep2 : partialSum (maxSub f 0 a hab0 hcont_a (m + 1) (by omega)) (m + 1)
      * (a / natCast (m + 1))
      ≤ (partialSum (maxSub f 0 b hab0b hcont (2 ^ K) hK) (m + 1) + natCast (m + 1) * ε')
      * (a / natCast (m + 1)) :=
    mul_le_mul_of_nonneg_right hstep1 hann
  have hpartb_nonneg : ∀ i : Nat, 0 ≤ maxSub f 0 b hab0b hcont (2 ^ K) hK i :=
    fun i => maxSub_nonneg f 0 b hab0b hcont hnonneg (2 ^ K) hK i
  have hstep3 : partialSum (maxSub f 0 b hab0b hcont (2 ^ K) hK) (m + 1)
      ≤ partialSum (maxSub f 0 b hab0b hcont (2 ^ K) hK) (2 ^ K) :=
    partialSum_mono hpartb_nonneg hjK
  have hexpand : (partialSum (maxSub f 0 b hab0b hcont (2 ^ K) hK) (m + 1) + natCast (m + 1) * ε')
      * (a / natCast (m + 1))
      = partialSum (maxSub f 0 b hab0b hcont (2 ^ K) hK) (m + 1) * (a / natCast (m + 1))
        + ε' * a := by
    rw [show (partialSum (maxSub f 0 b hab0b hcont (2 ^ K) hK) (m + 1) + natCast (m + 1) * ε')
        * (a / natCast (m + 1))
        = partialSum (maxSub f 0 b hab0b hcont (2 ^ K) hK) (m + 1) * (a / natCast (m + 1))
          + ε' * (natCast (m + 1) * (a / natCast (m + 1)))
        from by mach_mpoly [partialSum (maxSub f 0 b hab0b hcont (2 ^ K) hK) (m + 1),
          a / natCast (m + 1), natCast (m + 1), ε']]
    rw [mul_div_self_cancel a m]
  rw [hexpand] at hstep2
  have hstep4 : partialSum (maxSub f 0 b hab0b hcont (2 ^ K) hK) (m + 1) * (a / natCast (m + 1))
      ≤ partialSum (maxSub f 0 b hab0b hcont (2 ^ K) hK) (m + 1) * q :=
    mul_le_mul_of_nonneg_left (a_div_le_q a q m hratio) (partialSum_nonneg hpartb_nonneg (m + 1))
  have hstep5 : partialSum (maxSub f 0 b hab0b hcont (2 ^ K) hK) (m + 1) * q
      ≤ partialSum (maxSub f 0 b hab0b hcont (2 ^ K) hK) (2 ^ K) * q :=
    mul_le_mul_of_nonneg_right hstep3 hqnn
  have h1 := le_trans hstep2 (add_le_add_both hstep4 (le_refl (ε' * a)))
  exact le_trans h1 (add_le_add_both hstep5 (le_refl (ε' * a)))

/-! ## §5 — assembly: `∫₀ᵃf ≤ ∫₀ᵇf` -/

theorem minSub_nonneg (f : Real → Real) (a b : Real) (hab : a ≤ b)
    (hcont : ∀ z : Real, a ≤ z → z ≤ b → ContinuousAt f z)
    (hnonneg : ∀ z : Real, a ≤ z → z ≤ b → 0 ≤ f z) (n : Nat) (hn : 0 < n) (i : Nat) :
    0 ≤ minSub f a b hab hcont n hn i := by
  by_cases hi : i < n
  · rw [minSub_eq f a b hab hcont n hn i hi]
    have hmem := minSub_mem f a b hab hcont n hn i hi
    apply hnonneg
    · exact le_trans (meshPoint_mem a b n i hab hn (Nat.le_of_lt hi)).1 hmem.1
    · exact le_trans hmem.2 (meshPoint_mem a b n (i + 1) hab hn hi).2
  · unfold minSub
    rw [dif_neg hi]
    exact hnonneg a (le_refl a) hab

private theorem mul_two_eq_add_self (X : Real) : X * (1 + 1) = X + X := by mach_mpoly [X]

private theorem add_lt_add_both {p q r s : Real} (h1 : p < q) (h2 : r < s) : p + r < q + s := by
  have ha := add_lt_add_left h1 r
  rw [show r + p = p + r from by mach_mpoly [p, r], show r + q = q + r from by mach_mpoly [q, r]] at ha
  have hb := add_lt_add_left h2 q
  exact lt_trans_ax ha hb

private theorem zero_lt_of_le_of_ne {a : Real} (h0 : 0 ≤ a) (hne : a ≠ 0) : 0 < a := by
  obtain h1 | h1 | h1 := lt_total 0 a
  · exact h1
  · exact absurd h1.symm hne
  · exact absurd ((le_iff_lt_or_eq a 0).mpr (Or.inl h1)) (by
      intro hcontra; exact lt_irrefl_ax 0 (lt_of_le_of_lt h0 h1))

/-- **Monotonicity of the Riemann integral in its upper limit.** For `f` continuous and
nonnegative on `[0,b]`, `0 ≤ a ≤ b` implies `∫₀ᵃf ≤ ∫₀ᵇf`. The genuinely new work over
`RiemannIntegralRefine.lean` is the disk/square sandwich's actual need: comparing the integral
over two DIFFERENT intervals `[0,a]` and `[0,b]`, which needs uniform continuity (`maxSub_transfer`),
not just same-interval partition refinement (`sandwich_any_n`). -/
theorem riemann_integral_mono_interval (f : Real → Real) (a b : Real) (hab0 : 0 ≤ a) (hab : a ≤ b)
    (hab0b : 0 ≤ b)
    (hcont : ∀ z : Real, 0 ≤ z → z ≤ b → ContinuousAt f z)
    (hcont_a : ∀ z : Real, 0 ≤ z → z ≤ a → ContinuousAt f z)
    (hnonneg : ∀ z : Real, 0 ≤ z → z ≤ b → 0 ≤ f z)
    (I_a I_b : Real)
    (hIaup : ∀ k, I_a ≤ upperSumCont f 0 a hab0 hcont_a (2 ^ k) (two_pow_pos k))
    (hIagap : ∀ ε : Real, 0 < ε → ∃ k, upperSumCont f 0 a hab0 hcont_a (2 ^ k) (two_pow_pos k)
      - lowerSumCont f 0 a hab0 hcont_a (2 ^ k) (two_pow_pos k) < ε)
    (hIblow : ∀ k, lowerSumCont f 0 b hab0b hcont (2 ^ k) (two_pow_pos k) ≤ I_b)
    (hIbgap : ∀ ε : Real, 0 < ε → ∃ k, upperSumCont f 0 b hab0b hcont (2 ^ k) (two_pow_pos k)
      - lowerSumCont f 0 b hab0b hcont (2 ^ k) (two_pow_pos k) < ε) :
    I_a ≤ I_b := by
  by_cases hab_eq : a = b
  · subst hab_eq
    apply le_of_forall_pos_lt_add
    intro ε hε
    obtain ⟨k, hk⟩ := hIbgap ε hε
    have h1 := hIaup k
    have h2 : upperSumCont f 0 a hab0 hcont_a (2 ^ k) (two_pow_pos k)
        < lowerSumCont f 0 a hab0 hcont_a (2 ^ k) (two_pow_pos k) + ε := by
      have h3 := add_lt_add_left hk (lowerSumCont f 0 a hab0 hcont_a (2 ^ k) (two_pow_pos k))
      rwa [show lowerSumCont f 0 a hab0 hcont_a (2 ^ k) (two_pow_pos k)
          + (upperSumCont f 0 a hab0 hcont_a (2 ^ k) (two_pow_pos k)
            - lowerSumCont f 0 a hab0 hcont_a (2 ^ k) (two_pow_pos k))
          = upperSumCont f 0 a hab0 hcont_a (2 ^ k) (two_pow_pos k)
          from by mach_mpoly [lowerSumCont f 0 a hab0 hcont_a (2 ^ k) (two_pow_pos k),
            upperSumCont f 0 a hab0 hcont_a (2 ^ k) (two_pow_pos k)]] at h3
    have h4 := lt_of_le_of_lt h1 h2
    exact lt_of_lt_of_le h4 (add_le_add_both (hIblow k) (le_refl ε))
  · by_cases ha0 : a = 0
    · have hIa0 : I_a ≤ 0 := by
        have h1 := hIaup 0
        have hmw0 : meshWidth 0 a (2 ^ 0) = 0 := by
          show (a - 0) / natCast (2 ^ 0) = 0
          rw [ha0, sub_zero_local (0:Real), div_def (0:Real) (natCast (2 ^ 0))
            (ne_of_gt (natCast_pos (two_pow_pos 0)))]
          mach_mpoly [1 / natCast (2 ^ 0)]
        have hus0 : upperSumCont f 0 a hab0 hcont_a (2 ^ 0) (two_pow_pos 0) = 0 := by
          show partialSum (maxSub f 0 a hab0 hcont_a (2 ^ 0) (two_pow_pos 0)) (2 ^ 0)
            * meshWidth 0 a (2 ^ 0) = 0
          rw [hmw0]
          mach_mpoly [partialSum (maxSub f 0 a hab0 hcont_a (2 ^ 0) (two_pow_pos 0)) (2 ^ 0)]
        rwa [hus0] at h1
      have hIb0 : 0 ≤ I_b := by
        have h1 := hIblow 0
        have hms0 : (0:Real) ≤ minSub f 0 b hab0b hcont (2 ^ 0) (two_pow_pos 0) 0 :=
          minSub_nonneg f 0 b hab0b hcont hnonneg (2 ^ 0) (two_pow_pos 0) 0
        have hls0 : (0:Real) ≤ lowerSumCont f 0 b hab0b hcont (2 ^ 0) (two_pow_pos 0) := by
          show (0:Real) ≤ partialSum (minSub f 0 b hab0b hcont (2 ^ 0) (two_pow_pos 0)) (2 ^ 0)
            * meshWidth 0 b (2 ^ 0)
          have hps : (0:Real) ≤ partialSum (minSub f 0 b hab0b hcont (2 ^ 0) (two_pow_pos 0)) (2 ^ 0) :=
            partialSum_nonneg (fun i => minSub_nonneg f 0 b hab0b hcont hnonneg (2 ^ 0) (two_pow_pos 0) i)
              (2 ^ 0)
          exact mul_nonneg hps (meshWidth_nonneg hab0b (2 ^ 0))
        exact le_trans hls0 h1
      exact le_trans hIa0 hIb0
    · have ha0' : 0 < a := zero_lt_of_le_of_ne hab0 ha0
      have hab' : a < b := by
        obtain h1 | h1 := (le_iff_lt_or_eq a b).mp hab
        · exact h1
        · exact absurd h1 hab_eq
      apply le_of_forall_pos_lt_add
      intro ε hε
      have ha1pos : 0 < a + 1 := by
        have h1 := add_le_add_both hab0 (le_refl (1:Real))
        rw [show (0:Real) + 1 = 1 from by mach_mpoly [(1:Real)]] at h1
        exact lt_of_lt_of_le zero_lt_one_ax h1
      have hε''pos : 0 < ε / (1 + 1) := div_pos_of_pos_pos hε two_pos
      let ε'' := ε / (1 + 1)
      have hε'pos : 0 < ε'' / (a + 1) := div_pos_of_pos_pos hε''pos ha1pos
      let ε' := ε'' / (a + 1)
      have hcancel : ε' * (a + 1) = ε'' := div_mul_cancel (ne_of_gt ha1pos)
      have hεa : ε' * a < ε'' := by
        have h1 : ε' * a + ε' = ε'' := by
          rw [show ε' * a + ε' = ε' * (a + 1) from by mach_mpoly [ε', a]]
          exact hcancel
        have h2 := add_lt_add_left hε'pos (ε' * a)
        rw [h1] at h2
        rwa [show ε' * a + 0 = ε' * a from by mach_mpoly [ε' * a]] at h2
      have hcancel2 : ε'' * (1 + 1) = ε := div_mul_cancel (ne_of_gt two_pos)
      obtain ⟨K0, hK0⟩ := hIbgap ε'' hε''pos
      obtain ⟨δ, hδpos, hδ⟩ := heine_cantor_uniform_continuity hab0b hcont ε' hε'pos
      have hbpos : 0 < b + 1 := by
        have h1 := add_le_add_both hab0b (le_refl (1:Real))
        rw [show (0:Real) + 1 = 1 from by mach_mpoly [(1:Real)]] at h1
        exact lt_of_lt_of_le zero_lt_one_ax h1
      obtain ⟨N, hN⟩ := archimedean (b / δ)
      have hNpos : 0 < N := by
        obtain h0 | hpos := Nat.eq_zero_or_pos N
        · exfalso
          have hnn : 0 ≤ b / δ := div_nonneg hab0b (le_of_lt hδpos)
          rw [h0, natCast_zero] at hN
          exact lt_irrefl_ax 0 (lt_of_le_of_lt hnn hN)
        · exact hpos
      have hNle2N : N ≤ 2 ^ N := nat_le_two_pow N
      have h2Npos : 0 < natCast (2 ^ N) := natCast_pos (two_pow_pos N)
      have hNcast : natCast N ≤ natCast (2 ^ N) := natCast_le_of_nat_le hNle2N
      have hwidthK1 : meshWidth 0 b (2 ^ N) < δ := by
        show (b - 0) / natCast (2 ^ N) < δ
        rw [sub_zero_local b]
        have hstep1 : b / natCast (2 ^ N) ≤ b / natCast N :=
          div_le_div_pos hab0b (le_refl b) (natCast_pos hNpos) hNcast
        have hstep2 : b / natCast N < δ := by
          have hcross : b < δ * natCast N := by
            have hmul := mul_lt_mul_of_pos_right hN hδpos
            rw [div_mul_cancel (ne_of_gt hδpos)] at hmul
            rwa [mul_comm (natCast N) δ] at hmul
          exact div_lt_of_lt_mul hcross (natCast_pos hNpos)
        exact lt_of_le_of_lt hstep1 hstep2
      let K := K0 + N
      have hKdef : K = K0 + N := rfl
      have hwidthK : meshWidth 0 b (2 ^ K) < δ := by
        have hle : natCast (2 ^ N) ≤ natCast (2 ^ K) := by
          apply natCast_le_of_nat_le
          rw [hKdef]
          calc 2 ^ N ≤ 2 ^ N * 2 ^ K0 := Nat.le_mul_of_pos_right (2 ^ N) (two_pow_pos K0)
            _ = 2 ^ (N + K0) := by rw [← Nat.pow_add]
            _ = 2 ^ (K0 + N) := by rw [Nat.add_comm]
        have hstep1 : b / natCast (2 ^ K) ≤ b / natCast (2 ^ N) :=
          div_le_div_pos hab0b (le_refl b) (natCast_pos (two_pow_pos N)) hle
        have heq : meshWidth 0 b (2 ^ K) = b / natCast (2 ^ K) := by
          show (b - 0) / natCast (2 ^ K) = b / natCast (2 ^ K)
          rw [sub_zero_local b]
        have heqN : meshWidth 0 b (2 ^ N) = b / natCast (2 ^ N) := by
          show (b - 0) / natCast (2 ^ N) = b / natCast (2 ^ N)
          rw [sub_zero_local b]
        rw [heq]
        rw [heqN] at hwidthK1
        exact lt_of_le_of_lt hstep1 hwidthK1
      have hgapK : upperSumCont f 0 b hab0b hcont (2 ^ K) (two_pow_pos K)
          - lowerSumCont f 0 b hab0b hcont (2 ^ K) (two_pow_pos K) < ε'' := by
        have hu := upperSumCont_dyadic_anti f 0 b hab0b hcont K0 N (two_pow_pos K0)
        have hl := lowerSumCont_dyadic_mono f 0 b hab0b hcont K0 N (two_pow_pos K0)
        have hneg : -lowerSumCont f 0 b hab0b hcont (2 ^ (K0 + N)) (two_pow_pos (K0 + N))
            ≤ -lowerSumCont f 0 b hab0b hcont (2 ^ K0) (two_pow_pos K0) := neg_le_neg hl
        have hsum := add_le_add_both hu hneg
        rw [← sub_def (upperSumCont f 0 b hab0b hcont (2 ^ (K0 + N)) (two_pow_pos (K0 + N)))
              (lowerSumCont f 0 b hab0b hcont (2 ^ (K0 + N)) (two_pow_pos (K0 + N))),
            ← sub_def (upperSumCont f 0 b hab0b hcont (2 ^ K0) (two_pow_pos K0))
              (lowerSumCont f 0 b hab0b hcont (2 ^ K0) (two_pow_pos K0))] at hsum
        rw [hKdef]
        exact lt_of_le_of_lt hsum hK0
      let q := meshWidth 0 b (2 ^ K)
      have hq : meshWidth 0 b (2 ^ K) = q := rfl
      have hqnn : 0 ≤ q := meshWidth_nonneg hab0b (2 ^ K)
      have hqb : natCast (2 ^ K) * q = b := by
        have h1 := natCast_mul_meshWidth 0 b (2 ^ K) (two_pow_pos K)
        rw [hq, sub_zero_local b] at h1
        exact h1
      have haltN : a < natCast (2 ^ K) * q := by rw [hqb]; exact hab'
      obtain ⟨n, hnle, hn1, hn2⟩ := least_nq_gt a q (2 ^ K) haltN
      have hnne : n ≠ 0 := by
        intro hn0
        rw [hn0, natCast_zero] at hn1
        rw [zero_mul q] at hn1
        exact lt_irrefl_ax 0 (lt_trans_ax ha0' hn1)
      obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hnne
      rw [hm] at hnle hn1 hn2
      have hcross : natCast m * q ≤ a := by
        obtain hz | hz := hn2
        · omega
        · rwa [show m + 1 - 1 = m from by omega] at hz
      have hratio : a ≤ natCast (m + 1) * q := le_of_lt hn1
      have hjK : m + 1 ≤ 2 ^ K := hnle
      have htransfer := upperSumCont_transfer f a b hab0 (le_of_lt hab') hab0b hcont hcont_a hnonneg m K
        (two_pow_pos K) hjK q hq hqnn hcross hratio δ ε' hδpos hwidthK (le_of_lt hε'pos) hδ
      have hIale : I_a ≤ upperSumCont f 0 a hab0 hcont_a (m + 1) (by omega) :=
        le_upperSumCont_any f 0 a hab0 hcont_a I_a hIaup hIagap (m + 1) (by omega)
      have hchain : I_a ≤ upperSumCont f 0 b hab0b hcont (2 ^ K) (two_pow_pos K) + ε' * a :=
        le_trans hIale htransfer
      have hgapK' : upperSumCont f 0 b hab0b hcont (2 ^ K) (two_pow_pos K)
          < lowerSumCont f 0 b hab0b hcont (2 ^ K) (two_pow_pos K) + ε'' := by
        have h3 := add_lt_add_left hgapK
          (lowerSumCont f 0 b hab0b hcont (2 ^ K) (two_pow_pos K))
        rwa [show lowerSumCont f 0 b hab0b hcont (2 ^ K) (two_pow_pos K)
            + (upperSumCont f 0 b hab0b hcont (2 ^ K) (two_pow_pos K)
              - lowerSumCont f 0 b hab0b hcont (2 ^ K) (two_pow_pos K))
            = upperSumCont f 0 b hab0b hcont (2 ^ K) (two_pow_pos K)
            from by mach_mpoly [lowerSumCont f 0 b hab0b hcont (2 ^ K) (two_pow_pos K),
              upperSumCont f 0 b hab0b hcont (2 ^ K) (two_pow_pos K)]] at h3
      have hIbge : lowerSumCont f 0 b hab0b hcont (2 ^ K) (two_pow_pos K) ≤ I_b := hIblow K
      have hstep : upperSumCont f 0 b hab0b hcont (2 ^ K) (two_pow_pos K) < I_b + ε'' :=
        lt_of_lt_of_le hgapK' (add_le_add_both hIbge (le_refl ε''))
      have hcombine : upperSumCont f 0 b hab0b hcont (2 ^ K) (two_pow_pos K) + ε' * a
          < (I_b + ε'') + ε'' := add_lt_add_both hstep hεa
      have heqfin : ε'' + ε'' = ε := by
        rw [← mul_two_eq_add_self ε'']
        exact hcancel2
      have hIa_lt : I_a < (I_b + ε'') + ε'' := lt_of_le_of_lt hchain hcombine
      rwa [add_assoc I_b ε'' ε'', heqfin] at hIa_lt
