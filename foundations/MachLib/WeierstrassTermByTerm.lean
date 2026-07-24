import MachLib.WeierstrassSumContinuous
import MachLib.Rolle
import MachLib.TrigLipschitz

/-!
# Term-by-term differentiation: the Weierstrass sum's actual derivative

The last gap flagged in `WeierstrassSumContinuous.lean`: connect `W`'s ACTUAL derivative to the
already-summable `k=1` term sequence (`weierstrass_term_hasBoundedPartialSums`). Classical
statement (Rudin, *Principles of Mathematical Analysis*, Thm 7.17): if `Σf_n` converges pointwise
to `f` and `Σf_n'` converges uniformly, then `f' = Σf_n'`.

## Why this needed a new axiom

`HasDerivAt` is fully opaque in this codebase — no epsilon-delta unfolding exists anywhere
(unlike `ContinuousAt`, which IS transparent). Every existing `HasDerivAt` fact goes through the
closure axioms (`_add`/`_mul`/`_comp`/`_const`/...), built from finitely many elementary
functions — a closure that cannot reach `W`, a genuine infinite sum. `Differentiation.lean` now
carries `HasDerivAt_of_eps_delta`, added for exactly this arc (user-approved via
`AskUserQuestion`, weighed against a zero-new-axiom alternative and chosen to stay compatible
with the rest of the codebase's `HasDerivAt`-based machinery).

## The proof, adapted from Rudin's route

Fix `x`, `ε>0`. Choose `N` so the `k=1` majorant's tail past `N` is `< ε/3` (Cauchy criterion on
the derivative series). Split `W(y)-W(x)-D(x)(y-x)` into a finite-`N` piece plus a tail piece:

  - **Finite piece** (`term 1`): `S_N(y)-S_N(x)-D_N(x)(y-x) = [D_N(c)-D_N(x)](y-x)` for some `c`
    between `x,y` (MVT on `S_N`). Bounded via a Lipschitz bound on `D_N` — and here's the
    simplification versus the textbook route: `D_N`'s Lipschitz constant doesn't need a *second*
    derivative. `D_N`'s summand is `Aₙ·(−sin(Kₙz)·Kₙ)`, so `|D_N(c)−D_N(x)| ≤ Σ Aₙ·Kₙ·|sin(Kₙc)
    −sin(Kₙx)| ≤ Σ Aₙ·Kₙ²·|c−x|` directly via the pre-existing `sin_lipschitz`
    (`TrigLipschitz.lean`) — algebra plus one Lipschitz fact. `Σ AₙKₙ²` is exactly the `k=2`
    majorant, already known summable — no new `HasDerivAt` needed for `D_N` itself.
  - **Tail piece** (`term 2`): `(W(y)-S_N(y))-(W(x)-S_N(x))`. MVT applied to the FINITE block
    `S_n-S_N` (`n≥N`) plus the derivative series' Cauchy-tail bound gives this `≤ (ε/3)|y-x|`
    for every finite `n≥N`; letting `n→∞` (an explicit `ε`-of-room argument,
    `le_of_forall_pos_lt_add`, since convergence here comes from concrete `sup_exists` tail
    bounds, not an abstract limit) transfers the bound to `W` itself.

## What this proves

  - `weierstrass_sum_hasDerivAt` — `W` (from `weierstrass_sum_continuous`) is genuinely
    differentiable everywhere, with `HasDerivAt W (D x) x` for an explicit `D`, `D x` being the
    (already-summable) `k=1` term series' actual sum at `x`.

`sorryAx`-free, exactly ONE new axiom (`HasDerivAt_of_eps_delta`, disclosed in `AxiomLedger.lean`,
300 axioms total, up from 299).
-/

namespace MachLib
namespace Real

/-! ## §1 — A concrete "epsilon of room" lemma -/

private theorem h11pos : (0 : Real) < 1 + 1 := add_pos one_pos one_pos
private theorem h11ne : (1 + 1 : Real) ≠ 0 := ne_of_gt h11pos

private theorem abs_sub_le_local (a b : Real) : abs (a - b) ≤ abs a + abs b := by
  have h := abs_add a (-b)
  rw [show a + -b = a - b from by mach_mpoly [a, b], abs_neg b] at h
  exact h

private theorem add_lt_add_right_local {a b : Real} (h : a < b) (c : Real) : a + c < b + c := by
  rw [add_comm a c, add_comm b c]; exact add_lt_add_left h c

private theorem add_lt_add_local {a b c d : Real} (h1 : a < b) (h2 : c < d) : a + c < b + d :=
  lt_trans_ax (add_lt_add_right_local h1 c) (add_lt_add_left h2 b)

theorem le_of_forall_pos_lt_add {a b : Real} (h : ∀ η : Real, 0 < η → a < b + η) : a ≤ b := by
  apply Classical.byContradiction
  intro hcon
  have hba : b < a := by
    rcases lt_total a b with hlt | heq | hgt
    · exact absurd (le_of_lt hlt) hcon
    · exact absurd ((le_iff_lt_or_eq a b).mpr (Or.inr heq)) hcon
    · exact hgt
  have hd : 0 < a - b := sub_pos_of_lt hba
  have h2 := h (a - b) hd
  rw [show b + (a - b) = a from by mach_mpoly [a, b]] at h2
  exact absurd h2 (lt_irrefl_ax a)

/-! ## §2 — `k=1` and `k=2` majorants, closed form -/

/-- `Aₙ·Kₙ` — the `k=1` majorant (amplitude × frequency), closed form. -/
noncomputable def weierstrassAmp1 (t : Real) (n : Nat) : Real :=
  weierstrassAmplitude t n * weierstrassFreq n

/-- `Aₙ·Kₙ²` — the `k=2` majorant, closed form. -/
noncomputable def weierstrassAmp2 (t : Real) (n : Nat) : Real :=
  weierstrassAmplitude t n * weierstrassFreq n * weierstrassFreq n

/-- The actual `n`-th derivative term of `weierstrassTerm`, matching `weierstrassTerm_hasDerivAt`. -/
noncomputable def weierstrassTerm1 (t : Real) (n : Nat) (x : Real) : Real :=
  weierstrassAmplitude t n * (-Real.sin (weierstrassFreq n * x) * weierstrassFreq n)

theorem weierstrassTerm_hasDerivAt' (t : Real) (n : Nat) (x : Real) :
    HasDerivAt (weierstrassTerm t n) (weierstrassTerm1 t n x) x :=
  weierstrassTerm_hasDerivAt t n x

theorem weierstrassFreq_pos (n : Nat) : 0 < weierstrassFreq n := by
  unfold weierstrassFreq
  have hb : (0:Real) < 1 + 1 + 1 := by
    have h1 : (0:Real) < 1 + 1 := add_pos one_pos one_pos
    exact add_pos h1 one_pos
  exact mul_pos (npow_pos hb n) pi_pos

theorem weierstrassAmp1_nonneg (t : Real) (n : Nat) : 0 ≤ weierstrassAmp1 t n :=
  mul_nonneg (weierstrassAmplitude_nonneg t n) (le_of_lt (weierstrassFreq_pos n))

theorem weierstrassAmp2_nonneg (t : Real) (n : Nat) : 0 ≤ weierstrassAmp2 t n :=
  mul_nonneg (mul_nonneg (weierstrassAmplitude_nonneg t n) (le_of_lt (weierstrassFreq_pos n)))
    (le_of_lt (weierstrassFreq_pos n))

theorem weierstrassAmp1_hasBoundedPartialSums (t : Real) (ht : 0 < t) :
    HasBoundedPartialSums (weierstrassAmp1 t) := by
  have h := weierstrass_term_hasBoundedPartialSums t ht 1
  have heq : (fun n => npow 1 pi * npow n (1 / (1 + 1)) * npow (n * 1) (1 + 1 + 1)
        * Real.exp (-(pi * pi * t / (1 + 1) * npow n (npow 2 (1 + 1 + 1)))))
      = weierstrassAmp1 t := by
    funext n
    show npow 1 pi * npow n (1 / (1 + 1)) * npow (n * 1) (1 + 1 + 1)
        * Real.exp (-(pi * pi * t / (1 + 1) * npow n (npow 2 (1 + 1 + 1))))
      = weierstrassAmp1 t n
    unfold weierstrassAmp1 weierstrassAmplitude weierstrassFreq
    rw [show npow 1 pi = pi from by show pi * npow 0 pi = pi; rw [show npow 0 pi = 1 from rfl]; mach_ring,
        show n * 1 = n from by omega]
    mach_ring
  rwa [heq] at h

theorem weierstrassAmp2_hasBoundedPartialSums (t : Real) (ht : 0 < t) :
    HasBoundedPartialSums (weierstrassAmp2 t) := by
  have h := weierstrass_term_hasBoundedPartialSums t ht 2
  have heq : (fun n => npow 2 pi * npow n (1 / (1 + 1)) * npow (n * 2) (1 + 1 + 1)
        * Real.exp (-(pi * pi * t / (1 + 1) * npow n (npow 2 (1 + 1 + 1)))))
      = weierstrassAmp2 t := by
    funext n
    show npow 2 pi * npow n (1 / (1 + 1)) * npow (n * 2) (1 + 1 + 1)
        * Real.exp (-(pi * pi * t / (1 + 1) * npow n (npow 2 (1 + 1 + 1))))
      = weierstrassAmp2 t n
    unfold weierstrassAmp2 weierstrassAmplitude weierstrassFreq
    rw [show npow 2 pi = pi * pi from by
          show pi * (pi * npow 0 pi) = pi * pi; rw [show npow 0 pi = 1 from rfl]; mach_ring,
        show n * 2 = n + n from by omega, npow_add]
    mach_ring
  rwa [heq] at h

/-! ## §3 — Domination of `weierstrassTerm1` by `weierstrassAmp1` -/

private theorem wtbt_neg_ring (a b : Real) : -a * b = -(a * b) := by mach_mpoly [a, b]
private theorem wtbt_one_mul_ring (a : Real) : 1 * a = a := by mach_mpoly [a]

theorem weierstrassTerm1_dom (t : Real) (n : Nat) (x : Real) :
    abs (weierstrassTerm1 t n x) ≤ weierstrassAmp1 t n := by
  unfold weierstrassTerm1 weierstrassAmp1
  rw [abs_mul, abs_of_nonneg (weierstrassAmplitude_nonneg t n),
      wtbt_neg_ring (Real.sin (weierstrassFreq n * x)) (weierstrassFreq n),
      abs_neg, abs_mul, abs_of_nonneg (le_of_lt (weierstrassFreq_pos n))]
  have hstep := mul_le_mul_of_nonneg_right (abs_sin_le_one (weierstrassFreq n * x)) (le_of_lt (weierstrassFreq_pos n))
  rw [wtbt_one_mul_ring (weierstrassFreq n)] at hstep
  exact mul_le_mul_of_nonneg_left hstep (weierstrassAmplitude_nonneg t n)

/-! ## §4 — `D_N` Lipschitz bound, via `sin_lipschitz` + `weierstrassAmp2` (no 2nd derivative) -/

private theorem wtbt_distrib_ring (A B C : Real) : A * C + B * C = (A + B) * C := by mach_mpoly [A, B, C]

private theorem wtbt_diff_ring (A K sc sx : Real) :
    A * (-sc * K) - A * (-sx * K) = (A * K) * (sx - sc) := by mach_mpoly [A, K, sc, sx]

theorem weierstrassTerm1_lipschitz (t : Real) (n : Nat) (c x : Real) :
    abs (weierstrassTerm1 t n c - weierstrassTerm1 t n x) ≤ weierstrassAmp2 t n * abs (c - x) := by
  unfold weierstrassTerm1
  rw [wtbt_diff_ring (weierstrassAmplitude t n) (weierstrassFreq n)
        (Real.sin (weierstrassFreq n * c)) (Real.sin (weierstrassFreq n * x)),
      abs_mul]
  have hAK_nn : 0 ≤ weierstrassAmplitude t n * weierstrassFreq n :=
    mul_nonneg (weierstrassAmplitude_nonneg t n) (le_of_lt (weierstrassFreq_pos n))
  rw [abs_of_nonneg hAK_nn]
  have hstep1 : abs (Real.sin (weierstrassFreq n * x) - Real.sin (weierstrassFreq n * c))
      ≤ abs (weierstrassFreq n * x - weierstrassFreq n * c) := sin_lipschitz _ _
  have hstep2 : weierstrassFreq n * x - weierstrassFreq n * c = weierstrassFreq n * (x - c) := by
    mach_mpoly [weierstrassFreq n, x, c]
  rw [hstep2, abs_mul, abs_of_nonneg (le_of_lt (weierstrassFreq_pos n))] at hstep1
  have hstep3 := mul_le_mul_of_nonneg_left hstep1 hAK_nn
  have heq : weierstrassAmplitude t n * weierstrassFreq n * (weierstrassFreq n * abs (x - c))
      = weierstrassAmp2 t n * abs (x - c) := by
    unfold weierstrassAmp2; mach_mpoly [weierstrassAmplitude t n, weierstrassFreq n, abs (x - c)]
  rw [heq, show abs (x - c) = abs (c - x) from abs_sub_comm x c] at hstep3
  exact hstep3

private theorem wtbt_const_mul_partialSum (f : Nat → Real) (C : Real) :
    ∀ N, partialSum (fun i => f i * C) N = partialSum f N * C
  | 0 => by show (0:Real) = 0 * C; mach_ring
  | k + 1 => by
      rw [partialSum_succ, partialSum_succ, wtbt_const_mul_partialSum f C k]
      exact wtbt_distrib_ring (partialSum f k) (f k) C

theorem weierstrassD_N_lipschitz {t : Real} {N : Nat} {SumA2 : Real}
    (hSumA2_ub : ∀ k, partialSum (weierstrassAmp2 t) k ≤ SumA2) (c x : Real) :
    abs (partialSum (fun i => weierstrassTerm1 t i c) N - partialSum (fun i => weierstrassTerm1 t i x) N)
      ≤ SumA2 * abs (c - x) := by
  rw [← partialSum_sub]
  refine le_trans (abs_partialSum_le _ N) ?_
  have h1 : partialSum (fun i => abs (weierstrassTerm1 t i c - weierstrassTerm1 t i x)) N
      ≤ partialSum (fun i => weierstrassAmp2 t i * abs (c - x)) N :=
    partialSum_le_of_le (fun i => weierstrassTerm1_lipschitz t i c x) N
  rw [wtbt_const_mul_partialSum (weierstrassAmp2 t) (abs (c - x)) N] at h1
  have h3 : partialSum (weierstrassAmp2 t) N * abs (c - x) ≤ SumA2 * abs (c - x) :=
    mul_le_mul_of_nonneg_right (hSumA2_ub N) (abs_nonneg _)
  exact le_trans h1 h3

/-! ## §5 — MVT-based estimates -/

/-- MVT applied to the finite partial sum `S_N`, `x < y` case: the exact difference-quotient
identity, with the witness point `c` provably between `x` and `y`. -/
theorem weierstrassSN_mvt_lt (t : Real) (N : Nat) {x y : Real} (hxy : x < y) :
    ∃ c : Real, x < c ∧ c < y ∧
      partialSum (fun i => weierstrassTerm t i y) N - partialSum (fun i => weierstrassTerm t i x) N
        = partialSum (fun i => weierstrassTerm1 t i c) N * (y - x) := by
  obtain ⟨c, f', hac, hcb, hderiv, heqmvt⟩ := mean_value_theorem_ct
    (fun z => partialSum (fun i => weierstrassTerm t i z) N) x y hxy
    (fun z _ _ => ⟨partialSum (fun i => weierstrassTerm1 t i z) N,
      partialSum_hasDerivAt (weierstrassTerm_hasDerivAt' t) N z⟩)
  have hunique : f' = partialSum (fun i => weierstrassTerm1 t i c) N :=
    HasDerivAt_unique _ _ _ _ hderiv (partialSum_hasDerivAt (weierstrassTerm_hasDerivAt' t) N c)
  exact ⟨c, hac, hcb, by rw [← hunique]; exact heqmvt⟩

/-- MVT-derived Lipschitz bound: if `g'` is uniformly `≤ B` in magnitude everywhere, `g` itself is
`B`-Lipschitz between any `x < y`. Used for the block sums `S_n - S_N` in the tail estimate. -/
theorem mvt_bound_lt {g g' : Real → Real} (hderiv : ∀ z, HasDerivAt g (g' z) z)
    {x y : Real} (hxy : x < y) {B : Real} (hB : ∀ z, abs (g' z) ≤ B) :
    abs (g y - g x) ≤ B * (y - x) := by
  obtain ⟨c, f', hac, hcb, hderivc, heqmvt⟩ :=
    mean_value_theorem_ct g x y hxy (fun z _ _ => ⟨g' z, hderiv z⟩)
  have hunique : f' = g' c := HasDerivAt_unique _ _ _ _ hderivc (hderiv c)
  rw [hunique] at heqmvt
  rw [heqmvt, abs_mul, abs_of_nonneg (le_of_lt (sub_pos_of_lt hxy))]
  exact mul_le_mul_of_nonneg_right (hB c) (le_of_lt (sub_pos_of_lt hxy))

private theorem wtbt_abs_sub_eq_of_lt {x y : Real} (h : x < y) : abs (y - x) = y - x :=
  abs_of_nonneg (le_of_lt (sub_pos_of_lt h))

private theorem wtbt_neg_sub_ring (a b : Real) : -(a - b) = b - a := by mach_mpoly [a, b]

private theorem wtbt_abs_sub_eq_of_gt {x y : Real} (h : y < x) : abs (y - x) = x - y := by
  rw [show y - x = -(x - y) from (wtbt_neg_sub_ring x y).symm, abs_neg]
  exact wtbt_abs_sub_eq_of_lt h

private theorem wtbt_x_lt_c_le : ∀ {x c y : Real}, x < c → c < y → abs (c - x) ≤ abs (y - x) := by
  intro x c y hxc hcy
  have h1 : c - x ≤ y - x := sub_le_sub_right (le_of_lt_r hcy) x
  have h2 : (0:Real) ≤ c - x := le_of_lt (sub_pos_of_lt hxc)
  have h3 : (0:Real) ≤ y - x := le_of_lt (sub_pos_of_lt (lt_trans_ax hxc hcy))
  rwa [abs_of_nonneg h2, abs_of_nonneg h3]

/-- Order-independent version of `mvt_bound_lt`: works for any `x ≠ y`. -/
theorem mvt_bound {g g' : Real → Real} (hderiv : ∀ z, HasDerivAt g (g' z) z)
    {x y : Real} (hxy : x ≠ y) {B : Real} (hB : ∀ z, abs (g' z) ≤ B) :
    abs (g y - g x) ≤ B * abs (y - x) := by
  rcases lt_total x y with hlt | heq | hgt
  · rw [wtbt_abs_sub_eq_of_lt hlt]; exact mvt_bound_lt hderiv hlt hB
  · exact absurd heq hxy
  · have h := mvt_bound_lt hderiv hgt hB
    rw [show g x - g y = -(g y - g x) from (wtbt_neg_sub_ring (g y) (g x)).symm, abs_neg] at h
    rwa [wtbt_abs_sub_eq_of_gt hgt]

/-- Order-independent version of `weierstrassSN_mvt_lt`: works for any `x ≠ y`. -/
theorem weierstrassSN_mvt (t : Real) (N : Nat) {x y : Real} (hxy : x ≠ y) :
    ∃ c : Real, abs (c - x) ≤ abs (y - x) ∧
      partialSum (fun i => weierstrassTerm t i y) N - partialSum (fun i => weierstrassTerm t i x) N
        = partialSum (fun i => weierstrassTerm1 t i c) N * (y - x) := by
  rcases lt_total x y with hlt | heq | hgt
  · obtain ⟨c, hxc, hcy, heqmvt⟩ := weierstrassSN_mvt_lt t N hlt
    exact ⟨c, wtbt_x_lt_c_le hxc hcy, heqmvt⟩
  · exact absurd heq hxy
  · obtain ⟨c, hyc, hcx, heqmvt⟩ := weierstrassSN_mvt_lt t N hgt
    refine ⟨c, ?_, ?_⟩
    · have h1 : abs (x - c) = x - c := wtbt_abs_sub_eq_of_lt hcx
      have h2 : abs (x - y) = x - y := wtbt_abs_sub_eq_of_lt hgt
      have h3 : x - c ≤ x - y := sub_le_sub_left (le_of_lt_r hyc) x
      rw [show abs (c - x) = abs (x - c) from abs_sub_comm c x, h1,
          show abs (y - x) = abs (x - y) from abs_sub_comm y x, h2]
      exact h3
    · have hstep : -(partialSum (fun i => weierstrassTerm t i x) N - partialSum (fun i => weierstrassTerm t i y) N)
          = -(partialSum (fun i => weierstrassTerm1 t i c) N * (x - y)) := by rw [heqmvt]
      rwa [wtbt_neg_sub_ring (partialSum (fun i => weierstrassTerm t i x) N)
            (partialSum (fun i => weierstrassTerm t i y) N),
          show -(partialSum (fun i => weierstrassTerm1 t i c) N * (x - y))
            = partialSum (fun i => weierstrassTerm1 t i c) N * (y - x) from by
            mach_mpoly [partialSum (fun i => weierstrassTerm1 t i c) N, x, y]] at hstep

/-! ## §6 — The payoff -/

private theorem wtbt_regroup (wy wx sny snx sNcy sNcx : Real) :
    (wy - sNcy) - (wx - sNcx) = (wy - sny - (wx - snx)) + (sny - sNcy - (snx - sNcx)) := by
  mach_mpoly [wy, wx, sny, snx, sNcy, sNcx]

/-- **Tail estimate**: the difference `(W(y)-S_Nc(y)) - (W(x)-S_Nc(x))` is bounded by `B*(y-x)`,
where `B` uniformly bounds the derivative-series block from `Nc` onward. Combines MVT on the
finite block `S_n - S_Nc` (n≥Nc) with `hW_uniform`'s explicit tail control, via
`le_of_forall_pos_lt_add` to pass to the limit `n→∞`. -/
theorem weierstrassTail_diff_le (t : Real)
    (W : Real → Real)
    (hW_uniform : ∀ ε : Real, 0 < ε → ∃ N, ∀ n, N ≤ n → ∀ z,
      abs (W z - partialSum (fun i => weierstrassTerm t i z) n) < ε)
    (Nc : Nat) {B : Real}
    (hB : ∀ n, Nc ≤ n → ∀ z, abs (partialSum (fun i => weierstrassTerm1 t i z) n
      - partialSum (fun i => weierstrassTerm1 t i z) Nc) ≤ B)
    {x y : Real} (hxy : x ≠ y) :
    abs ((W y - partialSum (fun i => weierstrassTerm t i y) Nc)
      - (W x - partialSum (fun i => weierstrassTerm t i x) Nc)) ≤ B * abs (y - x) := by
  apply le_of_forall_pos_lt_add
  intro η hη
  have hη2 : 0 < η / (1 + 1) := div_pos_of_pos_pos hη h11pos
  obtain ⟨N'', hN''⟩ := hW_uniform (η / (1 + 1)) hη2
  obtain ⟨n, hnNc, hnN''⟩ : ∃ n, Nc ≤ n ∧ N'' ≤ n :=
    ⟨Nc + N'', Nat.le_add_right Nc N'', Nat.le_add_left N'' Nc⟩
  have hderiv_diff : ∀ z, HasDerivAt
      (fun w => partialSum (fun i => weierstrassTerm t i w) n - partialSum (fun i => weierstrassTerm t i w) Nc)
      (partialSum (fun i => weierstrassTerm1 t i z) n - partialSum (fun i => weierstrassTerm1 t i z) Nc) z :=
    fun z => HasDerivAt_sub _ _ _ _ z (partialSum_hasDerivAt (weierstrassTerm_hasDerivAt' t) n z)
      (partialSum_hasDerivAt (weierstrassTerm_hasDerivAt' t) Nc z)
  have hBbound : ∀ z, abs (partialSum (fun i => weierstrassTerm1 t i z) n
      - partialSum (fun i => weierstrassTerm1 t i z) Nc) ≤ B := fun z => hB n hnNc z
  have hmvt := mvt_bound hderiv_diff hxy hBbound
  have hWn_y : abs (W y - partialSum (fun i => weierstrassTerm t i y) n) < η / (1 + 1) := hN'' n hnN'' y
  have hWn_x : abs (W x - partialSum (fun i => weierstrassTerm t i x) n) < η / (1 + 1) := hN'' n hnN'' x
  have hregroup := wtbt_regroup (W y) (W x) (partialSum (fun i => weierstrassTerm t i y) n)
    (partialSum (fun i => weierstrassTerm t i x) n) (partialSum (fun i => weierstrassTerm t i y) Nc)
    (partialSum (fun i => weierstrassTerm t i x) Nc)
  rw [hregroup]
  have htri := abs_add
    (W y - partialSum (fun i => weierstrassTerm t i y) n - (W x - partialSum (fun i => weierstrassTerm t i x) n))
    (partialSum (fun i => weierstrassTerm t i y) n - partialSum (fun i => weierstrassTerm t i y) Nc
      - (partialSum (fun i => weierstrassTerm t i x) n - partialSum (fun i => weierstrassTerm t i x) Nc))
  refine lt_of_le_of_lt htri ?_
  have hpart1 := abs_sub_le_local (W y - partialSum (fun i => weierstrassTerm t i y) n)
    (W x - partialSum (fun i => weierstrassTerm t i x) n)
  have hpart1' : abs (W y - partialSum (fun i => weierstrassTerm t i y) n
      - (W x - partialSum (fun i => weierstrassTerm t i x) n)) < η / (1 + 1) + η / (1 + 1) :=
    lt_of_le_of_lt hpart1 (add_lt_add_local hWn_y hWn_x)
  have heta_eq : η / (1 + 1) + η / (1 + 1) = η := by
    rw [div_add_div_same h11ne, show η + η = (1 + 1) * η from by mach_ring]
    exact mul_div_cancel_left' h11ne
  have hpart1'' : abs (W y - partialSum (fun i => weierstrassTerm t i y) n
      - (W x - partialSum (fun i => weierstrassTerm t i x) n)) < η := by rwa [heta_eq] at hpart1'
  have hstepA := add_lt_add_right_local hpart1''
    (abs (partialSum (fun i => weierstrassTerm t i y) n - partialSum (fun i => weierstrassTerm t i y) Nc
      - (partialSum (fun i => weierstrassTerm t i x) n - partialSum (fun i => weierstrassTerm t i x) Nc)))
  have hstepB := add_le_add_left hmvt η
  have hfinal := lt_of_lt_of_le hstepA hstepB
  rwa [show η + B * abs (y - x) = B * abs (y - x) + η from by mach_mpoly [η, B, abs (y - x)]] at hfinal

private theorem wtbt_mvt_factor (Dc Dx X : Real) : Dc * X - Dx * X = (Dc - Dx) * X := by
  mach_mpoly [Dc, Dx, X]

private theorem wtbt_final_regroup (a b c d e f : Real) :
    a - b - f = (a - c - (b - d)) + ((c - d - e) + (e - f)) := by
  mach_mpoly [a, b, c, d, e, f]

/-- **`x < y` case of the full estimate**: `abs(W y - W x - D x*(y-x)) ≤ ε*(y-x)`. -/
theorem weierstrass_deriv_estimate (t : Real) (ht : 0 < t) (W D : Real → Real)
    (hW_uniform : ∀ ε : Real, 0 < ε → ∃ N, ∀ n, N ≤ n → ∀ z,
      abs (W z - partialSum (fun i => weierstrassTerm t i z) n) < ε)
    (hDspec : ∀ z, ∀ ε : Real, 0 < ε → ∃ N, ∀ n, N ≤ n →
      abs (D z - partialSum (fun i => weierstrassTerm1 t i z) n) < ε)
    {SumA1 SumA2 : Real}
    (hSumA1_ub : ∀ k, partialSum (weierstrassAmp1 t) k ≤ SumA1)
    (hSumA1_lub : ∀ s', (∀ k, partialSum (weierstrassAmp1 t) k ≤ s') → SumA1 ≤ s')
    (hSumA2_ub : ∀ k, partialSum (weierstrassAmp2 t) k ≤ SumA2)
    {x : Real} {ε : Real} (hε : 0 < ε) {δ : Real}
    (hδSumA2 : SumA2 * δ ≤ ε / (1 + 1 + 1)) (hδpos : 0 < δ)
    {y : Real} (hxy : x ≠ y) (hyδ : abs (y - x) < δ) :
    abs (W y - W x - D x * (y - x)) ≤ ε * abs (y - x) := by
  have h3pos : (0:Real) < 1 + 1 + 1 := by
    have h1 : (0:Real) < 1 + 1 := h11pos
    exact add_pos h1 one_pos
  have hε3 : 0 < ε / (1 + 1 + 1) := div_pos_of_pos_pos hε h3pos
  obtain ⟨Na, hNa⟩ := tail_lt_of_sup (weierstrassAmp1_nonneg t) hSumA1_lub hε3
  obtain ⟨Nd, hNd⟩ := hDspec x (ε / (1 + 1 + 1)) hε3
  obtain ⟨Nc, hNcNa, hNcNd⟩ : ∃ Nc, Na ≤ Nc ∧ Nd ≤ Nc :=
    ⟨Na + Nd, Nat.le_add_right Na Nd, Nat.le_add_left Nd Na⟩
  have hAyx : (0:Real) ≤ abs (y - x) := abs_nonneg _
  -- term 2: tail bound
  have hB : ∀ n, Nc ≤ n → ∀ z, abs (partialSum (fun i => weierstrassTerm1 t i z) n
      - partialSum (fun i => weierstrassTerm1 t i z) Nc) ≤ ε / (1 + 1 + 1) := by
    intro n hn z
    have hblock := partialSum_block_le (fun i => weierstrassTerm1_dom t i z) (weierstrassAmp1_nonneg t) hn hSumA1_ub
    have htail : SumA1 - partialSum (weierstrassAmp1 t) Nc < ε / (1 + 1 + 1) := hNa Nc hNcNa
    exact le_trans hblock (le_of_lt htail)
  have hterm2 := weierstrassTail_diff_le t W hW_uniform Nc hB hxy
  -- term 1: MVT + Lipschitz
  obtain ⟨c, hcx_le, heqmvt⟩ := weierstrassSN_mvt t Nc hxy
  have hlip := weierstrassD_N_lipschitz (N := Nc) hSumA2_ub c x
  have hterm1eq : partialSum (fun i => weierstrassTerm t i y) Nc - partialSum (fun i => weierstrassTerm t i x) Nc
      - partialSum (fun i => weierstrassTerm1 t i x) Nc * (y - x)
      = (partialSum (fun i => weierstrassTerm1 t i c) Nc - partialSum (fun i => weierstrassTerm1 t i x) Nc) * (y - x) := by
    rw [heqmvt]
    exact wtbt_mvt_factor (partialSum (fun i => weierstrassTerm1 t i c) Nc)
      (partialSum (fun i => weierstrassTerm1 t i x) Nc) (y - x)
  have hterm1 : abs (partialSum (fun i => weierstrassTerm t i y) Nc - partialSum (fun i => weierstrassTerm t i x) Nc
      - partialSum (fun i => weierstrassTerm1 t i x) Nc * (y - x)) ≤ SumA2 * abs (y - x) * abs (y - x) := by
    rw [hterm1eq, abs_mul]
    have h1 := mul_le_mul_of_nonneg_right hlip hAyx
    have h2 : SumA2 * abs (c - x) * abs (y - x) ≤ SumA2 * abs (y - x) * abs (y - x) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcx_le
        (show (0:Real) ≤ SumA2 from hSumA2_ub 0)) hAyx
    exact le_trans h1 h2
  have hδyx : abs (y - x) ≤ δ := le_of_lt hyδ
  have hterm1' : SumA2 * abs (y - x) * abs (y - x) ≤ (ε / (1 + 1 + 1)) * abs (y - x) := by
    have h1 : SumA2 * abs (y - x) ≤ SumA2 * δ := mul_le_mul_of_nonneg_left hδyx
      (show (0:Real) ≤ SumA2 from hSumA2_ub 0)
    have h2 : SumA2 * abs (y - x) ≤ ε / (1 + 1 + 1) := le_trans h1 hδSumA2
    exact mul_le_mul_of_nonneg_right h2 hAyx
  have hterm1final := le_trans hterm1 hterm1'
  -- combine
  have hDx_eq : D x * (y - x) - partialSum (fun i => weierstrassTerm1 t i x) Nc * (y - x)
      = (D x - partialSum (fun i => weierstrassTerm1 t i x) Nc) * (y - x) :=
    wtbt_mvt_factor (D x) (partialSum (fun i => weierstrassTerm1 t i x) Nc) (y - x)
  have hDtail : abs (D x - partialSum (fun i => weierstrassTerm1 t i x) Nc) < ε / (1 + 1 + 1) := hNd Nc hNcNd
  have hDtail' : abs (D x * (y - x) - partialSum (fun i => weierstrassTerm1 t i x) Nc * (y - x))
      ≤ (ε / (1 + 1 + 1)) * abs (y - x) := by
    rw [hDx_eq, abs_mul]
    exact mul_le_mul_of_nonneg_right (le_of_lt hDtail) hAyx
  have hDtail'' : abs (partialSum (fun i => weierstrassTerm1 t i x) Nc * (y - x) - D x * (y - x))
      ≤ (ε / (1 + 1 + 1)) * abs (y - x) := by rwa [abs_sub_comm] at hDtail'
  have hbig : abs (W y - W x - D x * (y - x)) ≤
      abs (W y - partialSum (fun i => weierstrassTerm t i y) Nc - (W x - partialSum (fun i => weierstrassTerm t i x) Nc))
      + (abs (partialSum (fun i => weierstrassTerm t i y) Nc - partialSum (fun i => weierstrassTerm t i x) Nc
        - partialSum (fun i => weierstrassTerm1 t i x) Nc * (y - x))
      + abs (partialSum (fun i => weierstrassTerm1 t i x) Nc * (y - x) - D x * (y - x))) := by
    have heq := wtbt_final_regroup (W y) (W x) (partialSum (fun i => weierstrassTerm t i y) Nc)
      (partialSum (fun i => weierstrassTerm t i x) Nc) (partialSum (fun i => weierstrassTerm1 t i x) Nc * (y - x))
      (D x * (y - x))
    rw [heq]
    exact le_trans (abs_add _ _) (add_le_add_left (abs_add _ _) _)
  refine le_trans hbig ?_
  have hcomb1 := add_le_add_both hterm1final hDtail''
  have hcomb2 := add_le_add_both hterm2 hcomb1
  have heq2 : ε / (1 + 1 + 1) * abs (y - x) + (ε / (1 + 1 + 1) * abs (y - x) + ε / (1 + 1 + 1) * abs (y - x))
      = ε * abs (y - x) := by
    rw [show ε / (1+1+1) * abs (y-x) + (ε / (1+1+1) * abs (y-x) + ε / (1+1+1) * abs (y-x))
          = (ε/(1+1+1) + ε/(1+1+1) + ε/(1+1+1)) * abs (y - x) from by
        mach_mpoly [ε / (1+1+1), abs (y - x)],
        div_add_div_same (ne_of_gt h3pos), div_add_div_same (ne_of_gt h3pos),
        show ε + ε + ε = (1+1+1) * ε from by mach_ring, mul_div_cancel_left' (ne_of_gt h3pos)]
  rwa [heq2] at hcomb2

/-- **`W` is genuinely differentiable everywhere**, with an explicit derivative `D` equal to the
already-summable `k=1` term series' actual sum. -/
theorem weierstrass_sum_hasDerivAt (t : Real) (ht : 0 < t) :
    ∃ W D : Real → Real,
      (∀ ε : Real, 0 < ε → ∃ N, ∀ n, N ≤ n → ∀ x,
        abs (W x - partialSum (fun i => weierstrassTerm t i x) n) < ε)
      ∧ (∀ x0, ContinuousAt W x0)
      ∧ ∀ x0, HasDerivAt W (D x0) x0 := by
  obtain ⟨W, hW_uniform, hW_cont⟩ := weierstrass_sum_continuous t ht
  obtain ⟨SumA1, hSumA1_ub, hSumA1_lub⟩ :=
    series_sum_exists_of_bounded (weierstrassAmp1_nonneg t) (weierstrassAmp1_hasBoundedPartialSums t ht)
  obtain ⟨SumA2, hSumA2_ub, _⟩ :=
    series_sum_exists_of_bounded (weierstrassAmp2_nonneg t) (weierstrassAmp2_hasBoundedPartialSums t ht)
  have hDex : ∀ x, ∃ s : Real, ∀ ε : Real, 0 < ε → ∃ N, ∀ n, N ≤ n →
      abs (s - partialSum (fun i => weierstrassTerm1 t i x) n) < ε :=
    fun x => exists_pointwise_sum_of_dominated (weierstrassAmp1_nonneg t)
      (weierstrassAmp1_hasBoundedPartialSums t ht) (fun n => weierstrassTerm1_dom t n x)
  let D : Real → Real := fun x => Classical.choose (hDex x)
  have hDspec : ∀ x, ∀ ε : Real, 0 < ε → ∃ N, ∀ n, N ≤ n →
      abs (D x - partialSum (fun i => weierstrassTerm1 t i x) n) < ε :=
    fun x => Classical.choose_spec (hDex x)
  refine ⟨W, D, hW_uniform, hW_cont, fun x => ?_⟩
  apply HasDerivAt_of_eps_delta
  intro ε hε
  have hSumA2nn : (0:Real) ≤ SumA2 := hSumA2_ub 0
  have h3pos : (0:Real) < 1 + 1 + 1 := by
    have h1 : (0:Real) < 1 + 1 := h11pos
    exact add_pos h1 one_pos
  have hε3 : 0 < ε / (1 + 1 + 1) := div_pos_of_pos_pos hε h3pos
  have hSumA2_lt : SumA2 < SumA2 + 1 := by
    have h := add_lt_add_left one_pos SumA2
    rwa [add_zero] at h
  have hSumA2_1_pos : (0:Real) < SumA2 + 1 := lt_of_le_of_lt hSumA2nn hSumA2_lt
  have hSumA2_le : SumA2 ≤ SumA2 + 1 := le_of_lt hSumA2_lt
  let δ : Real := (ε / (1 + 1 + 1)) / (SumA2 + 1)
  have hδpos : 0 < δ := div_pos_of_pos_pos hε3 hSumA2_1_pos
  have hδSumA2 : SumA2 * δ ≤ ε / (1 + 1 + 1) := by
    show SumA2 * ((ε / (1 + 1 + 1)) / (SumA2 + 1)) ≤ ε / (1 + 1 + 1)
    have h1 : SumA2 * ((ε / (1 + 1 + 1)) / (SumA2 + 1)) ≤ (SumA2 + 1) * ((ε / (1 + 1 + 1)) / (SumA2 + 1)) :=
      mul_le_mul_of_nonneg_right hSumA2_le (le_of_lt (div_pos_of_pos_pos hε3 hSumA2_1_pos))
    rwa [mul_div_cancel_left (ne_of_gt hSumA2_1_pos)] at h1
  refine ⟨δ, hδpos, fun y hy => ?_⟩
  rcases Classical.em (x = y) with heq | hne
  · rw [← heq, show x - x = (0:Real) from by mach_ring,
        show W x - W x - D x * (0:Real) = (0:Real) from by mach_mpoly [W x, D x],
        show abs (0:Real) = 0 from abs_of_nonneg (le_refl 0), show ε * (0:Real) = 0 from by mach_ring]
    exact le_refl 0
  · exact weierstrass_deriv_estimate t ht W D hW_uniform hDspec hSumA1_ub hSumA1_lub hSumA2_ub hε
      hδSumA2 hδpos hne hy

end Real
end MachLib
