import MachLib.Iteration
import MachLib.EMLWeierstrassTermBound

/-!
# Summability — bounded partial sums via MachLib's completeness axiom

`EMLWeierstrassTermBound` proved a single-term magnitude bound and explicitly flagged what it
does NOT do: connect to an actual infinite series. MachLib has no `tsum`/`Summable`/Cauchy-sequence
theory anywhere in the library (confirmed by grep before starting this file) — but it DOES have a
genuine completeness axiom, `sup_exists` (`Basic.lean`), already load-bearing for
`IntermediateValue.lean` and `ExtremeValueAttainment.lean`. That is enough to build series
convergence the Monotone-Convergence-Theorem way (bounded increasing partial sums have a
supremum) without ever constructing Cauchy sequences.

## What this file ships

  - `partialSum f n` — the finite sum `f 0 + f 1 + … + f (n-1)`, defined by plain `Nat` recursion
    (same idiom as `Iteration.geom` and `FinanceAmortization.partialSum`, generalized from `Int`
    to `Real`).
  - `HasBoundedPartialSums f` — the partial sums of `f` are bounded above (a `Prop`, via
    `BoundedAbove` from `Basic.lean`).
  - `series_sum_exists_of_bounded` — for `f` termwise nonneg with bounded partial sums, a genuine
    supremum `s` exists with `∀ n, partialSum f n ≤ s` and `s` least among such bounds. This IS a
    sum in the least-upper-bound sense (matches how nonneg `tsum` is characterized via `iSup` in
    completeness-based real analysis), constructed directly from `sup_exists` — no separate
    Cauchy-completeness development needed.
  - `hasBoundedPartialSums_of_eventually_le_geom` — the comparison/M-test step: if `f` is
    eventually (past some `N0`) termwise `≤` a genuine geometric sequence `npow n r` (`0≤r<1`),
    `f` has bounded partial sums. Built on `Iteration.geom`'s existing division-free bound
    `geom_scaled_le_one`.
  - `term_eventually_le_geometric` — upgrades `EMLWeierstrassTermBound.exp_beats_geometric`'s
    `< 1` eventually to `< npow n r` eventually for any fixed `0<r<1`, by the same
    exp-dominates-any-polynomial-rate argument applied to `R/r` instead of `R`.
  - `weierstrass_term_hasBoundedPartialSums` — the payoff: for every fixed `t>0` and derivative
    order `k`, the ACTUAL term sequence from `weierstrass_term_eventually_lt_one` is summable
    (bounded partial sums), not just eventually small term-by-term.

## What this does NOT do

**Not the full EML Weierstrass theorem, still.** This proves the derivative-series COEFFICIENTS
are summable — the exact hypothesis a Weierstrass M-test needs. It does not: (1) attach these
coefficients to the actual `Real.cos` series (no `Real.cos(bⁿπx)` appears here, only the bare
magnitude sequence), (2) prove uniform convergence in `x`, or (3) prove term-by-term
differentiation is valid (interchanging `Σ` and `d/dx`, the step that would actually deliver
`C^∞`/real-analyticity). Each of those is a further, separate piece of analysis on top of this
one. Matches this whole program's discipline of reporting exactly how far the chain reaches.

`sorryAx`-free, Mathlib-free, no new axioms beyond what MachLib already has (`sup_exists` from
`Basic.lean`, already trusted throughout `IntermediateValue.lean` / `ExtremeValueAttainment.lean`).
-/

namespace MachLib
namespace Real

/-! ## §1 — Finite partial sums over `Nat → Real` -/

/-- Finite partial sum `f 0 + f 1 + … + f (n-1)`. Real-valued generalization of
`FinanceAmortization.partialSum` (which is `Int`-valued), same recursion shape as `Iteration.geom`. -/
noncomputable def partialSum (f : Nat → Real) : Nat → Real
  | 0 => 0
  | n + 1 => partialSum f n + f n

theorem partialSum_succ (f : Nat → Real) (n : Nat) :
    partialSum f (n + 1) = partialSum f n + f n := rfl

theorem partialSum_nonneg {f : Nat → Real} (hf : ∀ n, 0 ≤ f n) : ∀ n, 0 ≤ partialSum f n
  | 0 => le_refl 0
  | n + 1 => by
      rw [partialSum_succ]
      have h := add_le_add_both (partialSum_nonneg hf n) (hf n)
      rwa [show (0 : Real) + 0 = 0 from by mach_ring] at h

theorem partialSum_le_succ {f : Nat → Real} (hf : ∀ n, 0 ≤ f n) (n : Nat) :
    partialSum f n ≤ partialSum f (n + 1) := by
  rw [partialSum_succ]
  have h := add_le_add_both (le_refl (partialSum f n)) (hf n)
  rwa [show partialSum f n + 0 = partialSum f n from by mach_ring] at h

/-- Gap-induction monotonicity (same style as `iter_exp_strict_lt`'s difference argument):
`partialSum f m ≤ partialSum f (m+k)` for any extra gap `k`. -/
theorem partialSum_mono_gap {f : Nat → Real} (hf : ∀ n, 0 ≤ f n) (m : Nat) :
    ∀ k, partialSum f m ≤ partialSum f (m + k)
  | 0 => le_refl _
  | k + 1 => le_trans (partialSum_mono_gap hf m k) (partialSum_le_succ hf (m + k))

theorem partialSum_mono {f : Nat → Real} (hf : ∀ n, 0 ≤ f n) {m n : Nat} (hmn : m ≤ n) :
    partialSum f m ≤ partialSum f n := by
  obtain ⟨k, hk⟩ := Nat.le.dest hmn
  rw [← hk]
  exact partialSum_mono_gap hf m k

/-! ## §2 — A second recursive characterization of `geom`, peeling the LAST term instead of
the first (`Iteration.geom_succ` peels the first: `geom L (n+1) = 1 + L * geom L n`). Needed
to align a shifted partial-sum tail with the geometric bound below. -/

private theorem gan_ring (L X Y : Real) : 1 + L * (X + Y) = (1 + L * X) + L * Y := by
  mach_mpoly [L, X, Y]

theorem geom_add_npow (L : Real) : ∀ m : Nat, geom L (m + 1) = geom L m + npow m L
  | 0 => by
      show geom L 1 = geom L 0 + npow 0 L
      rw [geom_succ, show geom L 0 = 0 from rfl]
      show (1 : Real) + L * 0 = 0 + npow 0 L
      show (1 : Real) + L * 0 = 0 + 1
      mach_ring
  | m + 1 => by
      have ih : geom L (m + 1) = geom L m + npow m L := geom_add_npow L m
      show geom L (m + 1 + 1) = geom L (m + 1) + npow (m + 1) L
      rw [geom_succ, ih, gan_ring L (geom L m) (npow m L), ← geom_succ L m, ← npow_succ m L, ← ih]

/-! ## §3 — Shifted partial-sum tail bound: past a threshold `N0` where `f` is eventually
`≤` a geometric sequence, the tail of `partialSum f` is controlled by `geom`. -/

private theorem ptl_ring (a b c d : Real) : (a + b * c) + b * d = a + b * (c + d) := by
  mach_mpoly [a, b, c, d]

theorem partialSum_tail_le_geom
    {f : Nat → Real} {N0 : Nat} {r : Real} (hN0 : ∀ n, N0 ≤ n → f n ≤ npow n r) :
    ∀ m, partialSum f (N0 + m) ≤ partialSum f N0 + npow N0 r * geom r m
  | 0 => by
      show partialSum f (N0 + 0) ≤ partialSum f N0 + npow N0 r * geom r 0
      rw [Nat.add_zero, show geom r 0 = 0 from rfl]
      rw [show partialSum f N0 + npow N0 r * 0 = partialSum f N0 from by mach_ring]
      exact le_refl _
  | m + 1 => by
      have ih := partialSum_tail_le_geom hN0 m
      have hbound : f (N0 + m) ≤ npow (N0 + m) r := hN0 (N0 + m) (Nat.le_add_right N0 m)
      have hnpow_split : npow (N0 + m) r = npow N0 r * npow m r := npow_add r N0 m
      have h1 : partialSum f (N0 + m) + f (N0 + m)
          ≤ (partialSum f N0 + npow N0 r * geom r m) + npow (N0 + m) r :=
        add_le_add_both ih hbound
      rw [hnpow_split, ptl_ring (partialSum f N0) (npow N0 r) (geom r m) (npow m r),
          ← geom_add_npow r m] at h1
      have hidx : N0 + (m + 1) = N0 + m + 1 := by omega
      rw [hidx, partialSum_succ]
      exact h1

/-! ## §4 — Uniform bound on `geom` (division form) -/

private theorem le_div_of_mul_le_pos_local {a b c : Real} (h : b * a ≤ c) (hb : 0 < b) :
    a ≤ c / b := by
  have hbne : b ≠ 0 := ne_of_gt hb
  have hbinv_pos : 0 < 1 / b := div_pos_of_pos_pos one_pos hb
  have h2 : b * a * (1 / b) ≤ c * (1 / b) := mul_le_mul_of_nonneg_right h (le_of_lt hbinv_pos)
  have h3 : b * a * (1 / b) = a * (b * (1 / b)) := by mach_ring
  rw [h3, mul_inv b hbne, mul_one_ax] at h2
  rwa [← div_def c b hbne] at h2

theorem geom_le_inv_one_sub {r : Real} (hr0 : 0 ≤ r) (hr1 : r < 1) (m : Nat) :
    geom r m ≤ 1 / (1 - r) :=
  le_div_of_mul_le_pos_local (geom_scaled_le_one hr0 m) (sub_pos_of_lt hr1)

private theorem div_lt_of_lt_mul_local2 {a b c : Real} (h : a < c * b) (hb : 0 < b) :
    a / b < c := by
  have hbne : b ≠ 0 := ne_of_gt hb
  have hbinv : 0 < 1 / b := div_pos_of_pos_pos one_pos hb
  have h2 : a * (1 / b) < c * b * (1 / b) := mul_lt_mul_of_pos_right h hbinv
  have h3 : c * b * (1 / b) = c := by
    rw [mul_assoc c b (1 / b), mul_inv b hbne, mul_one_ax]
  rw [h3] at h2
  rwa [div_def a b hbne]

/-! ## §5 — The comparison test / M-test step -/

/-- The set of partial sums of `f` is bounded above. -/
def HasBoundedPartialSums (f : Nat → Real) : Prop :=
  BoundedAbove (fun x => ∃ n, x = partialSum f n)

/-- **Comparison test.** A termwise-nonneg `f` eventually dominated by a genuine geometric
sequence `npow n r` (`0 ≤ r < 1`) has bounded partial sums — the exact hypothesis
`series_sum_exists_of_bounded` below needs to invoke `sup_exists`. -/
theorem hasBoundedPartialSums_of_eventually_le_geom
    {f : Nat → Real} (hf : ∀ n, 0 ≤ f n)
    {r : Real} (hr0 : 0 ≤ r) (hr1 : r < 1)
    {N0 : Nat} (hN0 : ∀ n, N0 ≤ n → f n ≤ npow n r) :
    HasBoundedPartialSums f := by
  refine ⟨partialSum f N0 + npow N0 r * (1 / (1 - r)), fun x hx => ?_⟩
  obtain ⟨n, hn⟩ := hx
  rcases Nat.lt_or_ge n N0 with hlt' | hge
  · have hmn : n ≤ N0 := Nat.le_of_lt hlt'
    have h1 : partialSum f n ≤ partialSum f N0 := partialSum_mono hf hmn
    have hextra : 0 ≤ npow N0 r * (1 / (1 - r)) :=
      mul_nonneg (npow_nonneg hr0 N0) (le_of_lt (div_pos_of_pos_pos one_pos (sub_pos_of_lt hr1)))
    rw [hn]
    have h2 := add_le_add_left hextra (partialSum f N0)
    rw [show partialSum f N0 + 0 = partialSum f N0 from by mach_ring] at h2
    exact le_trans h1 h2
  · obtain ⟨m, hm⟩ := Nat.le.dest hge
    have htail := partialSum_tail_le_geom hN0 m
    rw [hm] at htail
    have hgeom := geom_le_inv_one_sub hr0 hr1 m
    have hscale : npow N0 r * geom r m ≤ npow N0 r * (1 / (1 - r)) :=
      mul_le_mul_of_nonneg_left hgeom (npow_nonneg hr0 N0)
    have hfinal := add_le_add_left hscale (partialSum f N0)
    rw [hn]
    exact le_trans htail hfinal

/-- **A genuine sum, via completeness.** For `f` termwise nonneg with bounded partial sums, the
supremum of the partial sums exists — this is the series' sum in the least-upper-bound sense,
built directly from `sup_exists` (`Basic.lean`), the same completeness axiom `IntermediateValue`
and `ExtremeValueAttainment` already trust. No Cauchy-sequence machinery needed. -/
theorem series_sum_exists_of_bounded
    {f : Nat → Real} (hf : ∀ n, 0 ≤ f n) (hb : HasBoundedPartialSums f) :
    ∃ s : Real, (∀ n, partialSum f n ≤ s) ∧ ∀ s', (∀ n, partialSum f n ≤ s') → s ≤ s' := by
  obtain ⟨M, hM⟩ := hb
  have hne : ∃ x, ∃ n, x = partialSum f n := ⟨partialSum f 0, 0, rfl⟩
  obtain ⟨s, hub, hlub⟩ := sup_exists (fun x => ∃ n, x = partialSum f n) hne ⟨M, hM⟩
  refine ⟨s, fun n => hub (partialSum f n) ⟨n, rfl⟩, fun s' hs' => hlub s' ?_⟩
  intro x hx
  obtain ⟨n, hn⟩ := hx
  rw [hn]; exact hs' n

/-! ## §6 — Upgrading the exponential-beats-geometric bound from `< 1` to `< npow n r` -/

private theorem npow_div_mul_cancel_local {R r : Real} (hr : r ≠ 0) : (R / r) * r = R := by
  rw [div_def R r hr, show R * (1 / r) * r = R * (r * (1 / r)) from by mach_ring,
      mul_inv r hr, mul_one_ax]

/-- Upgrade of `exp_beats_geometric`: not just eventually `< 1`, but eventually `≤` any fixed
genuine geometric rate `npow n r` (`0 < r < 1`). Route: apply `exp_beats_geometric` with `R/r`
in place of `R`, then multiply the resulting `< 1` bound through by `npow n r > 0` and use
`npow_mul_distrib` to fold `npow n (R/r) * npow n r` back into `npow n R`. -/
theorem term_eventually_le_geometric
    {R D c C r : Real} (hR : 0 < R) (hD : 1 < D) (hc : 0 < c) (hC : 0 < C)
    (hr0 : 0 < r) (hr1 : r < 1) :
    ∃ N : Nat, ∀ n : Nat, N ≤ n →
      C * npow n R * Real.exp (-(c * npow n D)) ≤ npow n r := by
  have hRr : 0 < R / r := div_pos_of_pos_pos hR hr0
  obtain ⟨N, hN⟩ := exp_beats_geometric (R := R / r) (D := D) (c := c) (C := C) hRr hD hc hC
  refine ⟨N, fun n hn => ?_⟩
  have key := hN n hn
  have hrne : r ≠ 0 := ne_of_gt hr0
  have hprod : npow n (R / r) * npow n r = npow n R := by
    rw [← npow_mul_distrib (R / r) r n, npow_div_mul_cancel_local hrne]
  have hrpow_pos : 0 < npow n r := npow_pos hr0 n
  have hmul : C * npow n (R / r) * Real.exp (-(c * npow n D)) * npow n r
      < 1 * npow n r := mul_lt_mul_of_pos_right key hrpow_pos
  rw [show (1 : Real) * npow n r = npow n r from by mach_ring,
      show C * npow n (R / r) * Real.exp (-(c * npow n D)) * npow n r
        = C * (npow n (R / r) * npow n r) * Real.exp (-(c * npow n D)) from by mach_ring,
      hprod] at hmul
  exact le_of_lt hmul

/-! ## §7 — The payoff: the Weierstrass term sequence has bounded partial sums -/

/-- **The Weierstrass term sequence is summable**, for every fixed `t>0` and derivative order
`k`. Same setup as `weierstrass_term_eventually_lt_one` (`EMLWeierstrassTermBound.lean`), but
carried through `term_eventually_le_geometric` (with `r := 1/2`) and the comparison test instead
of stopping at the `< 1` bound. This is the exact hypothesis a Weierstrass M-test argument would
consume — genuine summability, not just eventual term-smallness. -/
theorem weierstrass_term_hasBoundedPartialSums (t : Real) (ht : 0 < t) (k : Nat) :
    HasBoundedPartialSums
      (fun n => npow k pi * npow n (1 / (1 + 1)) * npow (n * k) (1 + 1 + 1)
        * Real.exp (-(pi * pi * t / (1 + 1) * npow n (npow 2 (1 + 1 + 1))))) := by
  let a : Real := 1 / (1 + 1)
  let b : Real := 1 + 1 + 1
  have h11_pos : (0 : Real) < 1 + 1 := add_pos one_pos one_pos
  have h1_lt_11 : (1 : Real) < 1 + 1 := by
    have h := add_lt_add_left one_pos 1; rwa [add_zero] at h
  have h11_lt_111 : (1 : Real) + 1 < 1 + 1 + 1 := by
    have h := add_lt_add_left one_pos (1 + 1); rwa [add_zero] at h
  have h1_lt_111 : (1 : Real) < 1 + 1 + 1 := lt_trans_ax h1_lt_11 h11_lt_111
  have ha : 0 < a := div_pos_of_pos_pos one_pos h11_pos
  have hb : 0 < b := by show (0 : Real) < 1 + 1 + 1; exact lt_trans_ax one_pos h1_lt_111
  have hR : 0 < a * npow k b := mul_pos ha (npow_pos hb k)
  have hD : 1 < npow 2 b := by
    have h1 : npow 2 b = b * b := by show b * (b * 1) = b * b; mach_ring
    rw [h1]
    have hb1 : (1 : Real) < b := by show (1 : Real) < 1 + 1 + 1; exact h1_lt_111
    have hstep : 1 * 1 < b * b := by
      have h1lt : (1 : Real) * 1 < b * 1 := mul_lt_mul_of_pos_right hb1 one_pos
      have h2lt : b * 1 < b * b := wgc_mul_lt_mul_of_pos_left hb1 hb
      exact lt_trans_ax h1lt h2lt
    rwa [show (1 : Real) * 1 = 1 by mach_ring] at hstep
  have hc : 0 < pi * pi * t / (1 + 1) := by
    have hpp : 0 < pi * pi := mul_pos pi_pos pi_pos
    have hppt : 0 < pi * pi * t := mul_pos hpp ht
    exact div_pos_of_pos_pos hppt h11_pos
  have hC : 0 < npow k pi := npow_pos pi_pos k
  have hr0 : (0 : Real) < 1 / (1 + 1) := div_pos_of_pos_pos one_pos h11_pos
  have hr1 : (1 : Real) / (1 + 1) < 1 := by
    have h : (1 : Real) < 1 * (1 + 1) := by
      rw [show (1 : Real) * (1 + 1) = 1 + 1 from by mach_ring]; exact h1_lt_11
    exact div_lt_of_lt_mul_local2 h h11_pos
  obtain ⟨N, hN⟩ := term_eventually_le_geometric (R := a * npow k b) (D := npow 2 b)
    (c := pi * pi * t / (1 + 1)) (C := npow k pi) (r := 1 / (1 + 1)) hR hD hc hC hr0 hr1
  have hN0 : ∀ n : Nat, N ≤ n →
      npow k pi * npow n a * npow (n * k) b
        * Real.exp (-(pi * pi * t / (1 + 1) * npow n (npow 2 b))) ≤ npow n (1 / (1 + 1)) := by
    intro n hn
    have key := hN n hn
    have eR : npow n (a * npow k b) = npow n a * npow (n * k) b := by
      rw [npow_mul_distrib, npow_tower, Nat.mul_comm k n]
    rw [eR] at key
    have eassoc : npow k pi * (npow n a * npow (n * k) b)
        * Real.exp (-(pi * pi * t / (1 + 1) * npow n (npow 2 b)))
        = npow k pi * npow n a * npow (n * k) b
          * Real.exp (-(pi * pi * t / (1 + 1) * npow n (npow 2 b))) := by mach_ring
    rwa [eassoc] at key
  have hfnonneg : ∀ n, 0 ≤ npow k pi * npow n a * npow (n * k) b
      * Real.exp (-(pi * pi * t / (1 + 1) * npow n (npow 2 b))) := by
    intro n
    have h1 : 0 ≤ npow k pi := le_of_lt hC
    have h2 : 0 ≤ npow n a := npow_nonneg (le_of_lt ha) n
    have h3 : 0 ≤ npow (n * k) b := npow_nonneg (le_of_lt hb) (n * k)
    have h4 : 0 ≤ Real.exp (-(pi * pi * t / (1 + 1) * npow n (npow 2 b))) := le_of_lt (exp_pos _)
    exact mul_nonneg (mul_nonneg (mul_nonneg h1 h2) h3) h4
  exact hasBoundedPartialSums_of_eventually_le_geom hfnonneg (le_of_lt hr0) hr1 hN0
