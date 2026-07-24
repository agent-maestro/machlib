import MachLib.EMLWeierstrassGrowthComparison
import MachLib.Trig
import MachLib.Log
import MachLib.FieldLemmas

/-!
# EML Weierstrass term bound — connecting the growth lemma to the real setting

`MachLib.EMLWeierstrassGrowthComparison` proved the abstract growth-rate
mechanism (`(1+v)ⁿ` eventually beats any fixed linear function). This file
connects it, for the first time, to `Real.exp`/`Real.log`/`Real.pi` and the
ACTUAL Weierstrass parameters (`a = 1/2, b = 3`) — instantiating the exact
term-magnitude claim `monogate-research`'s
`exploration/eml_weierstrass_2026_06_25/` and
`exploration/eml_weierstrass_general_2026_07_23/` notes checked numerically:

  n-th term of the k-th derivative of the heat-mollified Weierstrass series:
    aⁿ · (bⁿπ)^k · exp(−b^(2n)·π²·t/2)

eventually (in `n`) drops below `1`, for every fixed `t > 0` and every fixed
derivative order `k`.

## What this does NOT prove

**Not the full EML Weierstrass theorem.** MachLib has no infinite-series /
summability infrastructure at all (no `Finset.sum`, `tsum`, `Summable` —
confirmed absent from the whole library; the closest precedent,
`MachLib.KLDivergence`, sums over a `List` via `List.foldr` for a FINITE
distribution, not an infinite series). Building genuine series-convergence
theory (Cauchy criterion, uniform convergence, term-by-term differentiation)
from scratch is a real, substantial, multi-session undertaking in its own
right — not attempted here, matching this whole research program's own
discipline of reporting a checked "here is exactly how far this reaches"
over forcing a bigger claim. What IS proved is the single-term magnitude
bound — the estimate a Weierstrass M-test argument would need as its input,
not the M-test (or the resulting C^∞ conclusion) itself.

`sorryAx`-free, Mathlib-free, no new axioms beyond what MachLib already has.
-/

namespace MachLib
namespace Real

/-! ## Bridging `npow` growth to `exp`/`log` -/

/-- `npow` of a strictly positive base is strictly positive. Standard
induction — only `npow_nonneg` (non-strict) existed already. -/
theorem npow_pos {x : Real} (hx : 0 < x) : ∀ n : Nat, 0 < npow n x
  | 0 => one_pos
  | n + 1 => by rw [npow_succ]; exact mul_pos hx (npow_pos hx n)

/-- `log (Rⁿ) = n · log R`, for `R > 0`. Standard induction via `log_mul`. -/
theorem npow_log_eq {R : Real} (hR : 0 < R) :
    ∀ n : Nat, Real.log (npow n R) = natCast n * Real.log R
  | 0 => by
      show Real.log 1 = natCast 0 * Real.log R
      rw [natCast_zero, log_one]
      mach_ring
  | n + 1 => by
      have ih := npow_log_eq hR n
      rw [npow_succ, natCast_succ]
      have hRn_pos : 0 < npow n R := by
        rcases Nat.eq_zero_or_pos n with h0 | hpos
        · rw [h0]; show (0:Real) < 1; exact one_pos
        · exact npow_pos hR n
      rw [log_mul hR hRn_pos, ih]
      mach_ring

/-- **Affine version.** `npow_eventually_beats_linear` handles `n·A` (linear
through the origin); this extends to `n·A + B` (any fixed additive offset
`B`) — needed below because the log of a constant multiplicative factor
(`log C`) contributes an offset, not a rescaling. For `n ≥ 1`, bumping the
slope to `A + |B| + 1` absorbs the offset: `n·(A+|B|+1) ≥ n·A+B` always,
since `n·(|B|+1) ≥ |B|+1 > B`. -/
theorem npow_eventually_beats_affine {v : Real} (hv : 0 < v) (A B : Real) :
    ∃ N : Nat, ∀ n : Nat, N ≤ n → natCast n * A + B < npow n (1 + v) := by
  obtain ⟨N0, hN0⟩ := npow_eventually_beats_linear hv (A + abs B + 1)
  refine ⟨N0 + 1, fun n hn => ?_⟩
  have hn0 : N0 ≤ n := by omega
  have hn1 : 1 ≤ n := by omega
  have hstep := hN0 n hn0
  have hn1_real : (1:Real) ≤ natCast n := by
    rcases n with _ | k
    · omega
    · exact wgc_natCast_ge_one_of_pos (Nat.succ_pos k)
  have hboundB : B ≤ natCast n * (abs B + 1) := by
    have habsB_nonneg : (0:Real) ≤ abs B := abs_nonneg B
    have h1 : (1:Real) * abs B ≤ natCast n * abs B :=
      mul_le_mul_of_nonneg_right hn1_real habsB_nonneg
    have h3 : abs B ≤ natCast n * abs B := by
      have e : (1:Real) * abs B = abs B := by mach_ring
      rwa [e] at h1
    have h4 : abs B + 1 ≤ natCast n * abs B + natCast n :=
      add_le_add_both h3 hn1_real
    have h5 : natCast n * abs B + natCast n = natCast n * (abs B + 1) := by mach_ring
    rw [h5] at h4
    have h6 : B ≤ abs B + 1 := by
      have h7 := le_add_of_nonneg_right (le_of_lt one_pos) (a := abs B)
      exact le_trans (le_abs_self B) h7
    exact le_trans h6 h4
  have hexpand : natCast n * A + B ≤ natCast n * A + natCast n * (abs B + 1) := by
    exact add_le_add_left hboundB (natCast n * A)
  have hcombine : natCast n * A + natCast n * (abs B + 1) = natCast n * (A + abs B + 1) := by
    mach_ring
  rw [hcombine] at hexpand
  exact lt_of_le_of_lt hexpand hstep

/-- **Exponential beats geometric, with a fixed positive multiplicative
constant absorbed.** For `R > 0`, `D > 1`, `c > 0`, `C > 0`: eventually
`C · Rⁿ · exp(−c·Dⁿ) < 1`. Route: `exp_grows_strictly` reduces this to
`C·Rⁿ ≤ c·Dⁿ`; taking `log` (via `npow_log_eq` + `log_mul`) turns THAT into
an affine-vs-`Dⁿ` comparison, exactly `npow_eventually_beats_affine`. -/
theorem exp_beats_geometric {R D c C : Real}
    (hR : 0 < R) (hD : 1 < D) (hc : 0 < c) (hC : 0 < C) :
    ∃ N : Nat, ∀ n : Nat, N ≤ n → C * npow n R * Real.exp (-(c * npow n D)) < 1 := by
  have hv : 0 < D - 1 := sub_pos_of_lt hD
  have hDv : (1:Real) + (D - 1) = D := by mach_ring
  obtain ⟨N, hN⟩ := npow_eventually_beats_affine hv (Real.log R / c) (Real.log C / c)
  refine ⟨N, fun n hn => ?_⟩
  have key := hN n hn
  rw [hDv] at key
  -- key : n * (log R / c) + log C / c < npow n D
  have hCRn_pos : 0 < C * npow n R := mul_pos hC (npow_pos hR n)
  have hlog_eq : Real.log (C * npow n R) = Real.log C + natCast n * Real.log R :=
    by rw [log_mul hC (npow_pos hR n), npow_log_eq hR n]
  have hkey2 : Real.log (C * npow n R) < c * npow n D := by
    rw [hlog_eq]
    have hmul : c * (natCast n * (Real.log R / c) + Real.log C / c) < c * npow n D :=
      wgc_mul_lt_mul_of_pos_left key hc
    have hcne : c ≠ 0 := ne_of_gt hc
    have heq : c * (natCast n * (Real.log R / c) + Real.log C / c)
        = natCast n * Real.log R + Real.log C := by
      have e1 : c * (natCast n * (Real.log R / c) + Real.log C / c)
          = natCast n * (c * (Real.log R / c)) + c * (Real.log C / c) := by mach_ring
      rw [e1, mul_div_cancel_left hcne, mul_div_cancel_left hcne]
    rw [heq] at hmul
    rwa [add_comm (Real.log C) (natCast n * Real.log R)]
  have hexp_lt : Real.exp (Real.log (C * npow n R)) < Real.exp (c * npow n D) :=
    exp_lt hkey2
  rw [exp_log hCRn_pos] at hexp_lt
  have h1 : C * npow n R < Real.exp (c * npow n D) := hexp_lt
  have h2 : Real.exp (c * npow n D) * Real.exp (-(c * npow n D)) = 1 := by
    rw [← exp_add]
    have e : c * npow n D + -(c * npow n D) = 0 := by mach_ring
    rw [e, exp_zero]
  have hexp_pos : 0 < Real.exp (-(c * npow n D)) := exp_pos _
  have h3 : C * npow n R * Real.exp (-(c * npow n D))
      < Real.exp (c * npow n D) * Real.exp (-(c * npow n D)) :=
    mul_lt_mul_of_pos_right h1 hexp_pos
  rwa [h2] at h3

/-! ## Two small `npow` algebra laws, needed to match the literal term formula -/

/-- `npow` distributes over a product base: `(xy)ⁿ = xⁿyⁿ`. -/
theorem npow_mul_distrib (x y : Real) : ∀ n : Nat, npow n (x * y) = npow n x * npow n y
  | 0 => by show (1:Real) = 1 * 1; mach_ring
  | n + 1 => by
      rw [npow_succ, npow_succ, npow_succ, npow_mul_distrib x y n]
      mach_ring

/-- Power tower commutes: `(xⁿ)^k = x^(n·k)`. -/
theorem npow_tower (x : Real) (n : Nat) : ∀ k : Nat, npow k (npow n x) = npow (n * k) x
  | 0 => by rw [Nat.mul_zero]; show (1:Real) = 1; rfl
  | k + 1 => by
      rw [npow_succ, npow_tower x n k, Nat.mul_succ, npow_add, mul_comm]

/-! ## The concrete Weierstrass instantiation -/

/-- **The term-magnitude claim**, connecting `exp_beats_geometric` to
`Real.pi` and the classic Weierstrass parameters `a = 1/2, b = 3`
(`monogate-research`'s `exploration/eml_weierstrass_2026_06_25/` and
`exploration/eml_weierstrass_general_2026_07_23/` notes). For every fixed
`t > 0` and every fixed derivative order `k`, the heat-mollified `k`-th
derivative's `n`-th term magnitude

  `π^k · aⁿ · b^(nk) · exp(−π²·t/2 · b^(2n))`

(the same quantity the notes call `aⁿ(bⁿπ)^k·exp(−b^(2n)π²t/2)` — `b^(nk) =
(bⁿ)^k` and `b^(2n) = (b²)ⁿ` via `npow_tower`, associativity aside) eventually
(in `n`) drops below `1` — exactly the numerical trend both SymPy notes
exhibited (all derivative orders collapsing to `0` by a modest `n`), now a
checked theorem rather than a finite table of computed values. -/
theorem weierstrass_term_eventually_lt_one (t : Real) (ht : 0 < t) (k : Nat) :
    ∃ N : Nat, ∀ n : Nat, N ≤ n →
      npow k pi * npow n (1 / (1 + 1)) * npow (n * k) (1 + 1 + 1)
        * Real.exp (-(pi * pi * t / (1 + 1) * npow n (npow 2 (1 + 1 + 1)))) < 1 := by
  let a : Real := 1 / (1 + 1)
  let b : Real := 1 + 1 + 1
  have h11_pos : (0:Real) < 1 + 1 := add_pos one_pos one_pos
  have h1_lt_11 : (1:Real) < 1 + 1 := by
    have h := add_lt_add_left one_pos 1
    rwa [add_zero] at h
  have h11_lt_111 : (1:Real) + 1 < 1 + 1 + 1 := by
    have h := add_lt_add_left one_pos (1 + 1)
    rwa [add_zero] at h
  have h1_lt_111 : (1:Real) < 1 + 1 + 1 := lt_trans_ax h1_lt_11 h11_lt_111
  have ha : 0 < a := div_pos_of_pos_pos one_pos h11_pos
  have hb : 0 < b := by
    show (0:Real) < 1 + 1 + 1
    exact lt_trans_ax one_pos h1_lt_111
  have hR : 0 < a * npow k b := mul_pos ha (npow_pos hb k)
  have hD : 1 < npow 2 b := by
    have h1 : npow 2 b = b * b := by
      show b * (b * 1) = b * b; mach_ring
    rw [h1]
    have hb1 : (1:Real) < b := by
      show (1:Real) < 1 + 1 + 1
      exact h1_lt_111
    have hb_pos : 0 < b := hb
    have hstep : 1 * 1 < b * b := by
      have h1lt : (1:Real) * 1 < b * 1 := mul_lt_mul_of_pos_right hb1 one_pos
      have h2lt : b * 1 < b * b := wgc_mul_lt_mul_of_pos_left hb1 hb_pos
      exact lt_trans_ax h1lt h2lt
    rwa [show (1:Real)*1 = 1 by mach_ring] at hstep
  have hc : 0 < pi * pi * t / (1 + 1) := by
    have hpp : 0 < pi * pi := mul_pos pi_pos pi_pos
    have hppt : 0 < pi * pi * t := mul_pos hpp ht
    exact div_pos_of_pos_pos hppt h11_pos
  have hC : 0 < npow k pi := npow_pos pi_pos k
  obtain ⟨N, hN⟩ := exp_beats_geometric (R := a * npow k b) (D := npow 2 b)
    (c := pi * pi * t / (1 + 1)) (C := npow k pi) hR hD hc hC
  refine ⟨N, fun n hn => ?_⟩
  have key := hN n hn
  have eR : npow n (a * npow k b) = npow n a * npow (n * k) b := by
    rw [npow_mul_distrib, npow_tower, Nat.mul_comm k n]
  rw [eR] at key
  have erw : npow k pi * (npow n a * npow (n * k) b)
      * Real.exp (-(pi * pi * t / (1 + 1) * npow n (npow 2 b)))
      = npow k pi * npow n a * npow (n * k) b
        * Real.exp (-(pi * pi * t / (1 + 1) * npow n (npow 2 b))) := by
    mach_ring
  rwa [erw] at key

end Real
end MachLib
