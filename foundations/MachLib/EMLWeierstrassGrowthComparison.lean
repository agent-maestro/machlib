import MachLib.Exp
import MachLib.ErrorAlgebra
import MachLib.Decimal
import MachLib.DivisionError

/-!
# EML Weierstrass growth comparison — double-exponential beats single-exponential

Formalizes the core asymptotic lemma behind `monogate-research`'s
`exploration/eml_weierstrass_general_2026_07_23/` note (T2.C, the open EML
Weierstrass target theorem): for a lacunary series with exponentially-growing
frequencies, heat-kernel damping (double-exponential in the index) beats any
fixed linear growth rate (single-exponential frequency growth composed with a
fixed polynomial/coefficient factor, after taking logs).

The SymPy note verified this numerically on two cases chosen to break the
original example's unnecessary hypotheses. This file proves the underlying
growth-rate comparison directly: `npow n (1+v)` (representing `Dⁿ` for
`D = 1+v > 1`) eventually exceeds ANY fixed linear function `natCast n * A`,
for `v > 0`. This is the fact that lets `exp(c · Dⁿ)` beat `rⁿ` for
*arbitrary* fixed `r` — the "double-exponential beats single-exponential"
mechanism, stated and proved independent of the specific numbers.

MachLib has zero Mathlib dependency (see `lakefile.lean`) and
`MachLib.Asymptotics`'s own scope note: "Does NOT define limits or
convergence... full limits require sequences + Cauchy reasoning that MachLib
doesn't have." This file does not attempt general limit theory either — it
proves the one comparison fact actually needed, via `archimedean` (already an
axiom, used the same way in `QuantitativeNonApproximation.lean`) plus a
squared Bernoulli bound for genuine quadratic (not just linear) growth.

## What this proves

  - `npow_bernoulli` — Bernoulli's inequality `1 + n·v ≤ (1+v)ⁿ`.
  - `npow_double_sq` / `npow_quadratic_lower` — squaring Bernoulli via
    `npow_add` gives a genuine quadratic lower bound `n²v² ≤ (1+v)^(2n)`.
  - `npow_beats_linear_from` — propagation lemma: if the bound holds at a
    starting point `N` with one step of slack to spare, ordinary induction
    (not floor division) carries it to every `m ≥ N`.
  - `npow_eventually_beats_linear` — **the main result**: for `v > 0` and any
    fixed `A : Real`, eventually `n · A < (1+v)ⁿ`. Quadratic beats linear for
    any fixed slope, however large. Combines the quadratic bound (to get the
    induction off the ground at `N = n+n`) with the propagation lemma.

## What this does NOT prove

Not yet connected to the actual Fourier-series / heat-kernel setting (that
would need `Real.cos`, infinite series/summability, and `Real.exp` composed
with `npow`-indexed frequencies `Bⁿ` — a substantially larger undertaking,
flagged as future work, not attempted here). This file formalizes the
asymptotic-comparison KERNEL of the argument, the piece that was previously
only checked numerically.

`sorryAx`-free, Mathlib-free, no new axioms beyond what MachLib already has
(`archimedean`, `exp` axioms — neither newly introduced here).
-/

namespace MachLib
namespace Real

/-! ## Small order/algebra helpers, derived locally from `lt_total`/`le_iff_lt_or_eq`
(MachLib's foundational trichotomy + order axioms) rather than importing distant
files for one lemma each — matches the codebase's own `_local` convention. -/

theorem wgc_lt_of_not_le {a b : Real} (h : ¬ a ≤ b) : b < a := by
  rcases lt_total a b with hab | hab | hab
  · exact absurd (le_of_lt hab) h
  · exact absurd (le_of_eq hab) h
  · exact hab

theorem wgc_not_lt_of_le {a b : Real} (h : a ≤ b) : ¬ b < a := by
  intro hba
  rcases (le_iff_lt_or_eq a b).mp h with hlt | heq
  · exact lt_irrefl_ax a (lt_trans_ax hlt hba)
  · subst heq; exact lt_irrefl_ax a hba

theorem wgc_mul_lt_mul_of_pos_left {a b c : Real} (h : a < b) (hc : 0 < c) :
    c * a < c * b := by
  have h1 : a * c < b * c := mul_lt_mul_of_pos_right h hc
  rw [mul_comm a c, mul_comm b c] at h1
  exact h1

theorem wgc_add_lt_add_of_lt_le {a b c d : Real} (h1 : a < b) (h2 : c ≤ d) :
    a + c < b + d := by
  have hstep1 : a + c < b + c := by
    have h := add_lt_add_left h1 c
    rwa [add_comm c a, add_comm c b] at h
  have hstep2 : b + c ≤ b + d := add_le_add_left h2 b
  exact lt_of_lt_of_le hstep1 hstep2

theorem wgc_natCast_ge_one_of_pos {n : Nat} (hn : 0 < n) : (1 : Real) ≤ natCast n := by
  match n, hn with
  | k + 1, _ =>
      rw [natCast_succ]
      have h := natCast_nonneg k
      have := add_le_add_both h (le_refl (1:Real))
      have e : (0:Real) + 1 = 1 := by mach_ring
      rwa [e] at this

/-! ## Bernoulli's inequality -/

/-- **Bernoulli's inequality.** `1 + n·v ≤ (1+v)ⁿ` for `v ≥ 0`. Standard
induction: the inductive step multiplies both sides of the IH by `(1+v) ≥ 1`
and drops the nonneg `n·v²` cross term. -/
theorem npow_bernoulli {v : Real} (hv : 0 ≤ v) :
    ∀ n : Nat, 1 + natCast n * v ≤ npow n (1 + v)
  | 0 => by
      rw [natCast_zero]
      have e : (1 : Real) + 0 * v = 1 := by mach_ring
      rw [e]
      exact le_refl _
  | n + 1 => by
      have ih := npow_bernoulli hv n
      rw [npow_succ, natCast_succ]
      have h1v0 : (0 : Real) ≤ 1 + v := le_trans (le_of_lt one_pos) (le_add_of_nonneg_right hv)
      -- Scale the IH by (1+v) ≥ 0: (1+v)*(1+n·v) ≤ (1+v)*npow n (1+v).
      have hscaled : (1 + v) * (1 + natCast n * v) ≤ (1 + v) * npow n (1 + v) :=
        mul_le_mul_of_nonneg_left ih h1v0
      -- Algebra: (1+v)*(1+n·v) = 1 + (n+1)·v + n·v² ≥ 1 + (n+1)·v.
      have hexpand : (1 + v) * (1 + natCast n * v)
          = 1 + (natCast n + 1) * v + natCast n * (v * v) := by mach_ring
      have hnv2_nonneg : 0 ≤ natCast n * (v * v) :=
        mul_nonneg (natCast_nonneg n) (mul_nonneg hv hv)
      have hgoal_lhs : 1 + (natCast n + 1) * v
          ≤ 1 + (natCast n + 1) * v + natCast n * (v * v) :=
        le_add_of_nonneg_right hnv2_nonneg
      rw [hexpand] at hscaled
      exact le_trans hgoal_lhs hscaled

/-! ## Squared Bernoulli — genuine quadratic growth -/

/-- `(1+v)^(2n) = ((1+v)ⁿ)²` — `npow_add` at `a = b = n`. -/
theorem npow_double_sq (v : Real) (n : Nat) :
    npow (n + n) (1 + v) = npow n (1 + v) * npow n (1 + v) :=
  npow_add (1 + v) n n

/-- **Squared Bernoulli.** `n²v² ≤ (1+v)^(2n)`, for `v ≥ 0`. Squares the
linear Bernoulli bound via `npow_double_sq`, then drops the nonneg
`1 + 2nv` cross terms. Genuine quadratic-in-`n` growth, unlike the linear
`npow_bernoulli` alone. -/
theorem npow_quadratic_lower {v : Real} (hv : 0 ≤ v) (n : Nat) :
    natCast n * natCast n * (v * v) ≤ npow (n + n) (1 + v) := by
  have hb := npow_bernoulli hv n
  have hb_nonneg : (0 : Real) ≤ 1 + natCast n * v :=
    le_trans (le_of_lt one_pos) (le_add_of_nonneg_right (mul_nonneg (natCast_nonneg n) hv))
  have hsq : (1 + natCast n * v) * (1 + natCast n * v)
      ≤ npow n (1 + v) * npow n (1 + v) := by
    have hstep1 : (1 + natCast n * v) * (1 + natCast n * v)
        ≤ npow n (1 + v) * (1 + natCast n * v) :=
      mul_le_mul_of_nonneg_right hb hb_nonneg
    have hnn : (0 : Real) ≤ npow n (1 + v) :=
      npow_nonneg (le_trans (le_of_lt one_pos) (le_add_of_nonneg_right hv)) n
    have hstep2 : npow n (1 + v) * (1 + natCast n * v)
        ≤ npow n (1 + v) * npow n (1 + v) :=
      mul_le_mul_of_nonneg_left hb hnn
    exact le_trans hstep1 hstep2
  rw [npow_double_sq]
  have hexpand : (1 + natCast n * v) * (1 + natCast n * v)
      = 1 + (natCast n + natCast n) * v + natCast n * natCast n * (v * v) := by mach_ring
  rw [hexpand] at hsq
  have hdrop : natCast n * natCast n * (v * v)
      ≤ 1 + (natCast n + natCast n) * v + natCast n * natCast n * (v * v) := by
    have h1 : (0:Real) ≤ 1 := le_of_lt one_pos
    have h2 : (0:Real) ≤ (natCast n + natCast n) * v :=
      mul_nonneg (add_nonneg_ea (natCast_nonneg n) (natCast_nonneg n)) hv
    have h3 := add_le_add_both h1 h2
    have e : (0:Real) + 0 = 0 := by mach_ring
    rw [e] at h3
    have h5 := add_le_add_both h3 (le_refl (natCast n * natCast n * (v * v)))
    have e2 : (0:Real) + natCast n * natCast n * (v * v)
        = natCast n * natCast n * (v * v) := by mach_ring
    rw [e2] at h5
    have e3 : (1 + (natCast n + natCast n) * v) + natCast n * natCast n * (v * v)
        = 1 + (natCast n + natCast n) * v + natCast n * natCast n * (v * v) := by mach_ring
    rwa [e3] at h5
  exact le_trans hdrop hsq

/-! ## The main result: exponential eventually beats any fixed linear bound -/

/-- **Propagation lemma.** If the bound holds at a starting point `N` WITH
enough slack (`A ≤ v · (1+v)^N`, i.e. one more step of growth already covers
`A`), it propagates forward to every `m ≥ N`: going from `m` to `m+1`, the
left side grows by exactly `A` while the right side grows by
`v · npow m (1+v)`, and the slack condition (itself non-decreasing in `m`,
since `npow` only grows) keeps covering the increment forever. Avoids Nat
division / floor(`m/2`) bookkeeping entirely — the only place genuine
super-linear growth is needed is to get the induction off the ground at
`N`, handled by `npow_quadratic_lower` at the call site. -/
theorem npow_beats_linear_from {v : Real} (hv : 0 < v) (A : Real) (N : Nat)
    (hbase : natCast N * A < npow N (1 + v)) (hslack : A ≤ v * npow N (1 + v)) :
    ∀ k : Nat, natCast (N + k) * A < npow (N + k) (1 + v)
  | 0 => by rw [Nat.add_zero]; exact hbase
  | k + 1 => by
      have ih := npow_beats_linear_from hv A N hbase hslack k
      have hmono : npow N (1 + v) ≤ npow (N + k) (1 + v) :=
        npow_mono_le (le_add_of_nonneg_right (le_of_lt hv)) (Nat.le_add_right N k)
      have hslack_k : A ≤ v * npow (N + k) (1 + v) :=
        le_trans hslack (mul_le_mul_of_nonneg_left hmono (le_of_lt hv))
      have hstep : natCast (N + k) * A + A < npow (N + k) (1 + v) + v * npow (N + k) (1 + v) :=
        wgc_add_lt_add_of_lt_le ih hslack_k
      have eL : natCast (N + k) * A + A = natCast (N + k + 1) * A := by
        rw [Nat.add_succ, natCast_succ]; mach_ring
      have eR : npow (N + k) (1 + v) + v * npow (N + k) (1 + v) = npow (N + k + 1) (1 + v) := by
        rw [npow_succ]; mach_ring
      rw [eL, eR] at hstep
      rw [Nat.add_succ]
      exact hstep

/-- **Main result.** For `v > 0` and any fixed `A : Real`, eventually
`natCast n · A < (1+v)ⁿ` — quadratic beats linear for any fixed slope,
however large. This is the growth-rate fact underlying "heat-kernel damping
beats any fixed exponential coefficient growth" in the EML Weierstrass
mechanism: applied with `1+v = D` (the squared frequency base) and `A`
absorbing the polynomial/coefficient growth rate, it is exactly what makes
`exp(c·Dⁿ)` eventually exceed `rⁿ` for arbitrary fixed `r`.

Strategy: get the quadratic bound off the ground at a threshold `N = n+n`
(`npow_quadratic_lower`), check it comes with enough slack for
`npow_beats_linear_from` to propagate forward to all `m ≥ N` by ordinary
induction — no floor division needed. -/
theorem npow_eventually_beats_linear {v : Real} (hv : 0 < v) (A : Real) :
    ∃ N : Nat, ∀ m : Nat, N ≤ m → natCast m * A < npow m (1 + v) := by
  by_cases hA : A ≤ 0
  · -- A ≤ 0: natCast m * A ≤ 0 < 1 ≤ npow m (1+v), for every m.
    refine ⟨0, fun m _ => ?_⟩
    have h1v : (1 : Real) ≤ 1 + v := le_add_of_nonneg_right (le_of_lt hv)
    have hnp1 : (1 : Real) ≤ npow m (1 + v) := one_le_npow (1 + v) h1v m
    have hmA_nonpos : natCast m * A ≤ 0 := by
      have hstep : natCast m * A ≤ natCast m * 0 :=
        mul_le_mul_of_nonneg_left hA (natCast_nonneg m)
      have e : natCast m * (0:Real) = 0 := by mach_ring
      rwa [e] at hstep
    exact lt_of_le_of_lt hmA_nonpos (lt_of_lt_of_le zero_lt_one_ax hnp1)
  · -- A > 0: choose n via archimedean so natCast n * (v*v) > 4*A (extra room covers slack too).
    have hApos : 0 < A := wgc_lt_of_not_le hA
    have hvv_pos : 0 < v * v := mul_pos hv hv
    obtain ⟨n, hn⟩ := archimedean ((A + A + A + A) / (v * v))
    have hn_pos : 0 < n := by
      rcases Nat.eq_zero_or_pos n with h0 | hpos
      · exfalso
        rw [h0, natCast_zero] at hn
        have h4A_nonneg : (0:Real) ≤ A + A + A + A :=
          add_nonneg_ea (add_nonneg_ea (add_nonneg_ea (le_of_lt hApos) (le_of_lt hApos))
            (le_of_lt hApos)) (le_of_lt hApos)
        have hdiv_nonneg : (0:Real) ≤ (A + A + A + A) / (v * v) :=
          div_nonneg_of_nonneg_pos h4A_nonneg hvv_pos
        exact absurd hn (wgc_not_lt_of_le hdiv_nonneg)
      · exact hpos
    have hn_ge1 : (1:Real) ≤ natCast n := wgc_natCast_ge_one_of_pos hn_pos
    have key : A + A + A + A < natCast n * (v * v) := by
      have hmul := mul_lt_mul_of_pos_right hn hvv_pos
      rwa [div_mul_cancel (ne_of_gt hvv_pos)] at hmul
    have hquad := npow_quadratic_lower (le_of_lt hv) n
    -- natCast n ≥ 1, so multiplying `key` by natCast n only strengthens it: gives
    -- natCast n * (A+A+A+A) < natCast n * natCast n * (v*v) ≤ npow(n+n)(1+v).
    have hstep2 : natCast n * (A + A + A + A) < npow (n + n) (1 + v) := by
      have hmul2 : natCast n * (A + A + A + A) < natCast n * (natCast n * (v * v)) :=
        wgc_mul_lt_mul_of_pos_left key (lt_of_lt_of_le zero_lt_one_ax hn_ge1)
      have e2 : natCast n * (natCast n * (v * v)) = natCast n * natCast n * (v * v) := by
        mach_ring
      rw [e2] at hmul2
      exact lt_of_lt_of_le hmul2 hquad
    have hnn_cast : natCast (n + n) = natCast n + natCast n := natCast_add n n
    -- (a) base case with slack: natCast(n+n)*A < npow(n+n)(1+v), using only ONE of the four
    -- A's from hstep2 (natCast n * A ≤ natCast n *(A+A+A+A) needs A ≥0, then natCast(n+n)*A
    -- = 2*natCast n*A ≤ natCast n*(A+A+A+A) since natCast n ≥ 2*natCast n needs care -- redo
    -- directly: natCast(n+n)*A = (natCast n + natCast n)*A = natCast n*A + natCast n*A
    -- ≤ natCast n*(A+A+A+A) since natCast n*A + natCast n*A ≤ natCast n*(A+A+A+A) iff
    -- 2 ≤ 4 after cancelling natCast n*A ≥0 -- clean via direct nonneg-difference argument.
    have hbase : natCast (n + n) * A < npow (n + n) (1 + v) := by
      have hle : natCast (n + n) * A ≤ natCast n * (A + A + A + A) := by
        rw [hnn_cast]
        have e : (natCast n + natCast n) * A + (natCast n * (A + A)) = natCast n * (A+A+A+A) := by
          mach_ring
        have hnn_A_nonneg : 0 ≤ natCast n * (A + A) :=
          mul_nonneg (natCast_nonneg n) (add_nonneg_ea (le_of_lt hApos) (le_of_lt hApos))
        have := le_add_of_nonneg_right hnn_A_nonneg (a := (natCast n + natCast n) * A)
        rwa [e] at this
      exact lt_of_le_of_lt hle hstep2
    -- (b) slack: A ≤ v * npow(n+n)(1+v). From hstep2, npow(n+n)(1+v) > natCast n*(A+A+A+A) ≥ A
    -- (since natCast n ≥1 and A+A+A+A ≥ A for A≥0) -- and v*npow(n+n)(1+v) needs the extra `v`
    -- factor; use hquad directly with the LINEAR Bernoulli piece instead for a clean bound.
    have hslack : A ≤ v * npow (n + n) (1 + v) := by
      have hbernoulli := npow_bernoulli (le_of_lt hv) (n + n)
      have h1 : (1:Real) + natCast (n+n) * v ≤ npow (n+n) (1+v) := hbernoulli
      have h2 : v * (1 + natCast (n+n) * v) ≤ v * npow (n+n) (1+v) :=
        mul_le_mul_of_nonneg_left h1 (le_of_lt hv)
      -- Suffices: A ≤ v*(1+natCast(n+n)*v) = v + natCast(n+n)*v*v. From `key` (scaled),
      -- natCast n * (v*v) > 4A ≥ A, and natCast(n+n) = 2*natCast n ≥ natCast n, so
      -- natCast(n+n)*(v*v) ≥ natCast n*(v*v) > 4A > A - v (since v>0, A>0... use ≥ A directly
      -- via a nonneg-slack argument rather than exact arithmetic).
      have hnn_ge : natCast n * (v * v) ≤ natCast (n + n) * (v * v) := by
        rw [hnn_cast]
        have hle2 : natCast n ≤ natCast n + natCast n :=
          le_add_of_nonneg_right (natCast_nonneg n)
        exact mul_le_mul_of_nonneg_right hle2 (le_of_lt hvv_pos)
      have hA_lt : A < natCast (n + n) * (v * v) := by
        have h4A_ge_A : A ≤ A + A + A + A := by
          have h3 : (0:Real) ≤ A + A + A := add_nonneg_ea (add_nonneg_ea (le_of_lt hApos)
            (le_of_lt hApos)) (le_of_lt hApos)
          have := le_add_of_nonneg_right h3 (a := A)
          rwa [show A + (A+A+A) = A+A+A+A by mach_ring] at this
        exact lt_of_le_of_lt h4A_ge_A (lt_of_lt_of_le key hnn_ge)
      have hfinal : A ≤ v + natCast (n + n) * (v * v) := by
        have := le_of_lt hA_lt
        have hv_nonneg : (0:Real) ≤ v := le_of_lt hv
        exact le_trans this (le_add_of_nonneg_left hv_nonneg)
      have e3 : v * (1 + natCast (n + n) * v) = v + natCast (n + n) * (v * v) := by mach_ring
      rw [e3] at h2
      exact le_trans hfinal h2
    refine ⟨n + n, fun m hm => ?_⟩
    obtain ⟨k, hk⟩ := Nat.le.dest hm
    rw [← hk]
    exact npow_beats_linear_from hv A (n + n) hbase hslack k

end Real
end MachLib
