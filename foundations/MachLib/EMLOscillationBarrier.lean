/-
MachLib.EMLOscillationBarrier — the oscillation barrier as an
asymptotic-class statement, and `sin` as its witness.

Bridges two strands of the EML programme:

  • The **Infinite-Zeros Barrier** (already formalised constructively via the
    Pfaffian zero-count bound: `EMLPfaffian.sin_not_in_eml_any_depth` —
    every `EMLTree` is a Pfaffian function with a *finite* zero count on any
    bounded interval, so `sin`, which has arbitrarily many zeros, is not an
    `EMLTree` at any depth).

  • The **asymptotic-class framework** (`EMLAsymptoticClass`), whose classes —
    `EventuallyConstant`, `EventuallyNegative`, `EventuallyAboveOne`,
    `EventuallyDominatesAny` — are all eventually-*signed* / monotone. They
    describe the **split / non-oscillatory** side of the EML world.

The connective tissue is `HasArbitrarilyLargeZeros`: an eventually-signed
function cannot have zeros arbitrarily far out, so EVERY signed asymptotic
class is disjoint from it. `sin` *does* have arbitrarily large zeros
(at `k·π`, with `k·π → ∞` by Archimedeanness), hence `sin` lands in NONE of
the signed classes.

Why this matters (frontier T1.A, differential Galois ↔ EML depth, see
`monogate-research/exploration/differential_galois_eml_depth_2026_06_24/`):
`HasArbitrarilyLargeZeros` is the Lean avatar of the **compact (rotational)
torus factor** of a differential Galois group. Split-torus / real-exponential
growth (the EML-finite side) is eventually signed; a compact-torus factor
forces oscillation — arbitrarily large zeros — which no EML asymptotic class
admits. So this file is the asymptotic-class statement of "the EML-finite side
carries no compact torus."
-/

import MachLib.EMLAsymptoticClass
import MachLib.EMLPfaffian
import MachLib.SinNotInEMLDepth2Partial   -- pi_gt_one

namespace MachLib

open Real

/-- `f` has zeros arbitrarily far out: for every threshold `N` there is some
`x ≥ N` with `f x = 0`. The formal Infinite-Zeros-Barrier predicate at the
asymptotic level (and the avatar of a compact differential-Galois torus). -/
def HasArbitrarilyLargeZeros (f : Real → Real) : Prop :=
  ∀ N : Real, ∃ x : Real, N ≤ x ∧ f x = 0

/-! ### Every eventually-signed asymptotic class is disjoint from oscillation.

These need no Archimedean / unboundedness input: a single zero past the
sign threshold already contradicts the class. -/

/-- An eventually-negative function has no zeros past its threshold. -/
theorem EventuallyNegative.not_arbitrarily_large_zeros {f : Real → Real}
    (h : EventuallyNegative f) : ¬ HasArbitrarilyLargeZeros f := by
  obtain ⟨N, hN⟩ := h
  intro hosc
  obtain ⟨x, hx_ge, hx_zero⟩ := hosc N
  have hlt : f x < 0 := hN x hx_ge
  rw [hx_zero] at hlt
  exact lt_irrefl_ax 0 hlt

/-- An eventually-`>1` function has no zeros past its threshold. -/
theorem EventuallyAboveOne.not_arbitrarily_large_zeros {f : Real → Real}
    (h : EventuallyAboveOne f) : ¬ HasArbitrarilyLargeZeros f := by
  obtain ⟨N, hN⟩ := h
  intro hosc
  obtain ⟨x, hx_ge, hx_zero⟩ := hosc N
  have h1 : 1 < f x := hN x hx_ge
  rw [hx_zero] at h1
  -- h1 : 1 < 0, with 0 < 1 ⇒ 0 < 0.
  exact lt_irrefl_ax 0 (lt_trans_ax zero_lt_one_ax h1)

/-- A function dominating every bound (→ +∞) has no zeros past its threshold. -/
theorem EventuallyDominatesAny.not_arbitrarily_large_zeros {f : Real → Real}
    (h : EventuallyDominatesAny f) : ¬ HasArbitrarilyLargeZeros f := by
  obtain ⟨N, hN⟩ := h 0
  intro hosc
  obtain ⟨x, hx_ge, hx_zero⟩ := hosc N
  have h0 : 0 < f x := hN x hx_ge
  rw [hx_zero] at h0
  exact lt_irrefl_ax 0 h0

/-! ### `sin` IS oscillatory: arbitrarily large zeros at `k·π`. -/

/-- `0 ≤ natCast n`. (Bridges `Nat` into the ordered Real; needed to scale
`natCast n` up by `π ≥ 1`.) -/
theorem natCast_nonneg (n : Nat) : (0 : Real) ≤ natCast n := by
  induction n with
  | zero => rw [natCast_zero]; exact le_refl 0
  | succ m ih =>
    rw [natCast_succ]
    exact le_trans ih (le_add_of_nonneg_right (le_of_lt zero_lt_one_ax))

/-- `sin` has arbitrarily large zeros. The zeros `k·π` are unbounded: given `N`,
Archimedeanness yields `n` with `N < natCast n`, and `natCast n ≤ natCast n · π`
(as `π ≥ 1`), so `natCast n · π ≥ N` is a zero of `sin`
(`sin (natCast n · π) = 0`). -/
theorem sin_has_arbitrarily_large_zeros : HasArbitrarilyLargeZeros sin := by
  intro N
  obtain ⟨n, hn⟩ := archimedean N
  refine ⟨natCast n * pi, ?_, ?_⟩
  · -- N ≤ natCast n * pi
    have h_step : natCast n ≤ natCast n * pi := by
      have h := mul_le_mul_of_nonneg_left (le_of_lt pi_gt_one) (natCast_nonneg n)
      rwa [mul_one_ax] at h
    exact le_of_lt (lt_of_lt_of_le hn h_step)
  · exact sin_natCast_mul_pi n

/-! ### Synthesis — `sin` escapes the signed asymptotic classification.

The compact-torus prototype lands in none of the EML-finite (split-side)
asymptotic classes. This is the asymptotic-class shadow of
`EMLPfaffian.sin_not_in_eml_any_depth`. -/

theorem sin_not_eventually_negative : ¬ EventuallyNegative sin :=
  fun h => h.not_arbitrarily_large_zeros sin_has_arbitrarily_large_zeros

theorem sin_not_eventually_above_one : ¬ EventuallyAboveOne sin :=
  fun h => h.not_arbitrarily_large_zeros sin_has_arbitrarily_large_zeros

theorem sin_not_eventually_dominates_any : ¬ EventuallyDominatesAny sin :=
  fun h => h.not_arbitrarily_large_zeros sin_has_arbitrarily_large_zeros

/-- `sin` is in none of the three positive-side asymptotic classes
(`Negative`, `AboveOne`, `DominatesAny`) at once — the oscillatory obstruction
made an asymptotic-class statement. -/
theorem sin_escapes_signed_classes :
    ¬ EventuallyNegative sin ∧ ¬ EventuallyAboveOne sin ∧
      ¬ EventuallyDominatesAny sin :=
  ⟨sin_not_eventually_negative, sin_not_eventually_above_one,
   sin_not_eventually_dominates_any⟩

/-! ### The CONVERSE witness — a split-torus solution realised as an EMLTree.

`exp x = exp x − log 1` (clamp: `log 1 = 0`), so `e^x` is the depth-1 `EMLTree`
`eml(var, const 1)`. It is the prototypical SPLIT-torus solution (`y'' = y`), and
by Phase-17 closure rule 6 (`Dominates × Const → Dominates`) it sits in
`EventuallyDominatesAny` — hence, by the disjointness above, has NO arbitrarily
large zeros. This is the structural converse of `sin_escapes_signed_classes`:
the split side IS an `EMLTree` and DOES land in a signed asymptotic class. The
two together realise the split↔compact dichotomy (frontier T1.A) inside Lean:

  • `sin`  (compact torus) — no `EMLTree`, escapes every signed class.
  • `e^x`  (split  torus) — the `EMLTree` `eml(var, const 1)`, dominates. -/

/-- `const 1` is constant (the divisor leaf of the `e^x` tree). -/
theorem const_one_eventually_constant :
    EventuallyConstant (EMLTree.const 1).eval :=
  ⟨1, 0, fun _ _ => rfl⟩

/-- The split-torus solution `e^x = eml(var, const 1)` dominates: it is in the
signed class `EventuallyDominatesAny`. Converse-side companion to
`sin_not_eventually_dominates_any`. -/
theorem exp_eml_dominates :
    EventuallyDominatesAny (EMLTree.eml EMLTree.var (EMLTree.const 1)).eval :=
  var_eventually_dominates_any.eml_with_const const_one_eventually_constant

/-- …and therefore has NO arbitrarily large zeros — the split-torus structural
opposite of `sin_has_arbitrarily_large_zeros`. -/
theorem exp_eml_not_arbitrarily_large_zeros :
    ¬ HasArbitrarilyLargeZeros (EMLTree.eml EMLTree.var (EMLTree.const 1)).eval :=
  exp_eml_dominates.not_arbitrarily_large_zeros

end MachLib
