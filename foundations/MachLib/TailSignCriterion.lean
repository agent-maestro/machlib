import MachLib.WitnessResidualContinuousTargetMetaLemma
import MachLib.GaussianDiskSandwich

/-!
# A reusable criterion for EML exclusion — and the two existing instances become corollaries

`no_tree_eq_target_of_not_tailSign` is **fully generic**: any continuous `TARGET` whose residual
`TARGET − L` lacks `TailSign` is not an EML tree, at any depth.

> ## ⚠ WHAT THIS FILE IS FOR — corrected 2026-08-06, after a wrong first answer
>
> **My first draft claimed the meta-lemma had only two instances (`sin`, `cos`) and that `a·sin`
> was new reach. Both were false.** `GeneralPeriodicTargetBarrier.no_tree_eq_periodic_target`
> already excludes **every nonconstant continuous periodic function** — which covers `sin`, `cos`,
> `sin²`, `a·sin`, `c + a·sin`, and every other periodic target at once.
>
> **I had grepped for the naming convention `*_not_tailSign` instead of for the meta-lemma's
> CALLERS**, and concluded coverage from a name pattern.
>
> **What this file actually adds is the NON-PERIODIC case.** `no_tree_eq_periodic_target` requires
> `Periodic TARGET p`; the criterion below requires only that the target keeps meeting a level and
> keeps leaving it — **arbitrarily spaced witnesses, no period.** `x · sin x` is the demonstration:
> its amplitude grows without bound, so no periodic barrier reaches it.

## The criterion

`TailSign f` is *eventually positive* ∨ *eventually negative* ∨ *eventually zero*. Refuting all
three at once needs exactly two facts, and they are the two the `sin` proof actually used:

> ### **zeros arbitrarily far out** kills `pos` and `neg`; **nonzeros arbitrarily far out** kills `zero`.

Nothing about periodicity, derivatives, or Pfaffian validity enters. **A target that keeps
returning to a level and keeps leaving it is excluded, however irregularly it does so** — the
witnesses need not be evenly spaced, which a period-based criterion would have required.

## ▸ A note on the exclusion taxonomy, which this corrects

`monogate-research/exploration/eml_exclusion_taxonomy/TAXONOMY.md` describes the working exclusion
family as *"Pfaffian/Khovanskii bounds any EML tree's zeros … target exhibits `M+1` distinct
zeros"*. **That route was RETIRED** — its axiom `zero_count_bound_classical` was deleted and both
theorems re-proven through `TailSign` (`KhovanskiiLemma.lean`'s removal notes,
`EMLAnyDepthBarrierUnconditional.lean`). **The live mechanism counts nothing; it is a sign
argument.** The taxonomy is updated alongside this file.

No new axioms. No `sorry`.
-/

namespace MachLib
namespace Real

/-- **THE CRITERION.** A function with zeros arbitrarily far out *and* nonzeros arbitrarily far out
has no eventual sign.

Each hypothesis kills exactly the branches it must: a zero beyond every `R` refutes *eventually
positive* and *eventually negative*; a nonzero beyond every `R` refutes *eventually zero*. -/
theorem not_tailSign_of_zeros_and_nonzeros {f : Real → Real}
    (hz : ∀ R : Real, ∃ x : Real, R < x ∧ f x = 0)
    (hn : ∀ R : Real, ∃ x : Real, R < x ∧ f x ≠ 0) :
    ¬ TailSign f := by
  intro h
  rcases h with ⟨R, hR⟩ | ⟨R, hR⟩ | ⟨R, hR⟩
  · obtain ⟨x, hx, hfx⟩ := hz R
    have := hR x hx
    rw [hfx] at this
    exact lt_irrefl_ax 0 this
  · obtain ⟨x, hx, hfx⟩ := hz R
    have := hR x hx
    rw [hfx] at this
    exact lt_irrefl_ax 0 this
  · obtain ⟨x, hx, hfx⟩ := hn R
    exact hfx (hR x hx)

/-- **The criterion, composed with the meta-lemma.** The one-stop exclusion route: exhibit a level
`L`, continuity, and the two witness families, and the target is outside EML at every depth. -/
theorem no_tree_eq_of_zeros_and_nonzeros
    (TARGET : Real → Real) (L : Real) (hcont : ∀ x : Real, ContinuousAt TARGET x)
    (hz : ∀ R : Real, ∃ x : Real, R < x ∧ TARGET x - L = 0)
    (hn : ∀ R : Real, ∃ x : Real, R < x ∧ TARGET x - L ≠ 0)
    (T : EMLTree) (heq : ∀ x : Real, T.eval x = TARGET x) : False :=
  no_tree_eq_target_of_not_tailSign TARGET L hcont
    (not_tailSign_of_zeros_and_nonzeros hz hn) T heq

/-! ## The witness families for `sin`, extracted once

Both are the Archimedean argument the hand proofs inlined: `nπ` for the zeros, `nπ + π/2` for the
nonzeros. Stated separately so any `sin`-shaped target can reuse them. -/

/-- `sin` has a zero beyond every `R` — at `nπ`, via Archimedes. -/
theorem sin_zero_beyond (R : Real) : ∃ x : Real, R < x ∧ Real.sin x = 0 := by
  obtain ⟨n, hn⟩ := archimedean R
  exact ⟨natCast n * pi, lt_of_lt_of_le hn (natCast_le_natCast_mul_pi n), sin_natCast_mul_pi n⟩

-- `pi_div_two_pos` is NOT redefined here: it already exists in the corpus and became reachable
-- once this file imported `GaussianDiskSandwich` for `continuousAt_mul`. A first draft duplicated
-- it -- instantiate, don't rebuild, caught by the compiler rather than by me.

/-- `sin` is nonzero beyond every `R` — at `nπ + π/2`, where it equals `cos(nπ) = ±1`. -/
theorem sin_nonzero_beyond (R : Real) : ∃ x : Real, R < x ∧ Real.sin x ≠ 0 := by
  obtain ⟨n, hn⟩ := archimedean R
  have hlt1 : R < natCast n * pi := lt_of_lt_of_le hn (natCast_le_natCast_mul_pi n)
  have hlt2 : R < natCast n * pi + pi / (1 + 1) := by
    have h := add_lt_add_left pi_div_two_pos (natCast n * pi)
    rw [add_zero] at h
    exact lt_trans_ax hlt1 h
  refine ⟨natCast n * pi + pi / (1 + 1), hlt2, ?_⟩
  intro hzero
  rw [Real.sin_add, sin_natCast_mul_pi, sin_pi_div_two, cos_pi_div_two,
    mul_zero, zero_add, mul_one_ax] at hzero
  exact cos_natCast_mul_pi_ne_zero n hzero

/-- **`sin` lacks `TailSign`, re-derived from the criterion.** Subsumes the hand proof in
`WitnessResidualTailSign.lean` — same conclusion, no inlined Archimedean argument. -/
theorem sin_not_tailSign_via_criterion : ¬ TailSign Real.sin :=
  not_tailSign_of_zeros_and_nonzeros sin_zero_beyond sin_nonzero_beyond

/-! ## Two instances, and only the second is new reach

`a · sin` (below) is **NOT new** — it is periodic and nonconstant, so
`no_tree_eq_periodic_target` already had it. It is kept as a *cheapness* demonstration: the
criterion discharges it in four lines with no periodicity argument.

**`x · sin x` is the one that matters.** Its amplitude grows without bound, so it is not periodic
and **no periodic barrier reaches it** — the criterion does, because it never asked for a period. -/

/-- **`a · sin` lacks `TailSign` for every `a ≠ 0`.** Already covered by the periodic barrier;
included to show the criterion costs four lines where the periodic route costs a period and a
nonconstancy witness. -/
theorem const_mul_sin_not_tailSign {a : Real} (ha : a ≠ 0) :
    ¬ TailSign (fun x => a * Real.sin x) := by
  refine not_tailSign_of_zeros_and_nonzeros ?_ ?_
  · intro R
    obtain ⟨x, hx, hfx⟩ := sin_zero_beyond R
    exact ⟨x, hx, by show a * Real.sin x = 0; rw [hfx, mul_zero]⟩
  · intro R
    obtain ⟨x, hx, hfx⟩ := sin_nonzero_beyond R
    exact ⟨x, hx, by show a * Real.sin x ≠ 0; exact mul_ne_zero ha hfx⟩

/-- **`x · sin x` lacks `TailSign` — and THIS one the periodic barrier cannot reach.**

Zeros are `sin`'s zeros (`x · 0 = 0`). For the nonzeros the witness `nπ + π/2` must additionally be
shown **strictly positive**, so that the leading factor is nonzero — `natCast n · π ≥ 0` and
`π/2 > 0`. That extra step is the only difference from `a · sin`, and it is exactly what a growing
amplitude costs.

**Its amplitude is unbounded, so it is not periodic and `no_tree_eq_periodic_target` does not
apply.** *(That last sentence is an observation, not a theorem in this file — what is proved here
is the `TailSign` refutation.)* -/
theorem x_mul_sin_not_tailSign : ¬ TailSign (fun x => x * Real.sin x) := by
  refine not_tailSign_of_zeros_and_nonzeros ?_ ?_
  · intro R
    obtain ⟨x, hx, hfx⟩ := sin_zero_beyond R
    exact ⟨x, hx, by show x * Real.sin x = 0; rw [hfx, mul_zero]⟩
  · intro R
    obtain ⟨n, hn⟩ := archimedean R
    have hlt1 : R < natCast n * pi := lt_of_lt_of_le hn (natCast_le_natCast_mul_pi n)
    have hstep : natCast n * pi < natCast n * pi + pi / (1 + 1) := by
      have h := add_lt_add_left pi_div_two_pos (natCast n * pi)
      rwa [add_zero] at h
    have hxpos : (0 : Real) < natCast n * pi + pi / (1 + 1) :=
      lt_of_le_of_lt (mul_nonneg (natCast_nonneg n) (le_of_lt pi_pos)) hstep
    refine ⟨natCast n * pi + pi / (1 + 1), lt_trans_ax hlt1 hstep, ?_⟩
    show (natCast n * pi + pi / (1 + 1)) * Real.sin (natCast n * pi + pi / (1 + 1)) ≠ 0
    refine mul_ne_zero (ne_of_gt hxpos) ?_
    intro hzero
    rw [Real.sin_add, sin_natCast_mul_pi, sin_pi_div_two, cos_pi_div_two,
      mul_zero, zero_add, mul_one_ax] at hzero
    exact cos_natCast_mul_pi_ne_zero n hzero

/-- `fun y => y` is continuous — take `δ := ε`. Not in the corpus; one line here rather than a
detour, since `continuousAt_mul` (imported) supplies the product half. -/
theorem continuousAt_id (x : Real) : ContinuousAt (fun y : Real => y) x :=
  fun ε hε => ⟨ε, hε, fun _ hy => hy⟩

/-- **The exclusion, end to end, for `x · sin x`.** No finite EML tree equals it, at any depth —
via the criterion, with no periodicity anywhere in the argument. -/
theorem no_tree_eq_x_mul_sin (T : EMLTree)
    (heq : ∀ x : Real, T.eval x = x * Real.sin x) : False :=
  no_tree_eq_target_of_not_tailSign (fun x => x * Real.sin x) 0
    (fun x => continuousAt_mul (continuousAt_id x)
      (hasDerivAt_continuousAt (HasDerivAt_sin x)))
    (by
      have h := x_mul_sin_not_tailSign
      intro hts
      exact h (tailSign_congr_eventually 0 (fun x _ => sub_zero (x * Real.sin x)) hts))
    T heq

end Real
end MachLib
