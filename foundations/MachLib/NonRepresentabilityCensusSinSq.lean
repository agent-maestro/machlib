import MachLib.CertcomTotalErrorFloor
import MachLib.WitnessResidualContinuousTargetMetaLemma

/-!
# C8: non-representability census — one genuinely new target, via the general meta-theorem

Track C, item C8. The muses' proposal named a "battery" including Painlevé transcendents from the
chain-5 census — checked and set aside: those aren't formalized as concrete `Real → Real` Lean
functions anywhere in this codebase (the chain-5 census, per agent memory, is a classification
result, not an implemented function library), so instantiating the meta-theorem for them would mean
formalizing them first — a large, separate undertaking, not a mechanical census entry. What IS
mechanical, and genuinely demonstrates `no_tree_eq_target_of_not_tailSign`'s reusability rather than
just restating `sin`/`nestedTarget` again: `sin²x` (`Real.sin x * Real.sin x`), a target with a
DIFFERENT oscillation shape than everything else this arc has used — always non-negative, recurring
to exactly `0` (at every `kπ`) and exactly `1` (wherever `sin` itself hits `±1`), rather than
recurring to two SIGNED extremes. One instantiation, honestly scoped as one, not an exhaustive
battery.
-/

namespace MachLib
namespace Real

open MachLib

private theorem sinSq_continuousAt (x : Real) : ContinuousAt (fun y => Real.sin y * Real.sin y) x :=
  hasDerivAt_continuousAt (HasDerivAt_mul Real.sin Real.sin (Real.cos x) (Real.cos x) x
    (HasDerivAt_sin x) (HasDerivAt_sin x))

/-- `sin²x` never settles: it recurs to exactly `0` (`sin(nπ)=0`, `sin_natCast_mul_pi`, archimedean
past any threshold — the SAME argument `sin_not_tailSign`'s `.pos`/`.neg` cases use) and to exactly
`1` (`sin_one_recurring`, already built for C6). Neither eventually-positive, eventually-negative,
nor eventually-exactly-`0` survives both recurring facts at once. -/
theorem sinSq_not_tailSign : ¬ TailSign (fun x => Real.sin x * Real.sin x - 0) := by
  intro h
  rcases h with ⟨R, hR⟩ | ⟨R, hR⟩ | ⟨R, hR⟩
  · obtain ⟨n, hn⟩ := archimedean R
    have hlt : R < natCast n * pi := lt_of_lt_of_le hn (natCast_le_natCast_mul_pi n)
    have hpos := hR (natCast n * pi) hlt
    rw [sin_natCast_mul_pi, mul_zero, sub_zero] at hpos
    exact lt_irrefl_ax 0 hpos
  · obtain ⟨n, hn⟩ := archimedean R
    have hlt : R < natCast n * pi := lt_of_lt_of_le hn (natCast_le_natCast_mul_pi n)
    have hneg := hR (natCast n * pi) hlt
    rw [sin_natCast_mul_pi, mul_zero, sub_zero] at hneg
    exact lt_irrefl_ax 0 hneg
  · obtain ⟨x, hxR, hsinx⟩ := sin_one_recurring R
    have hz := hR x hxR
    rw [hsinx, mul_one_ax, sub_zero] at hz
    exact zero_ne_one_ax hz.symm

/-- **`sin²x` is not EML-representable, by the same general mechanism, no `sin`/`nestedTarget`-
specific reasoning needed.** Direct instantiation of `no_tree_eq_target_of_not_tailSign`. -/
theorem no_tree_eq_sinSq_unconditional (T : EMLTree) (heq : ∀ x : Real, T.eval x = Real.sin x * Real.sin x) :
    False :=
  no_tree_eq_target_of_not_tailSign (fun x => Real.sin x * Real.sin x) 0 sinSq_continuousAt
    sinSq_not_tailSign T heq

end Real
end MachLib
