import MachLib.CompactIntervalNonApproximation
import MachLib.CertcomTotalErrorFloor

/-!
# The real Certcom handshake: total-error floor, compact-interval form

Combines the two halves the cont. 76 erratum kept explicitly separate: `certcom_total_error_floor`
(C7, the abstract rounding-bound combinator, via the reverse triangle inequality) with
`no_tree_eps_close_to_sin_compact_interval` (cont. 80, the EXPLICIT tree-structure-computed
non-approximation floor) instead of `no_tree_eps_close_to_sin_eventually` (C6, tail-only).

**What this closes, stated precisely.** For a compiled artifact whose rounding error stays within
`δ` of a `EMLPfaffianValidOn` tree throughout an interval `(A, B)` long enough to hold `M + 1`
alternating extrema (`M` explicit, from `combinedBoundE`) — NOT "eventually," an actual bounded
operating range a real compiled kernel would use — there is a POINT WITHIN THAT INTERVAL where the
artifact's total deviation from true `sin` is at least `ε − δ`. This is the practically relevant
form: a real compiled sin-approximation kernel runs on a fixed, bounded domain, not `x → ∞`, so this
is the theorem that actually bears on it, not the tail version.

**What remains genuinely open, unchanged from C7's own scoping.** `hround` here is still an
ABSTRACT hypothesis — the shape Certcom's rounding theorems supply, not derived from Certcom's
actual `real_*_eps`/`real_*_rounds` axioms for a specific compiled pipeline. Proving `hround` FROM
that real machinery, for a real EML tree meant as a `sin`-approximation kernel and its actual
Certcom-compiled C artifact, remains the thesis-shaped work neither this file nor `CertcomTotal
ErrorFloor.lean` attempts.
-/

namespace MachLib
namespace Real

open MachLib
open MachLib.EMLExplicitBound

/-- **The compact-interval Certcom handshake.** No matter how tight the rounding bound `δ` on a
compiled artifact is (as long as `δ < ε < 1`), once the shared operating interval `(A, B)` is long
enough to hold `M + 1` alternating extrema (`M` explicit, from the tree's own structure), there is
a point WITHIN `(A, B)` — not merely "arbitrarily far out" — where the compiled artifact's total
deviation from `Real.sin` is at least `ε − δ`. -/
theorem certcom_total_error_floor_compact_interval (T : EMLTree) (A B ε δ : Real)
    (hA0 : A < ext 0) (hεlt1 : ε < 1) (hδε : δ < ε) (hvalidon : EMLPfaffianValidOn T A B)
    (compiled : Real → Real) (hround : ∀ x : Real, A < x → x < B → abs (compiled x - T.eval x) ≤ δ)
    (hMB : ext (combinedBoundE (len T 0) (enc T emlEmptyChain).1
        (encTags T emlEmptyChain ()) (enc T emlEmptyChain).2 + 1) < B) :
    ∃ x : Real, A < x ∧ x < B ∧ ε - δ ≤ abs (compiled x - Real.sin x) := by
  apply Classical.byContradiction
  intro hcon
  apply no_tree_eps_close_to_sin_compact_interval T A B ε hA0 hεlt1 hvalidon
  · intro x hxA hxB
    have h1 := hround x hxA hxB
    have h2 : abs (compiled x - Real.sin x) < ε - δ := by
      apply lt_of_not_le
      intro hge
      exact hcon ⟨x, hxA, hxB, hge⟩
    have h3 : abs (T.eval x - Real.sin x) ≤
        abs (T.eval x - compiled x) + abs (compiled x - Real.sin x) := by
      have e : T.eval x - Real.sin x = (T.eval x - compiled x) + (compiled x - Real.sin x) := by
        mach_ring
      rw [e]; exact abs_add _ _
    have h4 : abs (T.eval x - compiled x) = abs (compiled x - T.eval x) := by
      rw [show T.eval x - compiled x = -(compiled x - T.eval x) from by mach_ring, abs_neg]
    rw [h4] at h3
    have h5 : abs (compiled x - T.eval x) + abs (compiled x - Real.sin x)
        ≤ δ + abs (compiled x - Real.sin x) := add_le_add h1 (le_refl _)
    have h6 : δ + abs (compiled x - Real.sin x) < δ + (ε - δ) := add_lt_add_left h2 δ
    have h7 : δ + (ε - δ) = ε := by mach_ring
    rw [h7] at h6
    exact lt_of_le_of_lt (le_trans h3 h5) h6
  · exact hMB

end Real
end MachLib
