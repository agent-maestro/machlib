import MachLib.QuantitativeNonApproximation
import MachLib.WitnessResidualDeepGSignControl

/-!
# C7: the Certcom handshake — an abstract total-error floor, scoped honestly

Track C, item C7. One of the two muses flagged this as "thesis-shaped, not lemma-shaped," and this
file does NOT dispute that framing — it builds the one piece that genuinely IS lemma-shaped
(combining C6's approximation floor with an ABSTRACT rounding-error bound via the triangle
inequality) and stops there, deliberately not touching Certcom's actual C-compilation pipeline
(the soundness witness arc, `project_certcom_soundness_witness` in agent memory — 74/74 axioms
witnessed, EML→C fully closed) or its 14-primitive `real_*_eps`/`real_*_rounds` libm rounding
model (`AxiomLedger.lean`'s `disclosedTrusted`). Wiring THIS theorem to THAT machinery — proving
the abstract `hround` hypothesis below from Certcom's actual rounding axioms for a specific
compiled artifact — is the genuinely thesis-shaped remaining work: it would need a real EML tree
`T` meant as a `sin`-approximation kernel, Certcom's compilation of it to C, and the rounding bound
Certcom actually proves for that pipeline. Not attempted here.

**What IS built:** for ANY finite EML tree `T` and ANY `compiled : Real → Real` whose deviation
from `T.eval` is bounded by `δ` everywhere (the SHAPE of bound Certcom's rounding theorems
supply, held abstract rather than imported), if `δ < ε < 1`, there are points arbitrarily far out
where the TOTAL error between `compiled` and the true `Real.sin` is at least `ε - δ` — not just the
representability gap (C6) or the rounding error (Certcom) in isolation, but the floor on their SUM,
via the reverse triangle inequality. No matter how good the floating-point implementation of `T` is
(how small `δ` gets), `T`'s own eventual departure from `sin` (C6) survives past any threshold: it
can be masked by rounding error only up to `δ`, never fully absorbed, since `δ < ε`. -/

namespace MachLib
namespace Real

open MachLib

/-- **The abstract total-error floor.** No matter how tight the rounding bound `δ` on a compiled
artifact is (as long as `δ < ε < 1`), there are points arbitrarily far out where the compiled
artifact's TOTAL deviation from `Real.sin` is at least `ε - δ`. -/
private theorem lt_of_not_le {a b : Real} (h : ¬ a ≤ b) : b < a := by
  rcases lt_total a b with hab | hab | hab
  · exact absurd (le_of_lt hab) h
  · exact absurd (le_of_eq hab) h
  · exact hab

theorem certcom_total_error_floor (T : EMLTree) (ε δ : Real) (hε : ε < 1) (hδε : δ < ε)
    (compiled : Real → Real) (hround : ∀ x : Real, abs (compiled x - T.eval x) ≤ δ)
    (R : Real) : ∃ x : Real, R < x ∧ ε - δ ≤ abs (compiled x - Real.sin x) := by
  apply Classical.byContradiction
  intro hcon
  apply no_tree_eps_close_to_sin_eventually T ε hε R
  intro x hx
  have h1 := hround x
  have h2 : abs (compiled x - Real.sin x) < ε - δ := by
    apply lt_of_not_le
    intro hge
    exact hcon ⟨x, hx, hge⟩
  have h3 : abs (T.eval x - Real.sin x) ≤ abs (T.eval x - compiled x) + abs (compiled x - Real.sin x) := by
    have e : T.eval x - Real.sin x = (T.eval x - compiled x) + (compiled x - Real.sin x) := by mach_ring
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

end Real
end MachLib
