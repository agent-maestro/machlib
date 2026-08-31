import MachLib.PolyFactor
import MachLib.PolyPEq
import MachLib.PolyMulDegree

/-!
# Towards lowest terms: the two steps a cancellation induction needs

`no_rational_logarithm` wants an irreducible `q` with `q ∣ Q` and `q ∤ P` — i.e. `P/Q` in lowest
terms at `q`. Reaching that is a cancellation with termination, and these are its two substantive
steps. Both turned out to be assemblies of existing `PolyPEq` and `PolyMulDegree` lemmas.

* **`cross_lift_of_common_factor`** — the cross-multiplied identity survives cancelling a common
  factor. Seven `PEq.trans` steps, every one an existing congruence.
* **`cofactor_length_lt`** — the cofactor is strictly shorter, because `PIrred q` carries
  `2 ≤ q.length` and `pmul_length` is exact on non-empty normal lists. This is what terminates the
  recursion.

## A note on how these were scoped

`(fv)` recorded these as "bookkeeping with named ingredients, not research", declined to build them
at the end of a long session, and they then took about twenty minutes. The estimate held **because it
was made from what the corpus contains** rather than from the shape of the argument — the same
discipline whose absence produced seven false absences the day before. `(fw)` records the sharpest of
those: a by-statement search that *errored* and was read as empty.
-/

namespace MachLib

theorem cross_lift_of_common_factor {P Q P₁ Q₁ P' Q' q : List Real}
    (hP : PEq P (pmul q P₁)) (hQ : PEq Q (pmul q Q₁))
    (h : PEq (pmul P₁ Q') (pmul P' Q₁)) :
    PEq (pmul P Q') (pmul P' Q) := by
  refine PEq.trans (peq_pmul hP (PEq.refl Q')) ?_
  refine PEq.trans (peq_pmul_assoc q P₁ Q') ?_
  refine PEq.trans (peq_pmul (PEq.refl q) h) ?_
  refine PEq.trans (PEq.symm (peq_pmul_assoc q P' Q₁)) ?_
  refine PEq.trans (peq_pmul (peq_pmul_comm q P') (PEq.refl Q₁)) ?_
  refine PEq.trans (peq_pmul_assoc P' q Q₁) ?_
  exact peq_pmul (PEq.refl P') (PEq.symm hQ)

/-- **The cofactor is strictly shorter.** `Q ≈ q·Q₁` with `q` irreducible (so `2 ≤ q.length`) forces
`Q₁.length < Q.length`, which is what makes the cancellation terminate. -/
theorem cofactor_length_lt {q Q Q₁ : List Real} (hq : PIrred q)
    (hQn : PNormal Q) (hQ₁n : PNormal Q₁) (hQ₁ne : Q₁ ≠ [])
    (hQ : PEq Q (pmul q Q₁)) : Q₁.length < Q.length := by
  have hqne : q ≠ [] := by
    intro h; rw [h] at hq; exact absurd hq.2.1 (by simp)
  have hEq : Q = pmul q Q₁ := by
    have h1 : pnorm Q = Q := pnorm_eq_self Q hQn
    have h2 : pnorm (pmul q Q₁) = pmul q Q₁ :=
      pnorm_eq_self _ (pmul_normal hq.1 hQ₁n hqne hQ₁ne)
    rw [← h1, hQ, h2]
  rw [hEq, pmul_length q Q₁ hqne hQ₁ne]
  have h2q : 2 ≤ q.length := hq.2.1
  have h1Q : 1 ≤ Q₁.length := by
    cases Q₁ with
    | nil => exact absurd rfl hQ₁ne
    | cons _ _ => simp
  omega

end MachLib
