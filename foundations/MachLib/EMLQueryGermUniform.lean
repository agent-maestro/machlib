import MachLib.EMLRayIdentity
import MachLib.EMLQueryGermNegBranch

/-!
# From interval-local bounds to `UniformZeroBoundFrom`

`(eo)` established that two of the query germ's three branches are interval-local, and `(ep)` supplied
the missing witness. This module does the join — **and does it once**, as a lemma about EML trees
rather than twice about germs, because the positive and negative branches differ only in which tree
they hand over.

## The one thing to be careful about

An over-eager join here would produce something that *looks* like a discharge of
`OneQueryDichotomy` and is not. So, stated plainly:

**This module does not discharge anything.** It upgrades two conditional bounds into two
`UniformZeroBoundFrom` producers. Composing all three branches into
`oneQueryDichotomy_of_uniformBoundsFrom`'s antecedent still needs the case split on
`ratGerm_eventual_sign`, and that antecedent is universally quantified over `N`, `P`, `Q` — the
ledger row stays open and the obligations gate will say so.
-/

namespace MachLib

open Real

/-- **The upgrade.** A tree agreeing with `f` on a ray, with log-positivity on every interval of
that ray, gives `f` a genuinely interval-independent bound: `encBound t`.

The two hypotheses are used in different places and both are needed. `hlog` on `Icc` feeds
`encBound_bounds`; the same hypothesis narrowed to the open interval feeds
`exists_nonzero_in_subinterval`, which is what supplies the per-interval nonzero witness that
`¬ EvZeroF` alone does not give. -/
theorem uniformZeroBoundFrom_of_rayTree (t : EMLTree) (f : Real → Real) (X : Real) (hX1 : 1 ≤ X)
    (hagree : ∀ x : Real, X ≤ x → t.eval x = f x)
    (hlog : ∀ a b : Real, X ≤ a → a < b → LogArgPosOn t (Icc a b))
    (hne : ¬ EvZeroF f) :
    UniformZeroBoundFrom f X (encBound t) := by
  have hposOpen : ∀ a b : Real, X ≤ a → a < b → LogArgPos t a b :=
    fun a b h1 h2 => LogArgPos_of_LogArgPosOn_Icc a b t (hlog a b h1 h2)
  -- `¬ EvZeroF f` transfers to the tree, since they agree past `X`
  have hnet : ¬ EvZeroF t.eval := by
    rintro ⟨Y, hY1, hY⟩
    have hY0 : (0 : Real) ≤ Y := le_trans (le_of_lt zero_lt_one_ax) hY1
    have hX0 : (0 : Real) ≤ X := le_trans (le_of_lt zero_lt_one_ax) hX1
    have hXsum : X ≤ X + Y := by
      have v := add_le_add_wit (le_refl X) hY0
      have e : X + (0 : Real) = X := by mach_ring
      rw [e] at v; exact v
    have hYsum : Y ≤ X + Y := by
      have v := add_le_add_wit hX0 (le_refl Y)
      have e : (0 : Real) + Y = Y := by mach_ring
      rw [e] at v; exact v
    refine hne ⟨X + Y, le_trans hX1 hXsum, ?_⟩
    intro x hx
    rw [← hagree x (le_trans hXsum hx)]
    exact hY x (le_trans hYsum hx)
  intro a b hXa hab zeros hnd hz
  obtain ⟨w, hw1, hw2, hw0⟩ :=
    exists_nonzero_in_subinterval t X hX1 hposOpen hnet a b hXa hab
  refine encBound_bounds t a b hab (hlog a b hXa hab) ⟨w, hw1, hw2, hw0⟩ zeros hnd ?_
  intro z hzmem
  obtain ⟨h1, h2, h0⟩ := hz z hzmem
  exact ⟨h1, h2, by rw [hagree z (le_trans hXa (le_of_lt h1))]; exact h0⟩

/-! ## The two interval-local branches, upgraded -/

/-- **Positive branch, uniform.** `u > 0` on the ray, so the `Fbasis` route applies and the tree is
`toEML (queryTerm N P Q)`. -/
theorem queryGerm_pos_branch_uniform (N : List (List Real)) (P Q : List Real)
    (X : Real) (hX1 : 1 ≤ X)
    (hQ : ∀ x : Real, X ≤ x → pev Q x ≠ 0)
    (hpos : ∀ x : Real, X ≤ x → 0 < pev P x / pev Q x)
    (hne : ¬ EvZeroF (fun x => bipev N x (Fbasis (pev P x / pev Q x)))) :
    UniformZeroBoundFrom (fun x => bipev N x (Fbasis (pev P x / pev Q x))) X
      (encBound (toEML (queryTerm N P Q))) := by
  refine uniformZeroBoundFrom_of_rayTree _ _ X hX1 ?_ ?_ hne
  · intro x hx
    rw [toEML_eval (queryTerm N P Q) x (queryTerm_divSafe N P Q x (hQ x hx)),
        queryTerm_eval]
  · intro a b hXa _
    exact logArgPosOn_toEML (queryTerm N P Q) (Icc a b)
      (fun x hx => queryTerm_divSafe N P Q x (hQ x (le_trans hXa hx.1)))
      (queryTerm_fArgsPos N P Q (Icc a b) (fun x hx => hpos x (le_trans hXa hx.1)))

/-- **Negative branch, uniform.** `u ≤ 0` on the ray, so `Fbasis u = exp u` and the tree is the
log-free `negGermTree`. Note the hypothesis list is *shorter* than the positive branch's — no
positivity — which is the same asymmetry `(eo)` recorded. -/
theorem queryGerm_neg_branch_uniform (N : List (List Real)) (P Q : List Real)
    (X : Real) (hX1 : 1 ≤ X)
    (hQ : ∀ x : Real, X ≤ x → pev Q x ≠ 0)
    (hneg : ∀ x : Real, X ≤ x → pev P x / pev Q x ≤ 0)
    (hne : ¬ EvZeroF (fun x => bipev N x (Fbasis (pev P x / pev Q x)))) :
    UniformZeroBoundFrom (fun x => bipev N x (Fbasis (pev P x / pev Q x))) X
      (encBound (negGermTree N P Q)) := by
  refine uniformZeroBoundFrom_of_rayTree _ _ X hX1 ?_ ?_ hne
  · intro x hx
    exact negGermTree_eval (hQ x hx) (hneg x hx)
  · intro a b hXa _
    exact negGermTree_logArgPos N P Q (Icc a b)
      (fun x hx => hQ x (le_trans hXa hx.1))

end MachLib
