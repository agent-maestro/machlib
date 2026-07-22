import MachLib.WitnessResidualTripleChain

/-! # `EMLNoCrossingAt` forces a global sign dichotomy — and exactly where that stops helping

Continuation of Option D (`EML_WITNESS_FINDING_DECISION_2026_07_15.md`), picking up the user's
explicit request to revisit the truly-general residual with a genuinely different idea, after
`WitnessResidualTripleChain.lean`'s five rounds of mechanical broadening (cont. 48-52) reached a
structurally-justified stopping point.

**The idea.** `EMLSmoothness.lean`'s `eml_log_arg_consistent_sign` (round 10, found during cont. 46
but never used until now) gives a sign dichotomy for `eml A B` on any BOUNDED interval from
`EMLNoCrossingAt` alone — `B` is either `≤ 0` throughout the interval or `> 0` throughout, never
mixed, with NO hypothesis about which. Stitching this across arbitrarily many overlapping bounded
intervals (any two points sit inside SOME shared interval) gives a genuinely GLOBAL dichotomy:
`EMLNoCrossingAt (eml A B)` holding for ALL `x` forces `B`'s sign to be globally consistent, full
stop — `eml_sign_dichotomy_global`. This is a real, general, previously-unexercised fact about
`EMLTree`, not specific to the nested-target family at all.

**What this buys directly.** `BChainTriple`'s non-positive-chain disjunct currently needs the
caller to already know `∀x, B.eval x ≤ 0` — a global fact, assumed rather than derived. Given
`EMLNoCrossingAt (eml A B)` everywhere and `B.eval x0 ≤ 0` at just ONE point, the dichotomy
upgrades that single-point fact to the full global one for free
(`no_eml_A_B_eq_nested_target_of_no_crossing_and_le_at_point`) — the same style of weakening
`WitnessResidualTripleChain.lean` already applied to the crossing disjunct (exact-zero → sign-change
via IVT), now applied to the non-positive-chain disjunct via a different tool (sign-consistency,
not IVT).

**Where it was pushed further, and where it genuinely stops — checked, not assumed.** The natural
next question: could `EMLNoCrossingAt T` holding globally, on its own, DERIVE `BChainTriple T`
entirely — replacing the whole hand-supplied witness with one purely structural hypothesis? Traced
this as a mutual/simultaneous induction (`EMLNoCrossingAt T` globally ⟹
`RightChildrenEverywherePositive T ∨ (T can't equal any nested-target member)`). The `B ≤ 0`
branch closes cleanly by the SAME recursion-into-`A` mechanism `BChainTriple` already uses. The
`B > 0` branch does NOT close: to conclude `RightChildrenEverywherePositive (eml A B)`, `A` needs
its OWN `RightChildrenEverywherePositive` fact — but the induction hypothesis on `A` only offers
`RightChildrenEverywherePositive A ∨ (A can't equal any nested-target member)`, and the SECOND
disjunct (a fact about `A` matching a DIFFERENT target family member) says nothing at all about
whether `A` is `RightChildrenEverywherePositive` — these are independent properties, not
complementary ones. The mutual recursion has no way to rule out "`A` is neither
`RightChildrenEverywherePositive` NOR provably matches no target" from what's in scope. This is a
genuine structural gap, confirmed by tracing the actual proof obligation, not a proof-effort
shortfall — consistent with round 19's original finding (`machlib-khovanskii-axiom-frontier.md`):
an unconstrained sibling is a real degree of freedom this style of argument cannot close.

**Net scope.** The dichotomy itself (`eml_sign_dichotomy_global`) is genuine, general, reusable
infrastructure regardless of this outcome. The concrete win is real but narrower than initially
hoped: it removes ONE hypothesis (the non-positive-chain's global fact, now derivable from a
single point plus `EMLNoCrossingAt`) rather than removing the need for `BChainTriple`'s witness
structure altogether. The fully general residual is exactly as open as
`WitnessResidualTripleChain.lean` left it.

`sorryAx`-free, verified via a genuinely fresh rebuild. Compiled clean on the first attempt for
every theorem. No `eml_pfaffian_validon_from_sin_equality` dependence. -/

namespace MachLib
namespace Real

/-- If `B`'s sign is `≤0` at ANY one point and `EMLNoCrossingAt (eml A B)` holds EVERYWHERE, `B`'s
sign is `≤0` EVERYWHERE — derived, not assumed. Via `eml_log_arg_consistent_sign`
(`EMLSmoothness.lean`, round 10): applied to the interval between the two points, the local
dichotomy can't go the other way without contradicting the known point. -/
theorem eml_sign_le_propagates {A B : EMLTree}
    (hnc : ∀ x : Real, MachLib.EMLNoCrossingAt (EMLTree.eml A B) x) (x0 x1 : Real)
    (hx0 : B.eval x0 ≤ 0) : B.eval x1 ≤ 0 := by
  rcases lt_total x0 x1 with hlt | heq | hgt
  · have hd := MachLib.eml_log_arg_consistent_sign hlt (fun z hz1 hz2 => hnc z)
    rcases hd with h | h
    · exact h x1 (le_of_lt hlt) (le_refl x1)
    · exfalso
      have hbp : 0 < B.eval x0 := h x0 (le_refl x0) (le_of_lt hlt)
      exact lt_irrefl_ax 0 (lt_of_lt_of_le hbp hx0)
  · rw [← heq]; exact hx0
  · have hd := MachLib.eml_log_arg_consistent_sign hgt (fun z hz1 hz2 => hnc z)
    rcases hd with h | h
    · exact h x1 (le_refl x1) (le_of_lt hgt)
    · exfalso
      have hbp : 0 < B.eval x0 := h x0 (le_of_lt hgt) (le_refl x0)
      exact lt_irrefl_ax 0 (lt_of_lt_of_le hbp hx0)

theorem eml_le_everywhere_of_no_crossing_and_le_at_point {A B : EMLTree}
    (hnc : ∀ x : Real, MachLib.EMLNoCrossingAt (EMLTree.eml A B) x) (x0 : Real)
    (hx0 : B.eval x0 ≤ 0) : ∀ x : Real, B.eval x ≤ 0 :=
  fun x1 => eml_sign_le_propagates hnc x0 x1 hx0

/-- Mirror of `eml_sign_le_propagates`: positivity at one point propagates everywhere too. -/
theorem eml_sign_pos_propagates {A B : EMLTree}
    (hnc : ∀ x : Real, MachLib.EMLNoCrossingAt (EMLTree.eml A B) x) (x0 x1 : Real)
    (hx0 : 0 < B.eval x0) : 0 < B.eval x1 := by
  rcases lt_total x0 x1 with hlt | heq | hgt
  · have hd := MachLib.eml_log_arg_consistent_sign hlt (fun z hz1 hz2 => hnc z)
    rcases hd with h | h
    · exfalso
      have hbp : B.eval x0 ≤ 0 := h x0 (le_refl x0) (le_of_lt hlt)
      exact lt_irrefl_ax 0 (lt_of_lt_of_le hx0 hbp)
    · exact h x1 (le_of_lt hlt) (le_refl x1)
  · rw [← heq]; exact hx0
  · have hd := MachLib.eml_log_arg_consistent_sign hgt (fun z hz1 hz2 => hnc z)
    rcases hd with h | h
    · exfalso
      have hbp : B.eval x0 ≤ 0 := h x0 (le_of_lt hgt) (le_refl x0)
      exact lt_irrefl_ax 0 (lt_of_lt_of_le hx0 hbp)
    · exact h x1 (le_refl x1) (le_of_lt hgt)

/-- **The full dichotomy**: `EMLNoCrossingAt` everywhere alone already forces `B`'s sign to be
GLOBALLY consistent, no per-point hypothesis needed at all — pick any reference point and use
`lt_total` on its own sign. -/
theorem eml_sign_dichotomy_global {A B : EMLTree}
    (hnc : ∀ x : Real, MachLib.EMLNoCrossingAt (EMLTree.eml A B) x) :
    (∀ x : Real, B.eval x ≤ 0) ∨ (∀ x : Real, 0 < B.eval x) := by
  rcases lt_total (B.eval 0) 0 with hlt | heq | hgt
  · exact Or.inl (eml_le_everywhere_of_no_crossing_and_le_at_point hnc 0 (le_of_lt hlt))
  · exact Or.inl (eml_le_everywhere_of_no_crossing_and_le_at_point hnc 0 (le_of_eq heq))
  · exact Or.inr (fun x1 => eml_sign_pos_propagates hnc 0 x1 hgt)

/-- The non-positive chain's hypothesis, weakened: `EMLNoCrossingAt` everywhere plus `B ≤ 0` at a
SINGLE point, instead of `B ≤ 0` at EVERY point directly. -/
theorem no_eml_A_B_eq_nested_target_of_no_crossing_and_le_at_point
    (A B : EMLTree) (hnc : ∀ x : Real, MachLib.EMLNoCrossingAt (EMLTree.eml A B) x)
    (x0 : Real) (hx0 : B.eval x0 ≤ 0)
    (cs : List Real) (hwf : nestedWF cs)
    (hT1eq : ∀ x : Real, (EMLTree.eml A B).eval x = nestedTarget cs x)
    (hAchain : BChainTriple A) : False :=
  no_tree_eq_nested_target_of_BChainTriple (EMLTree.eml A B)
    (Or.inr (Or.inr ⟨eml_le_everywhere_of_no_crossing_and_le_at_point hnc x0 hx0, hAchain⟩))
    cs hwf hT1eq

end Real
end MachLib
