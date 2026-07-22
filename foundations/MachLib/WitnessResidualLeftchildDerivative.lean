import MachLib.WitnessResidualGlobalSignDichotomy

/-! # `A`'s derivative, unconditionally — and the sharpest characterization yet of why it still
doesn't close the general residual

Continuation of Option D (`EML_WITNESS_FINDING_DECISION_2026_07_15.md`), per the explicit request
to keep pushing into the genuinely open, fully-general case after cont. 53 found a real (not just
effort-limited) wall in the "B positive" branch of the `EMLNoCrossingAt`-globally mutual induction.

**The new tool.** `EMLSmoothness.lean`'s `eml_leftchild_hasDerivAt_general` (built in the prequel
investigation for witness-FINDING, never repurposed for this arc's negative-direction closure
until now) gives `A`'s own derivative UNCONDITIONALLY — not branching on `B`'s sign at all, unlike
every mechanism built in `WitnessResidualTripleChain.lean`/`WitnessResidualGlobalSignDichotomy.lean`.
Given only `EMLNoCrossingAt (eml A B) x` at a single point (supplying `B`'s own derivative and
`B.eval x ≠ 0`) plus the target's known derivative (`nestedTarget_hasDerivAt`, cont. 43), `A`
differentiates at that point — REGARDLESS of whether `B` is positive, negative, or would otherwise
need one of the three existing mechanisms to pin down. `A_hasDerivAt_of_no_crossing_at_point`
instantiates this for the nested-target family directly.

**Why this looked promising.** The mechanism works by an algebraic identity
(`eml_leftchild_explicit_value`): rearranging `exp(A.eval x) − log(B.eval x) = target x` gives
`A.eval x = log(target x + log(B.eval x))` UNCONDITIONALLY (the inner sum
`target x + log(B.eval x)` always equals `exp(A.eval x)`, hence is always strictly positive — no
case split on the outer `log`'s branch needed at all). If `B` were ALSO known differentiable
(e.g. via `B`'s own `EMLNoCrossingAt`), the whole right-hand side differentiates by the ordinary
chain rule, transferring to `A.eval` via `HasDerivAt_of_eq`. This sidesteps needing to know
anything about `A`'s OWN internal structure — precisely the kind of "free" fact that closed other
pieces of this arc.

**Where it stops — traced precisely, confirming (a FOURTH independent time) the same root
obstruction.** `A`'s derivative alone does not give `EMLNoCrossingAt A` (a STRUCTURAL fact about
`A`'s own internal log-arguments avoiding the clamp) — external differentiability via composition
is not the same as internal structural validity, the exact distinction `WitnessResidualClosureAttempt.lean`
(cont. 43) drew between `T1`'s transported differentiability and its structural one. Worse: `A`'s
own "effective target" — the function it would need to match to recurse the way the `B ≤ 0` branch
does — is `fun x => log(target x + log(B.eval x))`, which is NOT independent of `B`. Unlike the
`B ≤ 0` case (where `log(B.eval x)` collapses to the CONSTANT `0`, eliminating `B` entirely and
giving `A.eval x = nestedTarget (0 :: cs) x` with no `B`-dependence left), the general case leaves
`log(B.eval x)` as a genuine, non-eliminable perturbation term. Nothing about `A` can be pinned
down without already knowing this term — which is exactly what's unconstrained.

This is the SAME obstruction found three times before, from three independent angles, now
confirmed a fourth way: prequel round 19 (`machlib-khovanskii-axiom-frontier.md`, witness-finding:
"a sibling subtree that stays bounded well above the needed threshold everywhere defeats the
propagation... a real degree of freedom"), `WitnessResidualClosureAttempt.lean` cont. 43 (the
"ambiguous set" where `exp(A(x)) = target(x)` exactly), and `WitnessResidualGlobalSignDichotomy.lean`
cont. 53 (the `B > 0` branch of the mutual induction needing `A`'s own
`RightChildrenEverywherePositive`, unavailable from the induction hypothesis). Four different
proof attempts, four different technical framings, the same underlying fact: an unconstrained
sibling subtree's contribution is irreducible by any elementary technique tried across this whole
multi-week, 53-round investigation (this document) plus its 30-round prequel. Also checked and
ruled out this round: `EMLAsymptoticBound.lean`'s `Tame`/`iter_exp` growth-rate machinery (a
SEPARATE, earlier body of work, predating even the Khovanskii investigation) — its own docstring
states plainly it does NOT cover the clamped-log case, which is exactly this residual's territory,
so it is not an available shortcut either.

**Assessment.** At this point, closing the fully general residual very likely needs the genuinely
new machinery flagged as far back as prequel round 7: a Taylor-coefficient/Faa-di-Bruno matching
argument, explicitly estimated there as comparable in scale to formalizing a fragment of Wilkie's
own o-minimality proof technique — a dedicated, multi-session research undertaking, not a next
increment on anything built so far. `A_hasDerivAt_of_no_crossing_at_point` remains genuine, real,
reusable infrastructure (differentiability transfer to `A` with zero dependence on `B`'s sign,
usable anywhere that's needed regardless of this residual), but it does not move the wall.

`sorryAx`-free, verified via a genuinely fresh rebuild. No `eml_pfaffian_validon_from_sin_equality`
dependence. -/

namespace MachLib
namespace Real

/-- `A`'s own derivative, unconditionally — not branching on `B`'s sign at all, unlike everything
built in this arc so far. Just instantiates `eml_leftchild_hasDerivAt_general`
(`EMLSmoothness.lean`) with `TARGET := nestedTarget cs`. -/
theorem A_hasDerivAt_of_no_crossing_at_point (A B : EMLTree) (cs : List Real) (hwf : nestedWF cs)
    (hT1eq : ∀ x : Real, (EMLTree.eml A B).eval x = nestedTarget cs x) (x : Real)
    (hnc : MachLib.EMLNoCrossingAt (EMLTree.eml A B) x) :
    ∃ D : Real, HasDerivAt A.eval D x := by
  obtain ⟨_, hncB, hBne⟩ := hnc
  obtain ⟨c, hc⟩ := MachLib.eml_hasDerivAt_of_no_crossing B x hncB
  obtain ⟨d, hd⟩ := nestedTarget_hasDerivAt cs hwf x
  exact MachLib.eml_leftchild_hasDerivAt_general hT1eq hd hc hBne

end Real
end MachLib
