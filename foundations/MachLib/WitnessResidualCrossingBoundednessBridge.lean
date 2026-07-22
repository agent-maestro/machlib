import MachLib.WitnessResidualNonposChainClosure
import MachLib.WitnessResidualCrossingUnboundedGeneral
import MachLib.EMLSmoothness

/-! # Closing the mixed-sign gap for concrete crossing shapes: the boundedness/unboundedness bridge

Continuation of Option D (`EML_WITNESS_FINDING_DECISION_2026_07_15.md`).
`WitnessResidualNonposChainClosure.lean` closed the residual for trees whose right children are
`≤ 0` everywhere down the left spine, and flagged an unexplored lead in its own docstring: a right
child that takes BOTH signs is, by definition, a crossing in the sense already proven in
`WitnessResidualCrossingUnboundedGeneral.lean`, and `nestedTarget cs` is bounded — so if a
crossing right child's unboundedness could be established, it would directly contradict the
target family's boundedness. This file realizes that connection for real, and finds it is
stronger and more general than the "mixed-sign" framing suggested.

**The bridge, in one lemma (`no_eml_A_B_eq_nested_target_of_unbounded_above`).** Any right child
`B` that provably forces `eml A B` unbounded above — by ANY means, not just the crossing
machinery — immediately rules out matching ANY member of the nested-target family, since the
family is bounded above by `nestedHi cs` (`nestedTarget_facts`). Two lines: extract a witness `x`
with `(eml A B).eval x > nestedHi cs`, substitute the equality hypothesis, contradict the range
fact. This is the first place in the whole arc where the crossing-unboundedness sub-arc
(cont. 37-39) and the nested-target boundedness sub-arc connect directly.

**Two concrete shapes close unconditionally, no case split on `cs` at all.** The earlier
"mixed-sign" framing assumed closing this gap would need `B`'s differentiability established for
an ARBITRARY, unknown compound tree — the same "no known closed form to transport from" wall as
`WitnessResidualClosureAttempt.lean`. But that wall only applies to a truly UNKNOWN `B`. For
CONCRETE, SPECIFIC crossing shapes, differentiability is already proven, unconditionally, with no
transport needed at all:
- `B = var` (`no_eml_A_var_eq_nested_target`): `var` crosses zero at `0`/`1` and is
  unconditionally differentiable (`HasDerivAt_id` — `var`'s closed form IS `id`, known outright).
  Closes `eml A var` against the whole family, for ANY `A`, regardless of `nestedLo cs`'s sign —
  strictly stronger than the pointwise `nestedLo cs ≤ 0`-only result below.
- `B = eml var (const c)`, `c > 1` (`no_eml_A_evarConstC_eq_nested_target`): the ORIGINAL crossing
  primitive this entire 40+-file arc was built around
  (`WitnessResidualCrossingUnbounded.lean`, cont. 37), reusing the already-proven
  `eml_A_crossing_var_const_unbounded_above_via_general`. Closes unconditionally too, for ANY `A`,
  ANY `c > 1`.

**A separate, complementary pointwise result** (`no_eml_eq_nested_target_of_B_neg_pi_div_two_nonpos`):
the immediate-contradiction branch of `BChainNonpos`'s induction never actually needed `B ≤ 0`
EVERYWHERE — only at the single point `-π/2` — so it generalizes to ANY `A`, ANY `B` (no crossing,
no differentiability needed at all) whenever `nestedLo cs ≤ 0`. Weaker than the bridge for shapes
that happen to be provably-unbounded (like `var`), but applicable to shapes that AREN'T crossings
at all (e.g. a compound `B` that dips non-positive at exactly that one point without crossing
zero elsewhere) — a genuinely different, non-overlapping coverage axis.

**The two named shapes generalize, via infrastructure that was already sitting in the codebase.**
`EMLSmoothness.lean` (a separate, earlier sub-arc toward closing
`eml_pfaffian_validon_from_sin_equality` directly, predating the `WitnessResidual*` naming
convention, already wired into a dozen `WitnessResidual*` files) proves
`eml_hasDerivAt_of_no_crossing`: ANY `EMLTree` is differentiable at `x`, given the purely LOCAL,
non-circular, structurally-checkable condition `EMLNoCrossingAt s x` (no internal log-argument
lands exactly on `0` at that point — strictly weaker than `EMLPfaffianValidOn`, provable by plain
structural induction with no reference to siblings or ancestors). Feeding this into the crossing
machinery (`no_eml_A_B_eq_nested_target_of_crossing_and_no_crossing`) closes the residual for ANY
`B` — not just `var` or `eml var (const c)` — that genuinely crosses zero on some `[x0, x1]` and
satisfies `EMLNoCrossingAt` throughout that interval. `var` and `eml var (const c)` are the two
cases where that side condition was already known unconditionally; this generalizes the SAME
argument to any future candidate `B` a checkable structural condition, not a from-scratch
differentiability proof, away.

**What is still open, stated plainly.** A fully GENERAL, truly UNKNOWN compound `B` — no promise
of a genuine crossing, no promise of `EMLNoCrossingAt` on the relevant interval — remains exactly
as open as `WitnessResidualClosureAttempt.lean` left it: `EMLNoCrossingAt` is a real hypothesis,
not derivable from nothing, same as the crossing values themselves. This file closes two concrete
named shapes, one pointwise-general-but-crossing-agnostic case, and one broad-but-still-
conditional structural class — not the fully general induction the residual ultimately needs. The
value here is the two BRIDGE lemmas (`no_eml_A_B_eq_nested_target_of_unbounded_above` and its
`EMLNoCrossingAt` specialization) — genuinely general, reusable for ANY future crossing shape this
codebase can establish unbounded (by hand OR via `EMLNoCrossingAt`), without redoing the
boundedness-contradiction argument each time.

`sorryAx`-free, verified via a genuinely fresh rebuild for every theorem in this file. No
`EMLPfaffianValidOn`, no `eml_pfaffian_validon_from_sin_equality` dependence anywhere. -/

namespace MachLib
namespace Real

/-- Generalization of the immediate-contradiction branch of
`no_tree_eq_nested_target_of_BChainNonpos`: it never actually needed `B ≤ 0` EVERYWHERE, only at
the single point `-π/2`. Works for ANY `A`, ANY `B`, no recursion, no structural hypothesis on
either subtree at all. -/
theorem no_eml_eq_nested_target_of_B_neg_pi_div_two_nonpos
    (A B : EMLTree) (cs : List Real) (hwf : nestedWF cs) (hlo : nestedLo cs ≤ 0)
    (hT1eq : ∀ x : Real, (EMLTree.eml A B).eval x = nestedTarget cs x)
    (hBnp : B.eval (-(pi / (1 + 1))) ≤ 0) : False := by
  have heq : Real.exp (A.eval (-(pi / (1 + 1)))) - Real.log (B.eval (-(pi / (1 + 1))))
      = nestedTarget cs (-(pi / (1 + 1))) := hT1eq (-(pi / (1 + 1)))
  rw [log_nonpos hBnp, sub_zero, nestedTarget_at_neg_pi_div_two cs hwf] at heq
  have hpos := Real.exp_pos (A.eval (-(pi / (1 + 1))))
  rw [heq] at hpos
  exact lt_irrefl_ax 0 (lt_of_lt_of_le hpos hlo)

theorem neg_pi_div_two_nonpos : -(pi / (1 + 1)) ≤ 0 := by
  have h11 : (0 : Real) < 1 + 1 := by
    have h := add_lt_add_left zero_lt_one_ax 1
    rw [add_zero] at h
    exact lt_trans_ax zero_lt_one_ax h
  have hpos : (0 : Real) < pi / (1 + 1) := div_pos_of_pos_pos pi_pos h11
  exact neg_nonpos_of_nonneg (le_of_lt hpos)

/-- Concrete corollary: a non-positive constant right child, whenever `nestedLo cs ≤ 0`.
(Subsumed for `k ≤ 0` by `no_tree_eq_nested_target_of_BChainNonpos` when `A` also chains, but this
version needs nothing about `A` at all — useful standalone when `A` is otherwise unconstrained.) -/
theorem no_eml_A_const_eq_nested_target_of_lo_nonpos
    (A : EMLTree) (k : Real) (hk : k ≤ 0) (cs : List Real) (hwf : nestedWF cs)
    (hlo : nestedLo cs ≤ 0)
    (hT1eq : ∀ x : Real, (EMLTree.eml A (EMLTree.const k)).eval x = nestedTarget cs x) : False :=
  no_eml_eq_nested_target_of_B_neg_pi_div_two_nonpos A (EMLTree.const k) cs hwf hlo hT1eq hk

/-- **The general bridge.** Any right child that provably forces `eml A B` unbounded above
immediately rules out matching ANY member of the nested-target family — the family is bounded
above by `nestedHi cs`. -/
theorem no_eml_A_B_eq_nested_target_of_unbounded_above
    (A B : EMLTree) (cs : List Real) (hwf : nestedWF cs)
    (hunbdd : ∀ M : Real, ∃ x : Real, M < (EMLTree.eml A B).eval x)
    (hT1eq : ∀ x : Real, (EMLTree.eml A B).eval x = nestedTarget cs x) : False := by
  obtain ⟨hrange, _, _⟩ := nestedTarget_facts cs hwf
  obtain ⟨x, hx⟩ := hunbdd (nestedHi cs)
  rw [hT1eq x] at hx
  exact lt_irrefl_ax (nestedHi cs) (lt_of_lt_of_le hx (hrange x).2)

/-- `var` genuinely crosses zero (`var.eval 0 = 0`, `var.eval 1 = 1 > 0`) and is unconditionally
differentiable (`HasDerivAt_id` — `var`'s closed form IS `id`, known outright, no transport
needed), so `eml_A_crossing_B_unbounded_above` applies with zero extra work. -/
theorem eml_A_var_unbounded_above (A : EMLTree) (M : Real) :
    ∃ x : Real, M < (EMLTree.eml A EMLTree.var).eval x :=
  eml_A_crossing_B_unbounded_above A EMLTree.var 0 1 zero_lt_one_ax rfl zero_lt_one_ax
    (fun z _ _ => ⟨1, HasDerivAt_id z⟩) M

/-- **No tree with `var` as its immediate right child can equal ANY member of the nested-target
family, for ANY `A`, unconditionally** — stronger than the `nestedLo cs ≤ 0`-only pointwise
result above; no case split on `cs` needed at all. -/
theorem no_eml_A_var_eq_nested_target
    (A : EMLTree) (cs : List Real) (hwf : nestedWF cs)
    (hT1eq : ∀ x : Real, (EMLTree.eml A EMLTree.var).eval x = nestedTarget cs x) : False :=
  no_eml_A_B_eq_nested_target_of_unbounded_above A EMLTree.var cs hwf (eml_A_var_unbounded_above A)
    hT1eq

/-- Same bridge argument, applied to `eml var (const c)` — the ORIGINAL crossing primitive this
whole 40+-file arc was built around (`WitnessResidualCrossingUnbounded.lean`, cont. 37), reusing
`eml_A_crossing_var_const_unbounded_above_via_general`'s already-proven unboundedness. Closes this
concrete shape unconditionally too, for ANY `A`, ANY `c > 1`. -/
theorem no_eml_A_evarConstC_eq_nested_target
    (A : EMLTree) (c : Real) (hc : 1 < c) (cs : List Real) (hwf : nestedWF cs)
    (hT1eq : ∀ x : Real,
      (EMLTree.eml A (EMLTree.eml EMLTree.var (EMLTree.const c))).eval x = nestedTarget cs x) :
    False :=
  no_eml_A_B_eq_nested_target_of_unbounded_above A (EMLTree.eml EMLTree.var (EMLTree.const c)) cs
    hwf (eml_A_crossing_var_const_unbounded_above_via_general A c hc) hT1eq

/-- **The bridge, generalized to any structurally-checkable crossing.** `eml_hasDerivAt_of_no_crossing`
(`EMLSmoothness.lean`) gives differentiability for ANY `EMLTree`, not just hand-verified shapes,
via the local, non-circular, checkable `EMLNoCrossingAt` condition. Feeding that into the crossing
bridge closes the residual for ANY `B` that genuinely crosses zero on some `[x0, x1]` and satisfies
`EMLNoCrossingAt` throughout — far broader than `var` and `eml var (const c)`, at the cost of
`EMLNoCrossingAt` becoming an explicit hypothesis for shapes where it isn't already known free. -/
theorem no_eml_A_B_eq_nested_target_of_crossing_and_no_crossing
    (A B : EMLTree) (x0 x1 : Real) (hx0x1 : x0 < x1)
    (hBx0 : B.eval x0 = 0) (hBx1pos : 0 < B.eval x1)
    (hnc : ∀ z : Real, x0 ≤ z → z ≤ x1 → MachLib.EMLNoCrossingAt B z)
    (cs : List Real) (hwf : nestedWF cs)
    (hT1eq : ∀ x : Real, (EMLTree.eml A B).eval x = nestedTarget cs x) : False :=
  no_eml_A_B_eq_nested_target_of_unbounded_above A B cs hwf
    (eml_A_crossing_B_unbounded_above A B x0 x1 hx0x1 hBx0 hBx1pos
      (fun z hz1 hz2 => MachLib.eml_hasDerivAt_of_no_crossing B z (hnc z hz1 hz2)))
    hT1eq

end Real
end MachLib
