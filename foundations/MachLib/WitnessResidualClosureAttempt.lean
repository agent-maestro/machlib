import MachLib.WitnessResidualRecursiveSignLift
import MachLib.WitnessResidualNestedTargetFamily

/-! # Attempting the full residual closure: two genuinely new techniques, honest account of the wall

Direct attempt to discharge `SupportsSignAnalysis` (or an equivalent) FROM the equation
`T1.eval = nestedTarget cs` itself, rather than assuming it — the piece needed to actually close
the witness-finding residual using everything built in this arc, not just characterize
boundedness in the abstract. This file records what that attempt turned up: two real, verified,
reusable techniques, and a precise account of where the attempt currently stops.

**Technique 1 — differentiability transports for free from the target's own closed form.**
The obvious first obstacle: my one-level sign-necessity machinery needs `T1`'s immediate right
child differentiable, but an ARBITRARY, UNKNOWN `T1` (the residual's own setup — we don't get to
pick its structure) has no free differentiability guarantee (log's clamp is a genuine
DISCONTINUITY at its boundary — checked directly against `Real.log`'s definition, not assumed —
so an arbitrary EMLTree is differentiable only where its own substructure avoids that boundary,
which is exactly the fact under investigation). The fix needs no structural argument on `T1` at
all: `nestedTarget cs` is a SPECIFIC, KNOWN function, differentiable everywhere given `nestedWF cs`
(proven directly, by induction on `cs`, via `HasDerivAt_sin`/`HasDerivAt_log_pos`/composition —
`nestedTarget_hasDerivAt`). Since `T1.eval` EQUALS `nestedTarget cs` GLOBALLY (the residual's own
hypothesis), `HasDerivAt_of_eq` transports that differentiability directly onto `T1`
(`T1_hasDerivAt_of_eq_nestedTarget`) — sidestepping the "does an arbitrary tree's structure
guarantee differentiability" question for `T1` ITSELF entirely.

**Technique 2 — pure algebra pins down `B` pointwise, no IVT or differentiability needed.**
For `T1 = eml A B` with `T1.eval x0 = target x0`: `log(B.eval x0) = exp(A.eval x0) - target x0`
follows directly. `Real.log`'s clamp returns EXACTLY `0` for non-positive arguments — so if this
computed quantity is NONZERO, `B.eval x0` is FORCED strictly positive, and in fact forced to
equal `exp(exp(A.eval x0) - target x0)` EXACTLY (`B_eval_forced_pos_of_ne`) — no IVT, no
continuity, no differentiability argument anywhere, purely algebraic (confirmed by the axiom
check: depends on nothing beyond basic ordered-field facts). Contrapositive
(`exp_A_eq_target_of_B_nonpos`): the ONLY way `B` can ever be non-positive at a point is if `A`'s
exp-image hits the target EXACTLY there.

**Where this leaves the residual, honestly.** These two facts together pin down `B` almost
everywhere — `B(x) > 0` unconditionally except possibly at points where `exp(A(x)) = target(x)`
exactly (call this the "ambiguous set"). If the ambiguous set were empty, `B` would be positive
everywhere with ZERO extra work, closing the case immediately via the existing
`RightChildrenEverywherePositive`-style machinery. But the ambiguous set's emptiness is NOT free:
it depends on `A`'s own behavior, which is exactly what the induction is trying to establish. If
the ambiguous set is nonempty, `B` may genuinely dip non-positive there — and determining whether
that constitutes a genuine crossing (triggering the unboundedness machinery) or something benign
again needs information about `A`'s behavior NEAR those points, which circles back to needing
`A`'s own differentiability/continuity — NOT transportable the same way, because (unlike `T1`) `A`
does not have a known closed form independent of the tree's own unknown structure. This is the
same underlying difficulty this whole arc identified from its earliest rounds ("grounded WHY path
1 is hard" — general compound trees mixing clamped and unclamped regions needs machinery not yet
built) — now sharpened and confirmed from a genuinely different angle (pointwise algebra and
differentiability-transport, not the Pfaffian-chain encoding this arc originally used to state
it), rather than resolved. Both new techniques remain independently reusable for whoever continues
this: transport works for ANY equation `T1.eval = (known closed-form target)`, and the pointwise
determination works for ANY compound tree, not just nested-target-family instances.

`sorryAx`-free, verified via a genuinely fresh rebuild — `B_eval_forced_pos_of_ne` in particular
depends on nothing beyond the most basic ordered-field axioms, no `exp_pos`, no `HasDerivAt`,
confirming it really is pure algebra. -/

namespace MachLib
namespace Real

/-- **The target family is differentiable everywhere, given well-formedness.** A self-contained
fact about `nestedTarget`, independent of any candidate tree `T1`. -/
theorem nestedTarget_hasDerivAt (cs : List Real) (hwf : nestedWF cs) (x : Real) :
    ∃ d : Real, HasDerivAt (nestedTarget cs) d x := by
  induction cs with
  | nil =>
    refine ⟨Real.cos x, ?_⟩
    have heq : ∀ y : Real, Real.sin y = nestedTarget [] y := fun y => (nestedTarget_nil y).symm
    exact HasDerivAt_of_eq Real.sin (nestedTarget []) (Real.cos x) x heq (HasDerivAt_sin x)
  | cons c cs' ih =>
    obtain ⟨hwf_c, hwf_cs'⟩ := hwf
    obtain ⟨d', hd'⟩ := ih hwf_cs'
    obtain ⟨hrange', _, _⟩ := nestedTarget_facts cs' hwf_cs'
    have hpos : 0 < c + nestedTarget cs' x := lt_of_lt_of_le hwf_c (add_le_add_left (hrange' x).1 c)
    have hsum := HasDerivAt_add (fun _ => c) (nestedTarget cs') 0 d' x (HasDerivAt_const c x) hd'
    have hcomp := HasDerivAt_comp Real.log (fun y => c + nestedTarget cs' y) (0 + d')
      (1 / (c + nestedTarget cs' x)) x hsum (HasDerivAt_log_pos _ hpos)
    refine ⟨(1 / (c + nestedTarget cs' x)) * (0 + d'), ?_⟩
    have heq : ∀ y : Real, Real.log (c + nestedTarget cs' y) = nestedTarget (c :: cs') y :=
      fun y => (nestedTarget_cons c cs' y).symm
    exact HasDerivAt_of_eq (fun y => Real.log (c + nestedTarget cs' y)) (nestedTarget (c :: cs'))
      ((1 / (c + nestedTarget cs' x)) * (0 + d')) x heq hcomp

/-- **Transport**: a candidate `T1` equal to a nested-target family member globally, given
well-formedness, is differentiable everywhere — for free, without needing anything about `T1`'s
OWN structure. This sidesteps the "does an arbitrary EMLTree's structure guarantee
differentiability" question entirely: we already know `T1.eval` equals a SPECIFIC, provably
differentiable function. -/
theorem T1_hasDerivAt_of_eq_nestedTarget (T1 : EMLTree) (cs : List Real) (hwf : nestedWF cs)
    (hT1eq : ∀ x : Real, T1.eval x = nestedTarget cs x) (x : Real) :
    ∃ d : Real, HasDerivAt T1.eval d x := by
  obtain ⟨d, hd⟩ := nestedTarget_hasDerivAt cs hwf x
  exact ⟨d, HasDerivAt_of_eq (nestedTarget cs) T1.eval d x (fun y => (hT1eq y).symm) hd⟩

theorem eq_sub_of_sub_eq_local {a b c : Real} (h : a - b = c) : b = a - c := by
  have e1 : a - c = a - (a - b) := by rw [h]
  have e2 : a - (a - b) = b := by mach_mpoly [a, b]
  rw [e2] at e1
  exact e1.symm

theorem eq_of_sub_eq_zero_local {a b : Real} (h : a - b = 0) : a = b := by
  have e1 : b + (a - b) = b + 0 := by rw [h]
  have e2 : b + (a - b) = a := by mach_ring
  have e3 : b + (0 : Real) = b := add_zero b
  rw [e2, e3] at e1
  exact e1

/-- **Pointwise, purely algebraic determination of `B`.** If `T1 = eml A B` satisfies the global
equation `T1.eval = target` (any target, not just nested ones), then at ANY point `x0` where
`exp(A.eval x0) ≠ target x0`, `B.eval x0` is FORCED to equal `exp(exp(A.eval x0) - target x0)`
EXACTLY — in particular, `B.eval x0 > 0` — with NO differentiability, NO IVT, NO continuity
argument needed at all. Pure algebra: `log`'s clamp returns EXACTLY `0` for non-positive
arguments, so a NONZERO computed log-value forces the argument positive. -/
theorem B_eval_forced_pos_of_ne (A B : EMLTree) (target : Real → Real)
    (hT1eq : ∀ x : Real, (EMLTree.eml A B).eval x = target x) (x0 : Real)
    (hne : Real.exp (A.eval x0) ≠ target x0) :
    B.eval x0 = Real.exp (Real.exp (A.eval x0) - target x0) ∧ 0 < B.eval x0 := by
  have heq : Real.exp (A.eval x0) - Real.log (B.eval x0) = target x0 := hT1eq x0
  have hK : Real.log (B.eval x0) = Real.exp (A.eval x0) - target x0 :=
    eq_sub_of_sub_eq_local heq
  have hBpos : 0 < B.eval x0 := by
    rcases lt_total (B.eval x0) 0 with h | h | h
    · rw [log_nonpos (le_of_lt h)] at hK
      exact absurd (eq_of_sub_eq_zero_local hK.symm) hne
    · rw [log_nonpos (le_of_eq h)] at hK
      exact absurd (eq_of_sub_eq_zero_local hK.symm) hne
    · exact h
  exact ⟨by rw [← hK, Real.exp_log hBpos], hBpos⟩

/-- Contrapositive form: if `B` is ever non-positive, the point is exactly one where `A`'s
exp-image hits the target exactly. Isolates the ONLY way `B` can fail to be forced positive. -/
theorem exp_A_eq_target_of_B_nonpos (A B : EMLTree) (target : Real → Real)
    (hT1eq : ∀ x : Real, (EMLTree.eml A B).eval x = target x) (x0 : Real)
    (hBnonpos : B.eval x0 ≤ 0) : Real.exp (A.eval x0) = target x0 := by
  refine Classical.byContradiction (fun hne => ?_)
  have hpos := (B_eval_forced_pos_of_ne A B target hT1eq x0 hne).2
  exact lt_irrefl_ax (0 : Real) (lt_of_lt_of_le hpos hBnonpos)

end Real
end MachLib
