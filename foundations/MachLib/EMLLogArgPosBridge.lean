import MachLib.EMLPfaffian
import MachLib.EMLEncoderAnalytic

/-!
# MachLib.EMLLogArgPosBridge — `EMLPfaffianValidOn` → `LogArgPosOn` (gap-piece ii)

The constructive mixed-EML finiteness bound `eml_eval_boundedZeros_unconditional`
takes its positivity side condition as `LogArgPosOn t (Icc a b)` (a RealSet /
CLOSED-interval predicate). The sin/cos-not-in-EML consumers instead carry
`EMLPfaffianValidOn t a b` — the same "every `eml` node's log-argument is
positive", but on the OPEN interval `(a, b)`.

This module bridges them. `logArgPosOn_of_validOn_subset` is the structural core:
on any RealSet `S ⊆ (a, b)`, open-interval validity gives `LogArgPosOn t S`. The
closed-subinterval corollary `logArgPosOn_Icc_of_validOn` then feeds the
constructive bound: pick `[a', b'] ⊂ (a, b)` (strictly interior — this is where the
endpoint mismatch is resolved, since e.g. `t2 = var` has `t2.eval 0 = 0`, so closed
positivity can fail exactly at the open interval's endpoints).

One of the three pieces (gap ii) needed to re-route `sin/cos_not_in_eml` off the
classical axiom — see AXIOM_AUDIT_V2.md §2c(2). Independent of the explicit-K
descent work (gap i).
-/

namespace MachLib
namespace EMLLogArgPosBridge

open MachLib.Real

/-- **Structural bridge.** On any `RealSet S` contained in the open interval
`(a, b)`, `EMLPfaffianValidOn t a b` (open-interval log-arg positivity) yields
`LogArgPosOn t S`. Induction on `t`; leaves are vacuous, and each `eml` node's
positivity conjunct restricts through `hsub`. -/
theorem logArgPosOn_of_validOn_subset (S : RealSet) (a b : Real)
    (hsub : ∀ x, S x → a < x ∧ x < b) :
    ∀ (t : EMLTree), EMLPfaffianValidOn t a b → LogArgPosOn t S := by
  intro t
  induction t with
  | const c => intro _; trivial
  | var => intro _; trivial
  | eml t1 t2 ih1 ih2 =>
    intro hvalid
    obtain ⟨hv1, hv2, hpos⟩ := hvalid
    refine ⟨ih1 hv1, ih2 hv2, ?_⟩
    intro x hSx
    obtain ⟨hxa, hxb⟩ := hsub x hSx
    exact hpos x hxa hxb

/-- **Closed-subinterval corollary.** For a strictly interior closed subinterval
`[a', b'] ⊂ (a, b)` (`a < a'`, `b' < b`), open-interval validity gives the
`LogArgPosOn t (Icc a' b')` that `eml_eval_boundedZeros_unconditional` requires.
The strict containment absorbs the endpoint mismatch. -/
theorem logArgPosOn_Icc_of_validOn (t : EMLTree) (a b a' b' : Real)
    (ha : a < a') (hb : b' < b) (hvalid : EMLPfaffianValidOn t a b) :
    LogArgPosOn t (Icc a' b') :=
  logArgPosOn_of_validOn_subset (Icc a' b') a b
    (fun x hx =>
      ⟨lt_of_lt_of_le ha hx.1, lt_of_le_of_lt hx.2 hb⟩)
    t hvalid

end EMLLogArgPosBridge
end MachLib
