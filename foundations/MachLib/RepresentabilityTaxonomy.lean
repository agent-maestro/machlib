import MachLib.LogImplicitRepresentability

/-!
# Compression: a formal explicit/implicit representability taxonomy behind C3

Per external review: name the two notions C3 (`LogImplicitRepresentability.lean`) already
distinguishes informally, so future results can be stated AGAINST the taxonomy rather than as
one-off theorems each re-explaining the distinction.

**Scoped honestly, not idealized.** `ImplicitlyRepresentable` is the natural, UNCONDITIONAL
notion — matches what `eml_exp_inverse_is_log` already proves, no hypothesis. The explicit side is
NOT a bare "some tree matches `f` everywhere" (that stronger, unconditional statement was never
proven — proving it would need deriving `EMLPfaffianValidOn` from a bare match, the exact
generalization `eml_eventually_valid_repr` supplies for OTHER results in this arc but which was
not invoked for `log`, and doing so now would be new strengthening work, not compression). Instead
`ExplicitlyRepresentableValidlyNear` matches EXACTLY the hypothesis shape C1 actually rules out —
validity spanning the point in question. Naming a weaker predicate honestly is better than naming
a strong one dishonestly.

**Open question, checked and recorded rather than left for a future round to "discover" (per
external review) — the UNCONDITIONAL separation is a genuinely distinct, unresolved gap, not
something C1's argument already delivers.** Worked through directly: could `t.eval x = Real.log x`
on `(0, b)`, with NO validity hypothesis at all, be ruled out the same way? No — the current proof
of `no_tree_eq_log_positive_side_given_validon` structurally NEEDS validity to get `ContinuousAt
t.eval 0` (via `eml_validon_continuousAt`); that continuity is the entire leverage the argument has
against `log`'s divergence. Without it, a bare match `heq` gives no contradiction on its own — `log`
diverging on `(0,b)` just means `t.eval` ALSO diverges there (trivially, since they're equal), and
nothing forces `t.eval 0` itself (a well-defined, finite value — `EMLTree.eval` is total) to relate
to that divergence in any particular way without an independent reason `t.eval` must stay bounded
approaching `0`. `eml_eventually_valid_repr` (the unconditional-validity machinery this whole arc
uses elsewhere) does NOT close the gap either: it supplies validity on SOME tail from an unspecified
point `a`, with no guarantee `a < 0` — i.e. no guarantee the resulting validity interval actually
spans the point in question. Closing the unconditional version would need either a general
"`EMLTree.eval` is continuous everywhere except at classifiable clamp-boundary points" structural
lemma (doesn't exist yet) or an adapted construction forcing `eml_eventually_valid_repr`'s `a` below
`0` specifically (not attempted). Real, small, open — flagged here rather than assumed closed.
-/

namespace MachLib
namespace Real

open MachLib

/-- `f` is EXPLICITLY EML-representable, VALIDLY, on the positive side of `x0` up to `b` — some
tree matches `f` there AND is `EMLPfaffianValidOn` on an interval spanning `x0`. This is the exact
notion `no_tree_eq_log_positive_side_given_validon` (C1) rules out for `log`. -/
def ExplicitlyRepresentableValidlyNear (f : Real → Real) (x0 b : Real) : Prop :=
  ∃ (t : EMLTree) (a : Real), a < x0 ∧ EMLPfaffianValidOn t a b ∧
    ∀ x : Real, x0 < x → x < b → t.eval x = f x

/-- `f` is IMPLICITLY EML-representable on the positive reals if some tree's graph, inverted,
recovers `f` there — no validity hypothesis, matching `eml_exp_inverse_is_log`'s own unconditional
shape. -/
def ImplicitlyRepresentable (f : Real → Real) : Prop :=
  ∃ t : EMLTree, ∀ x : Real, 0 < x → ∀ y : Real, t.eval y = x ↔ y = f x

/-- `log` is implicitly representable — restated from `eml_exp_inverse_is_log` (C3) against the
named taxonomy. -/
theorem log_implicitlyRepresentable : ImplicitlyRepresentable Real.log :=
  ⟨EMLTree.eml EMLTree.var (EMLTree.const 0), eml_exp_inverse_is_log⟩

/-- `log` is NOT validly-explicitly-representable near `0` — restated from
`no_tree_eq_log_positive_side_given_validon` (C1) against the named taxonomy. -/
theorem log_not_explicitlyRepresentableValidlyNear (b : Real) (hb : 0 < b) :
    ¬ ExplicitlyRepresentableValidlyNear Real.log 0 b := by
  rintro ⟨t, a, ha, hvalidon, heq⟩
  exact no_tree_eq_log_positive_side_given_validon t a b ha hb hvalidon heq

/-- **The separation, stated together against the named taxonomy.** `log` sits on opposite sides
of the two notions, for every `b > 0`: implicitly representable (unconditionally, `x0 = 0`), yet
not validly-explicitly-representable near that same point. -/
theorem log_separation (b : Real) (hb : 0 < b) :
    ImplicitlyRepresentable Real.log ∧ ¬ ExplicitlyRepresentableValidlyNear Real.log 0 b :=
  ⟨log_implicitlyRepresentable, log_not_explicitlyRepresentableValidlyNear b hb⟩

end Real
end MachLib
