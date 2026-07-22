import MachLib.LogDivergenceWall

/-!
# Implicit representability: where the explicit route fails, the relational one succeeds

Track C, item C3. The muses' proposal: turn C1's wall into a SEPARATION theorem by contrasting
two notions of "EML represents `f`" — EXPLICIT (`∃ t, t.eval = f`, what every non-representability
result in this whole arc has been about) versus IMPLICIT/relational (`∃ t` whose GRAPH, inverted,
recovers `f` — i.e. `t.eval y = x ↔ y = f x`). `exp` has no domain restriction (unlike `log`, which
MachLib clamps to `0` off the positive axis), so its EML representation is unconditionally valid
everywhere — and inverting it recovers `log` exactly, for every `x > 0`, with no validity hypothesis
at all. `log` fails the explicit route near `0` (C1) but trivially succeeds the implicit one
everywhere `log` is actually meaningful.

**C2, checked and NOT pursued — reported here rather than forced.** The muses' companion proposal
(regularized `log√(x²+ε²)`, converging to `log|x|` as a boundary-point characterization) needs
building `x² + ε²` inside an EML tree first. Checked directly against `EMLTree`'s actual grammar
(`SinNotInEML.lean`): exactly three constructors — `const`, `var`, `eml t1 t2 := exp(t1.eval) -
log(t2.eval)`. No addition, no multiplication, no squaring. Every compound node's value is
irreducibly `(a positive exp term) - (a log term)`; nothing in the grammar can isolate a bare
polynomial like `x²` or cancel an unwanted `exp`/`log` term exactly (only approximately, which
doesn't give an EXACT tree). This isn't a proof of impossibility (not attempted — would need its
own argument, likely an induction on tree structure showing every reachable closed form has a
specific exp/log-tower shape incompatible with polynomial growth), but hand-construction attempts
for even `x²` alone did not succeed, and nothing in this codebase's Pfaffian-chain machinery
(`MultiPoly`, used for `t.eval`'s DIFFERENTIAL relations, not its closed form) bridges the gap —
chain polynomial degree describes derivative relations, not `t.eval` itself. C2 as literally stated
needs either (a) a genuine impossibility proof that `EMLTree` can't build quadratics (a real,
self-contained result, NOT attempted this round), or (b) reformulating within the much richer
Pfaffian-chain VALUE class from the older `log_hard`/`exp_hard` arc (`project_log_hard_fixedD_pivot`,
predates Option D, `exp_hard` there is flagged multi-week/high-risk on a DIFFERENT question) — a
bigger scope decision, not a bounded afternoon item. Flagging honestly rather than forcing a
construction against a grammar that likely can't support it.

**C4 (cell stratification), not pursued** — both reviews already flagged it lowest priority, "only
needed if a future consumer needs exactness on the negative axis rather than ε-closeness." No such
consumer identified; skipped rather than built speculatively.
-/

namespace MachLib

open MachLib.Real

/-- **`exp` is explicitly EML-representable, exactly, with no domain restriction.** `eml var
(const 0)` evaluates to `Real.exp y - Real.log 0 = Real.exp y - 0 = Real.exp y` for every `y` — no
hypothesis, no clamp ever triggers (unlike any tree attempting to represent `log` itself). -/
theorem eml_exp_representation : (EMLTree.eml EMLTree.var (EMLTree.const 0)).eval = Real.exp := by
  funext y
  show Real.exp y - Real.log 0 = Real.exp y
  rw [log_zero, sub_zero]

/-- **The relational fact: inverting `exp`'s EML representative recovers `log` exactly, for every
`x > 0`, with no hypothesis at all** — not `EMLPfaffianValidOn`, not a neighborhood restriction,
nothing C1's wall needed. This is the sense in which `log` is IMPLICITLY representable despite
failing every EXPLICIT route near `0`. -/
theorem eml_exp_inverse_is_log (x : Real) (hx : 0 < x) (y : Real) :
    (EMLTree.eml EMLTree.var (EMLTree.const 0)).eval y = x ↔ y = Real.log x := by
  rw [eml_exp_representation]
  constructor
  · intro h; rw [← h, log_exp]
  · intro h; rw [h, exp_log hx]

/-- **The separation, stated together.** `log` is implicitly representable (via `exp`'s inverse,
unconditionally, for every `x > 0`) — restated from `eml_exp_inverse_is_log` — while no EML tree
valid across an interval containing `0` can represent it EXPLICITLY on the positive side of that
interval (`no_tree_eq_log_positive_side_given_validon`, `LogDivergenceWall.lean`). Two different
notions of "representable," and `log` sits on opposite sides of both, for the exact same
underlying reason: `log`'s singularity at `0` is invisible to the RELATION `exp` defines (which
never needs to evaluate anything AT the singularity) but fatal to any direct FUNCTIONAL match
(which does). -/
theorem log_implicit_not_explicit (t : EMLTree) (a b : Real) (ha : a < 0) (hb : 0 < b)
    (hvalidon : EMLPfaffianValidOn t a b) :
    (∀ x : Real, 0 < x → ∀ y : Real,
      (EMLTree.eml EMLTree.var (EMLTree.const 0)).eval y = x ↔ y = Real.log x) ∧
    ¬ (∀ x : Real, 0 < x → x < b → t.eval x = Real.log x) :=
  ⟨fun x hx y => eml_exp_inverse_is_log x hx y,
   fun heq => no_tree_eq_log_positive_side_given_validon t a b ha hb hvalidon heq⟩

end MachLib
