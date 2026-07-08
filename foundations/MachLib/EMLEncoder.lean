import MachLib.PfaffianChainExtend
import MachLib.SinNotInEML

/-!
# EMLTree → Pfaffian chain encoder — foundation

The recursive encoder turns an `EMLTree` (`const | var | eml t1 t2` with
`eml t1 t2 = exp(t1) − log(t2)`) into a Pfaffian chain + barrier polynomial
with eval-agreement, by *state-threading* a single growing chain via
`chainExtend` (no chain-merging).

This file builds the two index-bookkeeping primitives the recursion needs:

- `nVars t` — the number of chain variables `t` contributes: `0` for
  `const`/`var`, and `nVars t2 + nVars t1 + 3` for `eml t1 t2` (each `eml`
  node adds a reciprocal, a log, and an exp variable on top of its
  subtrees'). Ordered `t2` first so the recursion processes the log
  argument's reciprocal before the log itself.

- `liftLastYBy k` — `liftLastY` iterated `k` times, embedding `MultiPoly n`
  into `MultiPoly (n + k)` free of the top `k` variables. This is the ONE
  lift the encoder needs: after `t1` extends the chain above `t2`'s
  variables, `t2`'s barrier rises by `nVars t1` levels. `eval_liftLastYBy`
  says the added top variables are irrelevant to the lifted polynomial's
  value.

No new axioms.
-/

namespace MachLib

open MachLib.MultiPolyMod MachLib.MultiPolyMod.MultiPoly

/-- Number of chain variables an EML tree contributes. -/
def nVars : EMLTree → Nat
  | .const _  => 0
  | .var      => 0
  | .eml t1 t2 => nVars t2 + nVars t1 + 3

/-- `liftLastY` iterated `k` times: `MultiPoly n → MultiPoly (n + k)`,
free of the top `k` variables. -/
noncomputable def liftLastYBy {n : Nat} : (k : Nat) → MultiPoly n → MultiPoly (n + k)
  | 0,     p => p
  | k + 1, p => MultiPoly.liftLastY (liftLastYBy k p)

/-- The top `k` variables are irrelevant to a `k`-fold lift's value. -/
theorem eval_liftLastYBy {n : Nat} (k : Nat) (p : MultiPoly n) (x : Real)
    (env : Fin (n + k) → Real) :
    MultiPoly.eval (liftLastYBy k p) x env
      = MultiPoly.eval p x (fun i : Fin n => env ⟨i.val, by omega⟩) := by
  induction k with
  | zero =>
    show MultiPoly.eval p x env
       = MultiPoly.eval p x (fun i : Fin n => env ⟨i.val, by omega⟩)
    congr 1
  | succ k ih =>
    show MultiPoly.eval (MultiPoly.liftLastY (liftLastYBy k p)) x env
       = MultiPoly.eval p x (fun i : Fin n => env ⟨i.val, by omega⟩)
    rw [MultiPoly.eval_liftLastY (liftLastYBy k p) x env,
        ih (fun j : Fin (n + k) => env ⟨j.val, by omega⟩)]

end MachLib
