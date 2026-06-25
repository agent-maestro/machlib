import MachLib.PolyRing
import Lean

/-
MachLib.PolyRingTactic — the `mach_poly` reification tactic (ring-v2, slices 2-3).

Makes the PolyRing reflective engine push-button. `mach_poly x` proves a
UNIVARIATE polynomial identity `lhs = rhs` over the atom `x`; `mach_poly x, y, …`
proves a MULTIVARIATE identity over the listed atoms.

Univariate mechanics:
  1. reify both sides into `PExpr` (the metaprogram `reifyPExpr`),
  2. rewrite along `PExpr.denote_eq_eval` to `eval (toPoly ea) x = eval (toPoly eb) x`,
  3. reduce to `PEq (toPoly ea) (toPoly eb)` (equality up to trailing zeros), and
  4. discharge each per-coefficient CONSTANT equality with `mach_ring`.

This is the collection `mach_ring` alone cannot do (it can't combine like
monomials after distribution) — the reflection does the collection structurally
and leaves only degree-0 arithmetic. `import Lean` is Lean CORE (no Mathlib /
external dependency), so the zero-dependency property of MachLib is preserved.

Multivariate mechanics (slice 3): treat all atoms but the FIRST as opaque
constants, run the univariate machinery w.r.t. the first atom, and RECURSE the
whole procedure on each resulting per-coefficient equality (which is a polynomial
in the remaining atoms). The base case — no atoms left — is `mach_ring` on the
purely-constant leaf equalities. Because every comparison is a `PEq` DIRECT
coefficient match (`a = b`, never a difference `a + (-b) = 0`), no level ever
hands `mach_ring` a constant-collection goal it cannot sort-and-cancel.

SCOPE: closes ANY polynomial identity (including leading-term cancellation, via
`UPoly.PEq`) over the atoms listed. Validated sorryAx-clean on, among others, the
smoothstep certificate `1 − s²(3−2s) = (1−s)²(1+2s)`, the Brahmagupta two-square
identity, and the Vec3 cross-product Lagrange identity. COST scales with the
number of atoms and the degree: the per-level re-normalisation makes the
6-variable Lagrange identity need `set_option maxHeartbeats 0` (~70 s); the
in-build regression tests below are kept small so `lake build` stays fast. A
single nested-`MPoly` normal form (one reification, one normalisation) would be
the way to push 8-variable degree-4 identities (e.g. the four-square identity)
into routine-build territory.
-/

open Lean Elab Tactic Meta
open MachLib MachLib.Real

/-- Reify a `Real` expression into a `PExpr` over the single atom `x`. Anything
that isn't `+`, `*`, `-`, unary `-`, or the atom itself becomes a `lit`
(constant) — including, in the multivariate setting, the OTHER atoms. -/
partial def MachLib.Real.reifyPExpr (x : Expr) (e : Expr) : MetaM Expr := do
  if ← isDefEq e x then return mkConst ``PExpr.atom
  match e.getAppFnArgs with
  | (``HAdd.hAdd, a) =>
    return mkApp2 (mkConst ``PExpr.add) (← reifyPExpr x a[4]!) (← reifyPExpr x a[5]!)
  | (``HMul.hMul, a) =>
    return mkApp2 (mkConst ``PExpr.mul) (← reifyPExpr x a[4]!) (← reifyPExpr x a[5]!)
  | (``HSub.hSub, a) =>
    return mkApp2 (mkConst ``PExpr.sub) (← reifyPExpr x a[4]!) (← reifyPExpr x a[5]!)
  | (``Neg.neg, a) =>
    return mkApp (mkConst ``PExpr.neg) (← reifyPExpr x a[2]!)
  | _ => return mkApp (mkConst ``PExpr.lit) e

/-- One level of the reduction: reify the current equality goal w.r.t. atom `x`,
push it through `denote_eq_eval` + `eval_eq_of_PEq`, unfold `PEq`, and split the
coefficient conjunction. The remaining open goals are the per-coefficient
equalities (polynomials in any other atoms), with the trivially-true ones already
closed. -/
def MachLib.Real.machPolyStep (x : Expr) : TacticM Unit := do
  let goal ← getMainGoal
  let goalType ← instantiateMVars (← goal.getType)
  let some (_, lhs, rhs) := goalType.eq?
    | throwError "mach_poly: goal is not an equality:\n{goalType}"
  let ea ← reifyPExpr x lhs
  let eb ← reifyPExpr x rhs
  let dC := mkConst ``PExpr.denote
  let goal2 ← goal.change (← mkEq (mkApp2 dC x ea) (mkApp2 dC x eb))
  replaceMainGoal [goal2]
  evalTactic (← `(tactic| simp only [MachLib.Real.PExpr.denote_eq_eval]))
  evalTactic (← `(tactic| apply MachLib.Real.UPoly.eval_eq_of_PEq))
  evalTactic (← `(tactic| simp only [MachLib.Real.PExpr.toPoly, MachLib.Real.UPoly.add,
      MachLib.Real.UPoly.mul, MachLib.Real.UPoly.scale, MachLib.Real.UPoly.shiftX,
      MachLib.Real.UPoly.neg, MachLib.Real.UPoly.C, MachLib.Real.UPoly.X,
      MachLib.Real.UPoly.PEq]))
  evalTactic (← `(tactic| (repeat' apply And.intro) <;> (try trivial)))

/-- Recurse atom-by-atom. With atoms remaining, peel the first off with
`machPolyStep` and run the rest on every surviving coefficient goal; with none
left, the leaves are constant equalities for `mach_ring`. -/
partial def MachLib.Real.machPolyRec : List Expr → TacticM Unit
  | []        => do evalTactic (← `(tactic| all_goals mach_ring))
  | x :: rest => do
    machPolyStep x
    let goals ← getGoals
    let mut acc : List MVarId := []
    for g in goals do
      setGoals [g]
      machPolyRec rest
      acc := acc ++ (← getGoals)
    setGoals acc

/-- `mach_poly x` (univariate) / `mach_poly x, y, …` (multivariate) — close a
polynomial identity over the listed atoms through the PolyRing reflective
normaliser. Handles leading-term cancellation. See the file header for scope and
cost. -/
elab "mach_poly" xs:term,+ : tactic => do
  let atoms ← xs.getElems.toList.mapM (fun t => elabTerm t.raw none)
  machPolyRec atoms

/-! ### Regression demonstrations (these double as the tactic's test suite).
Kept small/fast on purpose — the heavy multivariate identities (Lagrange,
four-square) are validated out-of-build because they need raised heartbeats. -/

namespace MachLib.Real.PolyRingTactic.Tests

-- univariate, same degree: the smoothstep certificate, push-button
example (s : Real) :
    (1 : Real) - s * s * ((1 + 1 + 1) - (1 + 1) * s)
      = (1 - s) * (1 - s) * (1 + (1 + 1) * s) := by mach_poly s
example (s : Real) : (s + 1) * (s + 1) = s * s + (1 + 1) * s + 1 := by mach_poly s
example (s : Real) : (s + 1) * (s - 1) = s * s - 1 := by mach_poly s
example (s : Real) : (s * s) * (s * s) = s * s * s * s := by mach_poly s
example (s : Real) : -(s - 1) = 1 - s := by mach_poly s

-- univariate, cancellation to a LOWER degree (the PEq trailing-zeros path)
example (s : Real) : (s + 1) - s = 1 := by mach_poly s
example (s : Real) : s - s = 0 := by mach_poly s
example (s : Real) : (s + 1) * (s - 1) + 1 = s * s := by mach_poly s

-- multivariate (slice 3)
example (x y : Real) : (x + y) * (x + y) = x*x + (1+1)*x*y + y*y := by mach_poly x, y
example (x y : Real) : (x + y) * (x - y) = x*x - y*y := by mach_poly x, y
example (x y : Real) : (x - y) * (x - y) = x*x - (1+1)*x*y + y*y := by mach_poly x, y
example (x y z : Real) : (x + y + z) * (x + y + z)
    = x*x + y*y + z*z + (1+1)*(x*y + y*z + x*z) := by mach_poly x, y, z

end MachLib.Real.PolyRingTactic.Tests
