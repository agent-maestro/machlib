import MachLib.PolyRing
import Lean

/-
MachLib.PolyRingTactic — the `mach_poly` reification tactic (ring-v2, slice 2).

Makes the PolyRing reflective engine push-button. `mach_poly x` proves a
univariate polynomial identity `lhs = rhs` over the atom `x` by:
  1. reifying both sides into `PExpr` (the metaprogram `reifyPExpr`),
  2. rewriting along `PExpr.denote_eq_eval` to `eval (toPoly ea) x = eval (toPoly eb) x`,
  3. reducing to `PEq (toPoly ea) (toPoly eb)` (equality up to trailing zeros), and
  4. discharging each per-coefficient CONSTANT equality with `mach_ring`.

This is the collection `mach_ring` alone cannot do (it can't combine like
monomials after distribution) — the reflection does the collection structurally
and leaves only degree-0 arithmetic. `import Lean` is Lean CORE (no Mathlib /
external dependency), so the zero-dependency property of MachLib is preserved.

SCOPE: closes ANY univariate polynomial identity over a single atom, including
ones that CANCEL to a lower degree (`(s+1) − s = 1`, `s − s = 0`). The key is
`UPoly.PEq`: it compares the two coefficient lists DIRECTLY (`a = b`, tolerating
trailing zeros) rather than via a difference `a + (-b) = 0` — the latter would
hand `mach_ring` constant-collection goals like `1 + 1 + (-1 + -1) = 0` that it
cannot sort-and-cancel. Multivariate identities (quat four-square, Vec3 Lagrange)
are slice 3.
-/

open Lean Elab Tactic Meta
open MachLib MachLib.Real

/-- Reify a `Real` expression (univariate in atom `x`) into a `PExpr`. Anything
that isn't `+`, `*`, `-`, unary `-`, or the atom itself becomes a `lit`
(constant). -/
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

/-- `mach_poly x` — close a univariate polynomial identity over `x` through the
PolyRing reflective normaliser. Handles leading-term cancellation. See the file
header for scope. -/
elab "mach_poly" xt:term : tactic => do
  let xE ← elabTerm xt none
  let goal ← getMainGoal
  let some (_, lhs, rhs) := (← goal.getType).eq?
    | throwError "mach_poly: goal is not an equality"
  let ea ← reifyPExpr xE lhs
  let eb ← reifyPExpr xE rhs
  let dC := mkConst ``PExpr.denote
  let goal2 ← goal.change (← mkEq (mkApp2 dC xE ea) (mkApp2 dC xE eb))
  replaceMainGoal [goal2]
  evalTactic (← `(tactic| simp only [MachLib.Real.PExpr.denote_eq_eval]))
  evalTactic (← `(tactic| apply MachLib.Real.UPoly.eval_eq_of_PEq))
  evalTactic (← `(tactic| simp only [MachLib.Real.PExpr.toPoly, MachLib.Real.UPoly.add,
      MachLib.Real.UPoly.mul, MachLib.Real.UPoly.scale, MachLib.Real.UPoly.shiftX,
      MachLib.Real.UPoly.neg, MachLib.Real.UPoly.C, MachLib.Real.UPoly.X,
      MachLib.Real.UPoly.PEq]))
  evalTactic (← `(tactic| (repeat' apply And.intro) <;> (try trivial) <;> mach_ring))

/-! ### Regression demonstrations (these double as the tactic's test suite). -/

namespace MachLib.Real.PolyRingTactic.Tests

-- the smoothstep certificate, push-button (cf. the hand proof in PolyRing)
example (s : Real) :
    (1 : Real) - s * s * ((1 + 1 + 1) - (1 + 1) * s)
      = (1 - s) * (1 - s) * (1 + (1 + 1) * s) := by mach_poly s
example (s : Real) : (s + 1) * (s + 1) = s * s + (1 + 1) * s + 1 := by mach_poly s
example (s : Real) : (s + 1) * (s - 1) = s * s - 1 := by mach_poly s
example (s : Real) : (s * s) * (s * s) = s * s * s * s := by mach_poly s
example (s : Real) : -(s - 1) = 1 - s := by mach_poly s

-- cancellation to a LOWER degree (different-length coefficient lists): the PEq
-- equality-up-to-trailing-zeros path. These were out of scope for the v1 tactic.
example (s : Real) : (s + 1) - s = 1 := by mach_poly s
example (s : Real) : s - s = 0 := by mach_poly s
example (s : Real) : (s + 1) * (s - 1) + 1 = s * s := by mach_poly s

end MachLib.Real.PolyRingTactic.Tests
