import MachLib.PolyRing
import Lean

/-
MachLib.PolyRingTactic — the `mach_poly` reification tactic (ring-v2, slice 2).

Makes the PolyRing reflective engine push-button. `mach_poly x` proves a
univariate polynomial identity `lhs = rhs` over the atom `x` by:
  1. reifying both sides into `PExpr` (the metaprogram `reifyPExpr`),
  2. rewriting along `PExpr.denote_eq_eval` to `eval (toPoly ea) x = eval (toPoly eb) x`,
  3. reducing to the coefficient-list equality `toPoly ea = toPoly eb`, and
  4. discharging each per-coefficient CONSTANT equality with `mach_ring`.

This is the collection `mach_ring` alone cannot do (it can't combine like
monomials after distribution) — the reflection does the collection structurally
and leaves only degree-0 arithmetic. `import Lean` is Lean CORE (no Mathlib /
external dependency), so the zero-dependency property of MachLib is preserved.

SCOPE: closes univariate polynomial identities whose two sides have the SAME
effective degree (no leading-term cancellation) — which covers the smoothstep /
ease certificates (e.g. `1 − s²(3−2s) = (1−s)²(1+2s)`). Identities that cancel to
a lower degree (`(s+1) − s = 1`) currently leave a trailing-zero coefficient list
that the list-equality step can't match; the length-insensitive `IsZero`-difference
form is the next refinement. Multivariate identities are slice 3.
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

/-- `mach_poly x` — close a same-degree univariate polynomial identity over `x`
through the PolyRing reflective normaliser. See the file header for scope. -/
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
  evalTactic (← `(tactic| apply congrArg (fun p => MachLib.Real.UPoly.eval p $xt)))
  evalTactic (← `(tactic| simp only [MachLib.Real.PExpr.toPoly, MachLib.Real.UPoly.add,
      MachLib.Real.UPoly.mul, MachLib.Real.UPoly.scale, MachLib.Real.UPoly.shiftX,
      MachLib.Real.UPoly.neg, MachLib.Real.UPoly.C, MachLib.Real.UPoly.X,
      List.cons.injEq, and_true]))
  evalTactic (← `(tactic| (repeat' apply And.intro) <;> mach_ring))

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

end MachLib.Real.PolyRingTactic.Tests
