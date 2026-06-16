import MachLib.MultiPoly
import MachLib.PolynomialEvidence
import MachLib.PolynomialRootCount
import MachLib.Exp

/-!
# MachLib.ExpPolyBridge — Poly → MultiPoly 1 embedding

The bridge for option B of the Khovanskii sprint: translate the
single-variable `Poly` AST (in `PolynomialEvidence`) into the
two-variable `MultiPoly 1` AST (in `MultiPoly`). This is the
foundational step toward bridging the constructive `ExpPoly` track in
`SingleExpKhovanskii.lean` to the abstract `PfaffianFn` framework.

## What ships in this commit

- `Poly.toMultiPoly1 : Poly → MultiPoly 1`: the structural embedding
  (Poly.var → MultiPoly.varX, all other constructors mirrored).
- `Poly.eval_toMultiPoly1`: eval correctness — Poly.eval p x equals
  MultiPoly.eval (toMultiPoly1 p) x env for any env.
- `Poly.PolynomialRootCount.degreeUpper_toMultiPoly1`: degreeX correspondence.

The Poly variable maps to x (varX), not to y_0. The y_0 variable
slot in MultiPoly 1 is reserved for the chain variable
(exp(x) in SingleExpChain).
-/

namespace MachLib
namespace ExpPolyBridge

open MachLib.MultiPolyMod
open MachLib.PolynomialEvidence
open MachLib.PolynomialRootCount

/-- **Structural embedding** `Poly → MultiPoly 1`. The Poly's `var`
(univariate variable, treated as x) maps to MultiPoly's `varX`. The
y_0 slot in MultiPoly 1 is unused (no `varY` in the image). -/
noncomputable def Poly.toMultiPoly1 : Poly → MultiPoly 1
  | Poly.const c => MultiPoly.const c
  | Poly.var     => MultiPoly.varX
  | Poly.add p q => MultiPoly.add (Poly.toMultiPoly1 p) (Poly.toMultiPoly1 q)
  | Poly.sub p q => MultiPoly.sub (Poly.toMultiPoly1 p) (Poly.toMultiPoly1 q)
  | Poly.mul p q => MultiPoly.mul (Poly.toMultiPoly1 p) (Poly.toMultiPoly1 q)

/-- **Eval correctness**: `Poly.eval p x` equals
`MultiPoly.eval (toMultiPoly1 p) x env` for any environment `env`.
The y_0 slot doesn't appear in the image, so the eval is
env-independent. -/
theorem Poly.eval_toMultiPoly1 (p : Poly) (x : Real) (env : Fin 1 → Real) :
    MultiPoly.eval (Poly.toMultiPoly1 p) x env = Poly.eval p x := by
  induction p with
  | const c => rfl
  | var => rfl
  | add p q ihp ihq =>
    show MultiPoly.eval (Poly.toMultiPoly1 p) x env +
         MultiPoly.eval (Poly.toMultiPoly1 q) x env =
         Poly.eval p x + Poly.eval q x
    rw [ihp, ihq]
  | sub p q ihp ihq =>
    show MultiPoly.eval (Poly.toMultiPoly1 p) x env -
         MultiPoly.eval (Poly.toMultiPoly1 q) x env =
         Poly.eval p x - Poly.eval q x
    rw [ihp, ihq]
  | mul p q ihp ihq =>
    show MultiPoly.eval (Poly.toMultiPoly1 p) x env *
         MultiPoly.eval (Poly.toMultiPoly1 q) x env =
         Poly.eval p x * Poly.eval q x
    rw [ihp, ihq]

/-- **degreeY 0 is always 0** for the image: `toMultiPoly1` never
introduces `varY 0`. -/
theorem Poly.degreeY_toMultiPoly1 (p : Poly) :
    MultiPoly.degreeY 0 (Poly.toMultiPoly1 p) = 0 := by
  induction p with
  | const c => rfl
  | var => rfl
  | add p q ihp ihq =>
    show Nat.max (MultiPoly.degreeY 0 (Poly.toMultiPoly1 p))
                  (MultiPoly.degreeY 0 (Poly.toMultiPoly1 q)) = 0
    rw [ihp, ihq]; rfl
  | sub p q ihp ihq =>
    show Nat.max (MultiPoly.degreeY 0 (Poly.toMultiPoly1 p))
                  (MultiPoly.degreeY 0 (Poly.toMultiPoly1 q)) = 0
    rw [ihp, ihq]; rfl
  | mul p q ihp ihq =>
    show MultiPoly.degreeY 0 (Poly.toMultiPoly1 p) +
         MultiPoly.degreeY 0 (Poly.toMultiPoly1 q) = 0
    rw [ihp, ihq]

/-- **degreeX correspondence**: the MultiPoly 1 image has the same
formal x-degree (degreeX) as the original Poly's PolynomialRootCount.degreeUpper. -/
theorem Poly.PolynomialRootCount.degreeUpper_toMultiPoly1 (p : Poly) :
    MultiPoly.degreeX (Poly.toMultiPoly1 p) = PolynomialRootCount.degreeUpper p := by
  induction p with
  | const c => rfl
  | var => rfl
  | add p q ihp ihq =>
    show Nat.max (MultiPoly.degreeX (Poly.toMultiPoly1 p))
                  (MultiPoly.degreeX (Poly.toMultiPoly1 q))
         = Nat.max (PolynomialRootCount.degreeUpper p) (PolynomialRootCount.degreeUpper q)
    rw [ihp, ihq]
  | sub p q ihp ihq =>
    show Nat.max (MultiPoly.degreeX (Poly.toMultiPoly1 p))
                  (MultiPoly.degreeX (Poly.toMultiPoly1 q))
         = Nat.max (PolynomialRootCount.degreeUpper p) (PolynomialRootCount.degreeUpper q)
    rw [ihp, ihq]
  | mul p q ihp ihq =>
    show MultiPoly.degreeX (Poly.toMultiPoly1 p) +
         MultiPoly.degreeX (Poly.toMultiPoly1 q)
         = PolynomialRootCount.degreeUpper p + PolynomialRootCount.degreeUpper q
    rw [ihp, ihq]

end ExpPolyBridge
end MachLib
