import MachLib.Ring

/-!
MachLib.PolynomialEvidence — tiny polynomial AST and checked root evidence.

This module is deliberately small. It gives MachLib a reusable finite
polynomial evidence substrate without claiming analytic continuation,
infinite zero-set behavior, or a full polynomial algebra library.
-/

namespace MachLib
namespace PolynomialEvidence

open MachLib.Real

inductive Poly where
  | const : Real → Poly
  | var : Poly
  | add : Poly → Poly → Poly
  | sub : Poly → Poly → Poly
  | mul : Poly → Poly → Poly

namespace Poly

noncomputable def eval : Poly → Real → Real
  | const c, _ => c
  | var, x => x
  | add p q, x => eval p x + eval q x
  | sub p q, x => eval p x - eval q x
  | mul p q, x => eval p x * eval q x

noncomputable def zero : Poly := const 0
noncomputable def one : Poly := const 1
noncomputable def linearFactor (r : Real) : Poly := sub var (const r)
noncomputable def factorMul (r : Real) (q : Poly) : Poly := mul (linearFactor r) q

/-- The zero polynomial evaluates to zero. -/
theorem eval_zero (x : Real) : eval zero x = 0 := rfl

/-- The variable polynomial evaluates to its input. -/
theorem eval_var (x : Real) : eval var x = x := rfl

/-- A named linear factor vanishes at its named root. -/
theorem eval_linearFactor_at_root (r : Real) :
    eval (linearFactor r) r = 0 := by
  unfold linearFactor eval
  exact sub_self r

/-- Multiplying by a vanishing linear factor vanishes at the same root. -/
theorem eval_factorMul_at_root (r : Real) (q : Poly) :
    eval (factorMul r q) r = 0 := by
  unfold factorMul eval
  rw [eval_linearFactor_at_root, zero_mul]

/-- A repeated linear factor vanishes at its named root. -/
theorem eval_repeatedFactor_at_root (r : Real) :
    eval (mul (linearFactor r) (linearFactor r)) r = 0 := by
  unfold eval
  rw [eval_linearFactor_at_root, zero_mul]

end Poly
end PolynomialEvidence
end MachLib
