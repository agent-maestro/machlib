import MachLib.PolynomialEvidence

/-!
MachLib.FiniteZeroPacket — sample finite-zero evidence over the tiny
polynomial AST.

These examples are finite algebraic root packets. They do not claim analytic
continuation, infinite zero sets, or an analytic identity theorem.
-/

namespace MachLib
namespace FiniteZeroPacket

open MachLib.Real
open MachLib.PolynomialEvidence

/-- Sample 1: the zero polynomial has every input as a root. -/
theorem sample_zero_poly_root (x : Real) :
    Poly.eval Poly.zero x = 0 :=
  Poly.eval_zero x

/-- Sample 2: `(x - r)` vanishes at `r`. -/
theorem sample_linear_factor_root (r : Real) :
    Poly.eval (Poly.linearFactor r) r = 0 :=
  Poly.eval_linearFactor_at_root r

/-- Sample 3: `(x - r) * q` vanishes at `r`. -/
theorem sample_factor_product_left_root (r : Real) (q : Poly) :
    Poly.eval (Poly.factorMul r q) r = 0 :=
  Poly.eval_factorMul_at_root r q

/-- Sample 4: `(x - r) * (x - r)` vanishes at `r`. -/
theorem sample_repeated_factor_root (r : Real) :
    Poly.eval (Poly.mul (Poly.linearFactor r) (Poly.linearFactor r)) r = 0 :=
  Poly.eval_repeatedFactor_at_root r

/-- Sample 5: `(x - r) * (x - s)` vanishes at the right-hand root `s`. -/
theorem sample_two_factor_right_root (r s : Real) :
    Poly.eval (Poly.mul (Poly.linearFactor r) (Poly.linearFactor s)) s = 0 := by
  unfold Poly.eval
  rw [Poly.eval_linearFactor_at_root, mul_zero]

end FiniteZeroPacket
end MachLib
