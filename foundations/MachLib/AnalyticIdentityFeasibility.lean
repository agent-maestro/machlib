import MachLib.PolynomialEvidence

/-!
MachLib.AnalyticIdentityFeasibility — tiny checked footholds for a future
analytic identity theorem substrate.

This module does not formalize analytic functions, zero sets, accumulation
points, limits, topology, or the analytic identity theorem. It records only
the finite polynomial/root facts that the current MachLib algebra layer can
check today.
-/

namespace MachLib
namespace AnalyticIdentityFeasibility

open MachLib.Real

/-- The zero polynomial evaluates to zero in the current product/addition form. -/
theorem zero_polynomial_eval_checked (x : Real) :
    0 * x + 0 = 0 := by
  mach_ring

/-- A linear factor vanishes at its named root. -/
theorem linear_factor_known_root_checked (a r : Real) :
    a * (r - r) = 0 := by
  mach_ring

/-- A repeated linear factor also vanishes at its named root. -/
theorem repeated_factor_known_root_checked (a r : Real) :
    a * ((r - r) * (r - r)) = 0 := by
  mach_ring

/-- Polynomial AST zero evaluation, routed through `MachLib.PolynomialEvidence`. -/
theorem polynomial_ast_zero_eval_checked (x : Real) :
    PolynomialEvidence.Poly.eval PolynomialEvidence.Poly.zero x = 0 :=
  PolynomialEvidence.Poly.eval_zero x

/-- Polynomial AST factor/root evidence, routed through `MachLib.PolynomialEvidence`. -/
theorem polynomial_ast_factor_root_checked (r : Real) :
    PolynomialEvidence.Poly.eval (PolynomialEvidence.Poly.linearFactor r) r = 0 :=
  PolynomialEvidence.Poly.eval_linearFactor_at_root r

end AnalyticIdentityFeasibility
end MachLib
