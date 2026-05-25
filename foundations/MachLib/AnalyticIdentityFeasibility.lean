import MachLib.Ring

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

end AnalyticIdentityFeasibility
end MachLib
