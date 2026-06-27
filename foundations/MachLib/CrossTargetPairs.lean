import MachLib.Basic
import MachLib.Lemmas
import MachLib.Forge
import MachLib.FPModel
import MachLib.ErrorAlgebra
import MachLib.ErrorAlgebraTrans
import MachLib.ForwardError
import MachLib.HybridError

/-!
# More cross-target pairs — the framework spans the whole algebra

`FPModel.cross_target` says: if two computations are each within `B` of the same
exact value, they agree within `B1 + B2`. It is generic in the bounds, so it
composes with *any* forward-error bound — including the ones built this session.
This file instantiates it on the new algebra, showing cross-target equivalence is
no longer tied to FPModel's hand-proved kernels:

* `length_sq2_cross` — the same `length_sq2` at two precisions `w1, w2` agree
  within the sum of their two-sided (`ForwardError`) bounds;
* `gaussian2_cross` — the Gaussian `exp(−(x²+y²))` (a transcendental-∘-arithmetic
  kernel) at two precisions agrees, via the `HybridError` bound.

So "any two targets compute the same function (within summed error)" now holds
across the *whole* forward-error algebra — arithmetic, transcendental, hybrid —
not just the originally hand-proved cases. `sorryAx`-free.
-/

namespace MachLib.Real

/-- `length_sq2` at two precisions agrees within the sum of the two-sided bounds. -/
theorem length_sq2_cross
    {w1 w2 x y px1 py1 s1 px2 py2 s2 : Real}
    (hw1 : 0 ≤ w1) (hw1' : w1 ≤ 1) (hw2 : 0 ≤ w2) (hw2' : w2 ≤ 1)
    (hpx1 : RoundsW w1 px1 (x * x)) (hpy1 : RoundsW w1 py1 (y * y))
    (hs1 : RoundsW w1 s1 (px1 + py1))
    (hpx2 : RoundsW w2 px2 (x * x)) (hpy2 : RoundsW w2 py2 (y * y))
    (hs2 : RoundsW w2 s2 (px2 + py2)) :
    abs (s1 - s2)
      ≤ (npow 2 (1 + w1) - 1) * (x * x + y * y)
        + (npow 2 (1 + w2) - 1) * (x * x + y * y) :=
  cross_target (length_sq2_fwd_compose hw1 hw1' hpx1 hpy1 hs1)
               (length_sq2_fwd_compose hw2 hw2' hpx2 hpy2 hs2)

/-- The Gaussian `exp(−(x²+y²))` at two precisions agrees — cross-target across
the transcendental-∘-arithmetic boundary. -/
theorem gaussian2_cross
    {w1 w2 x y px1 py1 s1 p1 px2 py2 s2 p2 : Real}
    (hw1 : 0 ≤ w1) (hw1' : w1 ≤ 1) (hw2 : 0 ≤ w2) (hw2' : w2 ≤ 1)
    (hpx1 : RoundsW w1 px1 (x * x)) (hpy1 : RoundsW w1 py1 (y * y))
    (hs1 : RoundsW w1 s1 (px1 + py1)) (hp1 : RoundsW w1 p1 (exp (-s1)))
    (hpx2 : RoundsW w2 px2 (x * x)) (hpy2 : RoundsW w2 py2 (y * y))
    (hs2 : RoundsW w2 s2 (px2 + py2)) (hp2 : RoundsW w2 p2 (exp (-s2))) :
    abs (p1 - p2)
      ≤ exp (-(x * x + y * y)) * (exp ((npow 2 (1 + w1) - 1) * (x * x + y * y)) * (1 + w1) - 1)
        + exp (-(x * x + y * y)) * (exp ((npow 2 (1 + w2) - 1) * (x * x + y * y)) * (1 + w2) - 1) :=
  cross_target (gaussian2_fwd hw1 hw1' hpx1 hpy1 hs1 hp1)
               (gaussian2_fwd hw2 hw2' hpx2 hpy2 hs2 hp2)

end MachLib.Real
