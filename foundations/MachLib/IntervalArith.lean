import MachLib.Basic
import MachLib.Lemmas
import MachLib.Forge
import MachLib.Ring
import MachLib.FPModel

/-!
# Verified interval arithmetic — rigorous enclosures

Forward/backward error bound *how wrong* a result is. Interval arithmetic instead
carries a rigorous *enclosure*: an `Interval ⟨lo, hi⟩` known to contain the true
value, with every operation producing an interval that provably contains the true
result. It's the constructive cousin of the error algebra — and the natural
output of a verified evaluator (run the kernel on intervals, get a certified box
around the answer).

This is the seed: `Interval`, membership, and the operations `add`/`neg`/`sub`
(+ a nonneg `mul`) each with a **membership-preservation theorem** — `x ∈ I`,
`y ∈ J` ⟹ `x ∘ y ∈ (I ∘ J)`. General signed `mul` (the 4-corner min/max) and
division are the continuation. `sorryAx`-free.
-/

namespace MachLib.Real

/-- A closed real interval. -/
structure Interval where
  lo : Real
  hi : Real

/-- `x` lies in the interval. -/
def Interval.mem (I : Interval) (x : Real) : Prop := I.lo ≤ x ∧ x ≤ I.hi

noncomputable def Interval.add (I J : Interval) : Interval := ⟨I.lo + J.lo, I.hi + J.hi⟩
noncomputable def Interval.neg (I : Interval) : Interval := ⟨-I.hi, -I.lo⟩
noncomputable def Interval.sub (I J : Interval) : Interval := I.add J.neg
noncomputable def Interval.mulNN (I J : Interval) : Interval := ⟨I.lo * J.lo, I.hi * J.hi⟩

/-- Addition encloses. -/
theorem Interval.add_mem {I J : Interval} {x y : Real}
    (hx : I.mem x) (hy : J.mem y) : (I.add J).mem (x + y) := by
  obtain ⟨hxl, hxu⟩ := hx; obtain ⟨hyl, hyu⟩ := hy
  exact ⟨add_le_add_both hxl hyl, add_le_add_both hxu hyu⟩

/-- Negation encloses (endpoints swap and flip). -/
theorem Interval.neg_mem {I : Interval} {x : Real}
    (hx : I.mem x) : I.neg.mem (-x) := by
  obtain ⟨hxl, hxu⟩ := hx
  exact ⟨neg_le_neg hxu, neg_le_neg hxl⟩

/-- Subtraction encloses (`I − J := I + (−J)`). -/
theorem Interval.sub_mem {I J : Interval} {x y : Real}
    (hx : I.mem x) (hy : J.mem y) : (I.sub J).mem (x - y) := by
  rw [show x - y = x + (-y) from by mach_ring]
  exact Interval.add_mem hx (Interval.neg_mem hy)

/-- Multiplication encloses when both intervals are nonnegative. -/
theorem Interval.mulNN_mem {I J : Interval} {x y : Real}
    (hI : 0 ≤ I.lo) (hJ : 0 ≤ J.lo) (hx : I.mem x) (hy : J.mem y) :
    (I.mulNN J).mem (x * y) := by
  obtain ⟨hxl, hxu⟩ := hx; obtain ⟨hyl, hyu⟩ := hy
  have hx0 : 0 ≤ x := le_trans hI hxl
  have hy0 : 0 ≤ y := le_trans hJ hyl
  have hhi0 : 0 ≤ I.hi := le_trans hx0 hxu
  refine ⟨?_, ?_⟩
  · -- I.lo * J.lo ≤ x * y
    exact le_trans (mul_le_mul_of_nonneg_right hxl hJ)
                   (mul_le_mul_of_nonneg_left hyl hx0)
  · -- x * y ≤ I.hi * J.hi
    exact le_trans (mul_le_mul_of_nonneg_right hxu hy0)
                   (mul_le_mul_of_nonneg_left hyu hhi0)

/-! ## signed multiplication (any sign) — symmetric enclosure -/

/-- The largest magnitude in an interval. -/
noncomputable def Interval.maxabs (I : Interval) : Real := max (abs I.lo) (abs I.hi)

/-- Signed product enclosure: `[−R, R]` with `R = maxabs I · maxabs J`. Valid for
*any* signs (looser than the tight 4-corner `min/max`, which is the continuation). -/
noncomputable def Interval.mulSym (I J : Interval) : Interval :=
  ⟨-(I.maxabs * J.maxabs), I.maxabs * J.maxabs⟩

/-- `x ∈ [lo,hi] ⟹ |x| ≤ max(|lo|,|hi|)` — magnitude bounded by the larger
endpoint, regardless of sign. -/
theorem abs_le_maxabs {lo hi x : Real} (hlo : lo ≤ x) (hhi : x ≤ hi) :
    abs x ≤ max (abs lo) (abs hi) :=
  abs_le_of (le_trans hhi (le_trans (le_abs_self hi) (le_max_right _ _)))
            (le_trans (neg_le_neg hlo) (le_trans (neg_le_abs lo) (le_max_left _ _)))

/-- Signed multiplication encloses (any sign). -/
theorem Interval.mulSym_mem {I J : Interval} {x y : Real}
    (hx : I.mem x) (hy : J.mem y) : (I.mulSym J).mem (x * y) := by
  obtain ⟨hxl, hxu⟩ := hx; obtain ⟨hyl, hyu⟩ := hy
  have hxa : abs x ≤ I.maxabs := abs_le_maxabs hxl hxu
  have hya : abs y ≤ J.maxabs := abs_le_maxabs hyl hyu
  have hR : abs (x * y) ≤ I.maxabs * J.maxabs := by
    rw [abs_mul]
    exact le_trans (mul_le_mul_of_nonneg_right hxa (abs_nonneg y))
                   (mul_le_mul_of_nonneg_left hya (le_trans (abs_nonneg x) hxa))
  refine ⟨?_, le_of_abs_le hR⟩
  have h := neg_le_neg (neg_le_of_abs_le hR)
  rwa [show -(-(x * y)) = x * y from by mach_ring] at h

end MachLib.Real
