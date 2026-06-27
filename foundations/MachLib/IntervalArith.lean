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

end MachLib.Real
