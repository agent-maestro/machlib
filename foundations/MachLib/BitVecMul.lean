import MachLib.RippleCarry

/-!
# Leg B — bit-vector multiplication, proved correct

After the ripple-carry adder (`RippleCarry`), the next gate the Q-format datapath
needs is **multiply**. This builds it shift-and-add on the same Lean-core
`List Bool` bit-vectors and proves it computes `Nat` multiplication exactly:

    toNat (mul a b) = toNat a * toNat b

Ingredients (each Mathlib-free, sorryAx-free):
* `addCarry` — add a single carry bit (half-adder chain); `addCarry_correct`.
* `addc` — an arbitrary-length adder (the equal-length `rca` doesn't suffice once
  partial products are shifted); `addc_correct`.
* `mul` — shift-and-add: `a·(b₀ + 2B) = a·b₀ + 2·(a·B)`; `mul_correct`.

With the adder seed, this is the second of the bit-level ops; the Q16.16 datapath
(scaled multiply = `mul` then `>>> FRAC`) and the bridge to Leg A's real-valued
bound are what remain.
-/

namespace MachLib.RTL

/-- Add a single carry bit to a bit-vector (a half-adder chain). -/
def addCarry : Bool → List Bool → List Bool
  | c, []      => [c]
  | c, b :: bs => (xor b c) :: addCarry (b && c) bs

/-- Half-adder correctness (8→4 Boolean cases by `rfl`). -/
theorem ha_correct (b c : Bool) :
    bitVal (xor b c) + 2 * bitVal (b && c) = bitVal b + bitVal c := by
  cases b <;> cases c <;> rfl

theorem addCarry_correct : ∀ (c : Bool) (bs : List Bool),
    toNat (addCarry c bs) = bitVal c + toNat bs
  | c, []      => by simp [addCarry, toNat]
  | c, b :: bs => by
      simp only [addCarry, toNat]
      rw [addCarry_correct (b && c) bs]
      have h := ha_correct b c
      omega

/-- Arbitrary-length adder (pads the shorter operand with implicit zeros). -/
def addc : Bool → List Bool → List Bool → List Bool
  | c, [],      bs      => addCarry c bs
  | c, a :: as, []      => addCarry c (a :: as)
  | c, a :: as, b :: bs => (fa a b c).1 :: addc (fa a b c).2 as bs

theorem bitVal_false : bitVal false = 0 := by decide
theorem bitVal_true : bitVal true = 1 := by decide

theorem addc_correct : ∀ (c : Bool) (a b : List Bool),
    toNat (addc c a b) = bitVal c + toNat a + toNat b
  | c, [],      bs      => by
      rw [show addc c [] bs = addCarry c bs from rfl, addCarry_correct]; simp [toNat]
  | c, a :: as, []      => by
      rw [show addc c (a :: as) [] = addCarry c (a :: as) from rfl, addCarry_correct]; simp [toNat]
  | c, a :: as, b :: bs => by
      simp only [addc, toNat]
      rw [addc_correct (fa a b c).2 as bs]
      have h := fa_correct a b c
      omega

/-- `add a b` adds two bit-vectors. -/
def add (a b : List Bool) : List Bool := addc false a b

theorem add_correct (a b : List Bool) : toNat (add a b) = toNat a + toNat b := by
  rw [add, addc_correct, bitVal_false]; omega

/-- Shift-and-add multiplier: `a·(b₀ + 2B) = a·b₀ + 2·(a·B)`. -/
def mul : List Bool → List Bool → List Bool
  | _, []       => []
  | a, b0 :: bs =>
      match b0 with
      | true  => add a (false :: mul a bs)
      | false => false :: mul a bs

theorem mul_help_t (M N : Nat) : M + 2 * (M * N) = M * (1 + 2 * N) := by
  rw [Nat.mul_add, Nat.mul_one, show M * (2 * N) = 2 * (M * N) from by rw [Nat.mul_left_comm]]
theorem mul_help_f (M N : Nat) : 2 * (M * N) = M * (0 + 2 * N) := by
  rw [Nat.zero_add, show M * (2 * N) = 2 * (M * N) from by rw [Nat.mul_left_comm]]

/-- **The multiplier computes multiplication.** `toNat (mul a b) = toNat a · toNat b`. -/
theorem mul_correct : ∀ (a b : List Bool), toNat (mul a b) = toNat a * toNat b
  | _, []       => by simp [mul, toNat]
  | a, b0 :: bs => by
      have ih := mul_correct a bs
      cases b0
      · -- b0 = false:  mul a (false :: bs) = false :: mul a bs
        simp only [mul, toNat]
        rw [bitVal_false, ih, Nat.zero_add]
        exact mul_help_f (toNat a) (toNat bs)
      · -- b0 = true:   mul a (true :: bs) = add a (false :: mul a bs)
        simp only [mul, toNat]
        rw [add_correct, bitVal_true]
        simp only [toNat]
        rw [bitVal_false, ih, Nat.zero_add]
        exact mul_help_t (toNat a) (toNat bs)

end MachLib.RTL
