import MachLib.BitVecMul

/-!
# Leg B — the Q16.16 datapath and the bridge to Leg A

The verified gates (`add`, `mul`) become the actual fixed-point datapath, and the
bridge to the analytic side (Leg A / `FixedPoint`) is proved:

* `fxmul` — the **scaled** product `(a·b) >>> FRAC` the RTL emits (`mul` then drop
  the low `FRAC` bits); `fxmul_correct : toNat (fxmul a b) = (A·B) / 2^FRAC`.
* `fxaffine` — a datapath `(c·x) >>> FRAC + d`: the bit-level form of the affine
  map (`AffineContraction`'s PID-plant / EMA / RC kernel); `fxaffine_correct`.
* `fxmul_trunc_lt_ulp` — **the bridge.** The truncation the shift discards is
  `< 2^FRAC` integer units = **< 1 ULP = 2^−FRAC in the real domain**. That is
  *exactly* Leg A's `|fxmul a b − a·b| ≤ s = 2^−FRAC` (`FixedPoint`), now derived
  from the bit-level division rather than assumed — the discrete and analytic
  halves of cross-target equivalence meeting on one quantity.

Pure Lean-core, Mathlib-free, `sorryAx`-free. `FRAC` is generic (16 for Q16.16).
-/

namespace MachLib.RTL

/-- Fractional-bit count of the Q-format (16 for Q16.16). -/
def FRAC : Nat := 16

/-! ## arithmetic shift right = drop low bits = integer division by `2^n` -/

theorem drop_succ_eq (n : Nat) (bs : List Bool) :
    bs.drop (n + 1) = (bs.drop 1).drop n := by
  cases bs with
  | nil      => simp
  | cons b bs => rfl

theorem drop_one_toNat (bs : List Bool) : toNat (bs.drop 1) = toNat bs / 2 := by
  cases bs with
  | nil      => simp [toNat]
  | cons b bs =>
      have hb : bitVal b ≤ 1 := by cases b <;> decide
      show toNat bs = toNat (b :: bs) / 2
      simp only [toNat]; omega

/-- Dropping `n` low bits is integer division by `2^n`. -/
theorem drop_toNat : ∀ (n : Nat) (bs : List Bool), toNat (bs.drop n) = toNat bs / 2 ^ n
  | 0, bs => by simp
  | n + 1, bs => by
      rw [drop_succ_eq, drop_toNat n (bs.drop 1), drop_one_toNat, Nat.div_div_eq_div_mul,
          show 2 * 2 ^ n = 2 ^ (n + 1) from by rw [Nat.pow_succ]; omega]

/-! ## the Q16.16 scaled product (the emitted `(a*b) >>> FRAC`) -/

/-- Scaled fixed-point product: `(a·b)` then drop the low `FRAC` bits. -/
def fxmul (a b : List Bool) : List Bool := (mul a b).drop FRAC

/-- The scaled product computes the truncated quotient `(A·B)/2^FRAC`. -/
theorem fxmul_correct (a b : List Bool) :
    toNat (fxmul a b) = (toNat a * toNat b) / 2 ^ FRAC := by
  rw [fxmul, drop_toNat, mul_correct]

/-! ## a datapath: the bit-level affine map `(c·x) >>> FRAC + d` -/

/-- The fixed-point affine step `c·x + d` (the PID plant / EMA / RC kernel). -/
def fxaffine (c x d : List Bool) : List Bool := add (fxmul c x) d

theorem fxaffine_correct (c x d : List Bool) :
    toNat (fxaffine c x d) = (toNat c * toNat x) / 2 ^ FRAC + toNat d := by
  rw [fxaffine, add_correct, fxmul_correct]

/-! ## the bridge to Leg A -/

/-- **The bridge: the scaled multiply truncates by `< 1 ULP`.** The bit-level
shift discards `(A·B) − fxmul(a,b)·2^FRAC < 2^FRAC` integer units — i.e. `< 1`
ULP `= 2^−FRAC` in the real domain. This is exactly Leg A's
`|fxmul a b − a·b| ≤ s = 2^−FRAC` (`FixedPoint`), derived here from the bit-level
division: the discrete RTL and the analytic forward-error bound on the same
quantity. -/
theorem fxmul_trunc_lt_ulp (a b : List Bool) :
    toNat a * toNat b - toNat (fxmul a b) * 2 ^ FRAC < 2 ^ FRAC := by
  rw [fxmul_correct]
  have hpos : 0 < 2 ^ FRAC := Nat.pos_pow_of_pos FRAC (by decide)
  have hdm := Nat.div_add_mod (toNat a * toNat b) (2 ^ FRAC)
  have hlt := Nat.mod_lt (toNat a * toNat b) hpos
  have hc := Nat.mul_comm (toNat a * toNat b / 2 ^ FRAC) (2 ^ FRAC)
  omega

end MachLib.RTL
