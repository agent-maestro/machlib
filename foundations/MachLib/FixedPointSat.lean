import MachLib.FixedPointRTL

/-!
# Leg B — saturating clamp (overflow saturation / anti-windup)

A real fixed-point PID datapath cannot let the integrator (or any accumulator)
overflow — it **saturates**: a value that no longer fits the datapath width is
clamped to the largest representable magnitude. This is the bit-level anti-windup
the `fxpid` datapath needs to be a usable controller.

The honest hardware primitive is **overflow saturation**, and it needs no
magnitude comparator: a value fits in `W` bits exactly when its high part
(`x.drop W`) is all zero, which is the bit-level `isZero` test reusing
`drop_toNat`. So:

* `allZero` / `allZero_iff` — the bit-level zero test, `allZero bs ↔ toNat bs = 0`.
* `ones` / `ones_toNat` — the all-ones vector, value `2^W − 1` (the max W-bit value).
* `fitsW` / `fitsW_iff` — `x` fits in `W` bits iff `toNat x < 2^W` (high part zero).
* `satW` / `satW_correct` — **the saturating clamp computes the Nat saturation**
  `min(toNat x, 2^W − 1)`: pass through if it fits, else clamp to `2^W − 1`.

Pure Lean-core, Mathlib-free, `sorryAx`-free. Two-sided (signed, lower-bound)
saturation is the extension; for the unsigned Q-format the lower bound is `0`
(automatic, `toNat ≥ 0`), so overflow saturation is the meaningful clamp.
-/

namespace MachLib.RTL

/-! ## the bit-level zero test -/

/-- All-zero test — the bit-level `isZero`. -/
def allZero : List Bool → Bool
  | []      => true
  | b :: bs => (!b) && allZero bs

/-- `allZero bs` holds exactly when the vector denotes `0`. -/
theorem allZero_iff : ∀ bs : List Bool, allZero bs = true ↔ toNat bs = 0
  | []      => by constructor <;> intro _ <;> rfl
  | b :: bs => by
      have ih := allZero_iff bs
      cases b
      · show ((!false) && allZero bs) = true ↔ toNat (false :: bs) = 0
        rw [show ((!false) && allZero bs) = allZero bs from rfl,
            show toNat (false :: bs) = bitVal false + 2 * toNat bs from rfl, bitVal_false, ih]
        constructor
        · intro h; omega
        · intro h; omega
      · show ((!true) && allZero bs) = true ↔ toNat (true :: bs) = 0
        rw [show ((!true) && allZero bs) = false from rfl,
            show toNat (true :: bs) = bitVal true + 2 * toNat bs from rfl, bitVal_true]
        constructor
        · intro h; exact absurd h (by decide)
        · intro h; exact absurd h (by omega)

/-! ## the all-ones (max-value) vector -/

/-- `n` one-bits — the all-ones vector, value `2ⁿ − 1` (max `n`-bit value). -/
def ones : Nat → List Bool
  | 0     => []
  | n + 1 => true :: ones n

theorem ones_toNat : ∀ n, toNat (ones n) = 2 ^ n - 1
  | 0     => by decide
  | n + 1 => by
      have ih := ones_toNat n
      have hp : 1 ≤ 2 ^ n := Nat.pos_pow_of_pos n (by decide)
      have hs : 2 ^ (n + 1) = 2 ^ n * 2 := Nat.pow_succ 2 n
      rw [show toNat (ones (n + 1)) = bitVal true + 2 * toNat (ones n) from rfl, bitVal_true, ih]
      omega

/-! ## fit test and the saturating clamp -/

/-- The value fits in `W` bits iff its high part (above bit `W`) is all zero. -/
def fitsW (W : Nat) (x : List Bool) : Bool := allZero (x.drop W)

theorem fitsW_iff (W : Nat) (x : List Bool) : fitsW W x = true ↔ toNat x < 2 ^ W := by
  have hpos : 0 < 2 ^ W := Nat.pos_pow_of_pos W (by decide)
  rw [fitsW, allZero_iff, drop_toNat]
  have hdm := Nat.div_add_mod (toNat x) (2 ^ W)
  have hlt := Nat.mod_lt (toNat x) hpos
  constructor
  · intro h; rw [h] at hdm; omega
  · intro h; exact Nat.div_eq_of_lt h

/-- **Saturating clamp to `W` bits** (overflow saturation / anti-windup): pass the
value through if it fits, else clamp to the max representable `2^W − 1`. -/
def satW (W : Nat) (x : List Bool) : List Bool := if fitsW W x then x else ones W

/-- **The saturating clamp computes the Nat saturation** `min(toNat x, 2^W − 1)`:
the value if it fits, the max representable otherwise. The bit-level anti-windup
the fixed-point PID datapath needs, verified against its integer semantics. -/
theorem satW_correct (W : Nat) (x : List Bool) :
    toNat (satW W x) = if toNat x < 2 ^ W then toNat x else 2 ^ W - 1 := by
  rw [satW]
  split
  · rename_i h
    rw [if_pos ((fitsW_iff W x).mp h)]
  · rename_i h
    rw [if_neg (fun hc => h ((fitsW_iff W x).mpr hc)), ones_toNat]

end MachLib.RTL
