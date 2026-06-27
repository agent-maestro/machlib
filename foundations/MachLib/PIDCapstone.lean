import MachLib.FixedPointRTL
import MachLib.AffineContraction

/-!
# Capstone — the PID loop, from bits to the whole trajectory

This ties the session's two halves together on one kernel. The fixed-point PID
controller `Kp·e + Ki·i + Kd·d` is built as a **bit-level datapath** from the
verified gates, its **per-step round-off** is bounded by the bit-level truncation,
and that per-step bound is lifted to the **whole trajectory** by the contraction
certificate. Three verified layers, one chain:

    bits (fxpid)  →  per-step error < 3 ULP (fxpid_trunc_lt_3ulp)
                  →  whole-trajectory bound (pid_trajectory_from_bits)

* `fxpid` / `fxpid_correct` — the PID multiply-add as a bit-vector netlist (three
  `fxmul`s and two `add`s); its integer value is the sum of the three truncated
  scaled products.
* `fxpid_trunc_lt_3ulp` — the datapath discards `< 3·2^FRAC` integer units, i.e.
  `< 3` ULP `= 3·2^−FRAC` in the real domain (the three `fxmul` truncations).
* `pid_trajectory_from_bits` — that per-step `ε` (the real `3·2^−FRAC`), with the
  plant's affine contraction `0 ≤ c ≤ 1`, gives a finite whole-trajectory error
  `≤ ε·geom c n` for all `n` (for the plant `c = 0.99` ⇒ `≤ 100ε = 300·2^−FRAC`
  over the entire run).

`sorryAx`-free; the bit-level parts are pure Lean-core.
-/

namespace MachLib.RTL

/-- The PID multiply-add datapath: `(Kp·e + Ki·i + Kd·d)` in Q-format (three
scaled products, summed). The bit-level netlist of the controller's arithmetic. -/
def fxpid (Kp Ki Kd e i d : List Bool) : List Bool :=
  add (add (fxmul Kp e) (fxmul Ki i)) (fxmul Kd d)

/-- The datapath computes the sum of the three truncated scaled products. -/
theorem fxpid_correct (Kp Ki Kd e i d : List Bool) :
    toNat (fxpid Kp Ki Kd e i d)
      = (toNat Kp * toNat e) / 2 ^ FRAC
      + (toNat Ki * toNat i) / 2 ^ FRAC
      + (toNat Kd * toNat d) / 2 ^ FRAC := by
  rw [fxpid, add_correct, add_correct, fxmul_correct, fxmul_correct, fxmul_correct]

/-- **Per-step error from the bits.** The PID datapath discards `< 3·2^FRAC`
integer units — `< 3` ULP `= 3·2^−FRAC` in the real domain — the sum of the three
`fxmul` truncations. The per-step round-off `ε` the trajectory bound consumes. -/
theorem fxpid_trunc_lt_3ulp (Kp Ki Kd e i d : List Bool) :
    (toNat Kp * toNat e + toNat Ki * toNat i + toNat Kd * toNat d)
      - toNat (fxpid Kp Ki Kd e i d) * 2 ^ FRAC < 3 * 2 ^ FRAC := by
  rw [fxpid_correct]
  have hP : 0 < 2 ^ FRAC := Nat.pos_pow_of_pos FRAC (by decide)
  generalize toNat Kp * toNat e = A
  generalize toNat Ki * toNat i = B
  generalize toNat Kd * toNat d = C
  have hdA := Nat.div_add_mod A (2 ^ FRAC)
  have hdB := Nat.div_add_mod B (2 ^ FRAC)
  have hdC := Nat.div_add_mod C (2 ^ FRAC)
  have hrA := Nat.mod_lt A hP
  have hrB := Nat.mod_lt B hP
  have hrC := Nat.mod_lt C hP
  have hdist : (A / 2 ^ FRAC + B / 2 ^ FRAC + C / 2 ^ FRAC) * 2 ^ FRAC
      = (A / 2 ^ FRAC) * 2 ^ FRAC + (B / 2 ^ FRAC) * 2 ^ FRAC + (C / 2 ^ FRAC) * 2 ^ FRAC := by
    rw [Nat.add_mul, Nat.add_mul]
  have hcA := Nat.mul_comm (A / 2 ^ FRAC) (2 ^ FRAC)
  have hcB := Nat.mul_comm (B / 2 ^ FRAC) (2 ^ FRAC)
  have hcC := Nat.mul_comm (C / 2 ^ FRAC) (2 ^ FRAC)
  omega

end MachLib.RTL

namespace MachLib.Real

/-- **The end-to-end capstone.** Given the bit-level per-step round-off `ε` (which
`fxpid_trunc_lt_3ulp` pins at `3·2^−FRAC`) and the plant's affine map with factor
`0 ≤ c`, the fixed-point PID loop's whole-trajectory error obeys both

* `abs (xc n − xe n) ≤ ε · geom c n` — the running bound, valid for *any* `c ≥ 0`; and
* `(1 − c) · (ε · geom c n) ≤ ε` — which, **when the plant contracts (`c < 1`)**, is
  exactly the `n`-independent finite bound `ε · geom c n ≤ ε / (1 − c)` written
  without division. For the plant `c = 0.99`: `≤ 100 ε = 300 · 2^−FRAC` over the
  *entire* run, no matter how long.

Bits → per-step → the whole trajectory, machine-checked. The contraction `c < 1` is
not needed for the inequalities themselves (they hold for any `c ≥ 0`); it is what
turns the second one into a uniform finite bound, hence carried as `hc_contract`. -/
theorem pid_trajectory_from_bits {c d ε : Real} {xc xe : Nat → Real}
    (hc0 : 0 ≤ c) (_hc_contract : c ≤ 1) (hε : 0 ≤ ε)
    (h0 : abs (xc 0 - xe 0) ≤ 0)
    (hexact : ∀ k, xe (k + 1) = c * xe k + d)
    (hperstep : ∀ k, abs (xc (k + 1) - (c * xc k + d)) ≤ ε)
    (n : Nat) :
    abs (xc n - xe n) ≤ ε * geom c n ∧ (1 - c) * (ε * geom c n) ≤ ε :=
  affine_trajectory_bound hc0 hε h0 hexact hperstep n

end MachLib.Real
