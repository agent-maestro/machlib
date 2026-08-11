import MachLib.PIDCapstone
import MachLib.Decimal

/-!
# The `Nat` → `Real` bridge for the fixed-point datapath

**Why this file exists.** `FixedPointRTL.fxmul_trunc_lt_ulp` and
`PIDCapstone.fxpid_trunc_lt_3ulp` are statements about **counts of discarded integer units**. Every
document in this repo read them as "`< 1 ULP = 2⁻ᶠᴿᴬᶜ` / `< 3 ULP` **in the real domain**" — but
until 2026-08-10 that reading was carried by comments, with no theorem crossing from `Nat` into
`MachLib.Real`. Found while building the trust-boundary diagram for the end-to-end claim; see
`docs/what_is_proven.md` §2.

This file closes that join. It is the **first** of the two the flagship composition needs; the
second (controller error → closed-loop state-update error) needs a plant model and is still open.

Everything here is `MachLib.Real`'s ordered-field axioms plus `natCast_zero`/`natCast_succ`; no
analysis, no new axioms.
-/

namespace MachLib
namespace Real

/-- `natCast` is monotone. Induction on the gap, using `natCast_succ`. -/
theorem natCast_le_mono : ∀ {a b : Nat}, a ≤ b → natCast a ≤ natCast b := by
  intro a b h
  induction b with
  | zero =>
      have : a = 0 := Nat.le_zero.mp h
      subst this; exact le_refl _
  | succ n ih =>
      rcases Nat.lt_or_ge a (n + 1) with hlt | hge
      · have hle : a ≤ n := Nat.lt_succ_iff.mp hlt
        refine le_trans (ih hle) ?_
        rw [natCast_succ]
        exact le_add_of_nonneg_right (le_of_lt zero_lt_one_ax)
      · have : a = n + 1 := Nat.le_antisymm h hge
        subst this; exact le_refl _

/-- `natCast` is strictly monotone: `a < b` in `Nat` gives `natCast a < natCast b`. -/
theorem natCast_lt_mono {a b : Nat} (h : a < b) : natCast a < natCast b := by
  have hstep : natCast a < natCast (a + 1) := by
    rw [natCast_succ]
    have s := add_lt_add_left zero_lt_one_ax (natCast a)
    have e : natCast a + (0 : Real) = natCast a := by mach_ring
    rw [e] at s; exact s
  exact lt_of_lt_of_le hstep (natCast_le_mono h)

/-- `0 < natCast (2 ^ FRAC)` — the scale factor is a positive real. -/
theorem natCast_two_pow_frac_pos : (0 : Real) < natCast (2 ^ RTL.FRAC) :=
  natCast_pos (Nat.pow_pos (by decide))

/-! ## The bridge

`fxmul_trunc_lt_ulp` says `A·B − q·2^F < 2^F` in `Nat`, where `q = toNat (fxmul a b)`. Cast, and it
says the same about reals — which is what "one ULP" means once both sides are divided by the scale.
-/

/-- **The datapath's truncation, in the REAL domain.** `A·B < q·2^F + 2^F` over `MachLib.Real`,
where `q` is what the netlist actually computes.

Dividing through by `natCast (2^F)²` reads it in Q-format: the computed value `q/2^F` is below the
exact product `A·B/2^(2F)` by less than `1/2^F` — **one ULP**. That division is ordinary algebra in
an ordered field; before this theorem, the step from the `Nat` count to the real bound was not
algebra at all, but a convention stated in a comment. -/
theorem fxmul_real_trunc_lt_ulp (a b : List Bool) :
    natCast (RTL.toNat a) * natCast (RTL.toNat b)
      < natCast (RTL.toNat (RTL.fxmul a b)) * natCast (2 ^ RTL.FRAC)
        + natCast (2 ^ RTL.FRAC) := by
  -- in `Nat`: `A·B < q·2^F + 2^F`
  have hq : RTL.toNat (RTL.fxmul a b) * 2 ^ RTL.FRAC ≤ RTL.toNat a * RTL.toNat b := by
    rw [RTL.fxmul_correct]
    exact Nat.div_mul_le_self _ _
  have hnat : RTL.toNat a * RTL.toNat b
      < RTL.toNat (RTL.fxmul a b) * 2 ^ RTL.FRAC + 2 ^ RTL.FRAC := by
    have h := RTL.fxmul_trunc_lt_ulp a b
    omega
  have hc := natCast_lt_mono hnat
  rwa [natCast_mul, natCast_add, natCast_mul] at hc

/-- The other side: the netlist never *over*-computes. Together with the bound above, the real-domain
truncation lies in `[0, 2^F)` at product scale — i.e. in `[0, 2^−F)` after scaling. -/
theorem fxmul_real_trunc_nonneg (a b : List Bool) :
    natCast (RTL.toNat (RTL.fxmul a b)) * natCast (2 ^ RTL.FRAC)
      ≤ natCast (RTL.toNat a) * natCast (RTL.toNat b) := by
  have hq : RTL.toNat (RTL.fxmul a b) * 2 ^ RTL.FRAC ≤ RTL.toNat a * RTL.toNat b := by
    rw [RTL.fxmul_correct]
    exact Nat.div_mul_le_self _ _
  have hc := natCast_le_mono hq
  rwa [natCast_mul, natCast_mul] at hc

/-- **The PID datapath's truncation, in the real domain**: `< 3` ULP at product scale.
The real-domain counterpart of `PIDCapstone.fxpid_trunc_lt_3ulp`. -/
theorem fxpid_real_trunc_lt_3ulp (Kp Ki Kd e i d : List Bool) :
    natCast (RTL.toNat Kp) * natCast (RTL.toNat e)
      + natCast (RTL.toNat Ki) * natCast (RTL.toNat i)
      + natCast (RTL.toNat Kd) * natCast (RTL.toNat d)
    < natCast (RTL.toNat (RTL.fxpid Kp Ki Kd e i d)) * natCast (2 ^ RTL.FRAC)
      + natCast 3 * natCast (2 ^ RTL.FRAC) := by
  -- discharge the `Nat` fact rather than assume it: the netlist never over-computes,
  -- so the truncated subtraction in `fxpid_trunc_lt_3ulp` is the honest difference
  have hq : RTL.toNat (RTL.fxpid Kp Ki Kd e i d) * 2 ^ RTL.FRAC
      ≤ RTL.toNat Kp * RTL.toNat e + RTL.toNat Ki * RTL.toNat i
        + RTL.toNat Kd * RTL.toNat d := by
    rw [RTL.fxpid_correct]
    have h1 := Nat.div_mul_le_self (RTL.toNat Kp * RTL.toNat e) (2 ^ RTL.FRAC)
    have h2 := Nat.div_mul_le_self (RTL.toNat Ki * RTL.toNat i) (2 ^ RTL.FRAC)
    have h3 := Nat.div_mul_le_self (RTL.toNat Kd * RTL.toNat d) (2 ^ RTL.FRAC)
    have hd : (RTL.toNat Kp * RTL.toNat e / 2 ^ RTL.FRAC
          + RTL.toNat Ki * RTL.toNat i / 2 ^ RTL.FRAC
          + RTL.toNat Kd * RTL.toNat d / 2 ^ RTL.FRAC) * 2 ^ RTL.FRAC
        = (RTL.toNat Kp * RTL.toNat e / 2 ^ RTL.FRAC) * 2 ^ RTL.FRAC
          + (RTL.toNat Ki * RTL.toNat i / 2 ^ RTL.FRAC) * 2 ^ RTL.FRAC
          + (RTL.toNat Kd * RTL.toNat d / 2 ^ RTL.FRAC) * 2 ^ RTL.FRAC := by
      rw [Nat.add_mul, Nat.add_mul]
    omega
  have hnat : RTL.toNat Kp * RTL.toNat e + RTL.toNat Ki * RTL.toNat i
        + RTL.toNat Kd * RTL.toNat d
      < RTL.toNat (RTL.fxpid Kp Ki Kd e i d) * 2 ^ RTL.FRAC + 3 * 2 ^ RTL.FRAC := by
    have h := RTL.fxpid_trunc_lt_3ulp Kp Ki Kd e i d
    omega
  have hc := natCast_lt_mono hnat
  rwa [natCast_add, natCast_add, natCast_mul, natCast_mul, natCast_mul,
    natCast_add, natCast_mul, natCast_mul] at hc

end Real
end MachLib
