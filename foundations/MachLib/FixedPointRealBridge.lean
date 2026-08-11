import MachLib.PIDCapstone
import MachLib.Decimal
import MachLib.FPModel

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

/-! ## ▸ Join 2, first half: the state-update disturbance

The closed-loop theorem consumes `|xc (k+1) − (c·xc k + d)| ≤ ε` — a bound on the **state update**.
`fxpid` is the *controller's* multiply-add and is the wrong subject for it; the right one is
`RTL.fxaffine`, which `FixedPointRTL` already documents as "the PID plant / EMA / RC kernel". That
mismatch is part of why the flagship chain never composed.

Below, the Q-format value of one `fxaffine` step differs from the exact real affine step by
**less than one ULP, and never negatively** — the datapath only ever truncates. This is the
disturbance `δ_k` the closed-loop hypothesis wants. -/

/-- One unit in the last place, as a real. -/
noncomputable def ulp : Real := 1 / natCast (2 ^ RTL.FRAC)

/-- The Q-format value of a bit-vector: `toNat bs · 2⁻ᶠᴿᴬᶜ`. -/
noncomputable def qval (bs : List Bool) : Real := natCast (RTL.toNat bs) * ulp

theorem ulp_pos : (0 : Real) < ulp := one_div_pos_of_pos natCast_two_pow_frac_pos

theorem ulp_scale : natCast (2 ^ RTL.FRAC) * ulp = 1 := by
  show natCast (2 ^ RTL.FRAC) * (1 / natCast (2 ^ RTL.FRAC)) = 1
  exact mul_inv _ (ne_of_gt natCast_two_pow_frac_pos)

/-- **The per-step disturbance of the fixed-point affine datapath.**

`0 ≤ (c·x + d) − fxaffine(c,x,d) < 1 ULP` in Q-format values. The exact real affine step and the one
the netlist computes differ by a single truncation, and the sign is one-directional.

This is the quantity the closed-loop bound calls `ε` — now *derived from the datapath* rather than
introduced as a free variable. -/
theorem fxaffine_step_error (c x d : List Bool) :
    0 ≤ (qval c * qval x + qval d) - qval (RTL.fxaffine c x d)
    ∧ (qval c * qval x + qval d) - qval (RTL.fxaffine c x d) < ulp := by
  -- rewrite the netlist's value
  have hval : qval (RTL.fxaffine c x d)
      = (natCast (RTL.toNat (RTL.fxmul c x)) + natCast (RTL.toNat d)) * ulp := by
    show natCast (RTL.toNat (RTL.fxaffine c x d)) * ulp = _
    rw [RTL.fxaffine_correct, ← RTL.fxmul_correct, natCast_add]
  -- the scale identity, in the shape the algebra needs
  have hsc : natCast (RTL.toNat (RTL.fxmul c x)) * ulp
      = natCast (RTL.toNat (RTL.fxmul c x)) * natCast (2 ^ RTL.FRAC) * (ulp * ulp) := by
    have e : natCast (RTL.toNat (RTL.fxmul c x)) * natCast (2 ^ RTL.FRAC) * (ulp * ulp)
        = natCast (RTL.toNat (RTL.fxmul c x)) * (natCast (2 ^ RTL.FRAC) * ulp) * ulp := by
      mach_mpoly [natCast (RTL.toNat (RTL.fxmul c x)), natCast (2 ^ RTL.FRAC), ulp]
    rw [e, ulp_scale]
    mach_mpoly [natCast (RTL.toNat (RTL.fxmul c x)), ulp]
  -- the difference, in one product
  have key : (qval c * qval x + qval d) - qval (RTL.fxaffine c x d)
      = (natCast (RTL.toNat c) * natCast (RTL.toNat x)
          - natCast (RTL.toNat (RTL.fxmul c x)) * natCast (2 ^ RTL.FRAC)) * (ulp * ulp) := by
    show natCast (RTL.toNat c) * ulp * (natCast (RTL.toNat x) * ulp)
        + natCast (RTL.toNat d) * ulp - qval (RTL.fxaffine c x d) = _
    rw [hval]
    have expand : natCast (RTL.toNat c) * ulp * (natCast (RTL.toNat x) * ulp)
          + natCast (RTL.toNat d) * ulp
          - (natCast (RTL.toNat (RTL.fxmul c x)) + natCast (RTL.toNat d)) * ulp
        = natCast (RTL.toNat c) * natCast (RTL.toNat x) * (ulp * ulp)
          - natCast (RTL.toNat (RTL.fxmul c x)) * ulp := by
      mach_mpoly [natCast (RTL.toNat c), natCast (RTL.toNat x), natCast (RTL.toNat d),
        natCast (RTL.toNat (RTL.fxmul c x)), ulp]
    rw [expand, hsc]
    mach_mpoly [natCast (RTL.toNat c), natCast (RTL.toNat x),
      natCast (RTL.toNat (RTL.fxmul c x)), natCast (2 ^ RTL.FRAC), ulp]
  rw [key]
  have huu : (0 : Real) < ulp * ulp := mul_pos ulp_pos ulp_pos
  constructor
  · -- non-negative: the netlist never over-computes
    have hnn : (0 : Real) ≤ natCast (RTL.toNat c) * natCast (RTL.toNat x)
        - natCast (RTL.toNat (RTL.fxmul c x)) * natCast (2 ^ RTL.FRAC) :=
      sub_nonneg_of_le (fxmul_real_trunc_nonneg c x)
    have t := mul_le_mul_of_nonneg_right hnn (le_of_lt huu)
    have e : (0 : Real) * (ulp * ulp) = 0 := by mach_ring
    rw [e] at t; exact t
  · -- strictly under one ULP
    have hlt : natCast (RTL.toNat c) * natCast (RTL.toNat x)
        - natCast (RTL.toNat (RTL.fxmul c x)) * natCast (2 ^ RTL.FRAC)
        < natCast (2 ^ RTL.FRAC) := by
      have s := fxmul_real_trunc_lt_ulp c x
      have u := add_lt_add_left s (-(natCast (RTL.toNat (RTL.fxmul c x))
        * natCast (2 ^ RTL.FRAC)))
      have l : -(natCast (RTL.toNat (RTL.fxmul c x)) * natCast (2 ^ RTL.FRAC))
            + natCast (RTL.toNat c) * natCast (RTL.toNat x)
          = natCast (RTL.toNat c) * natCast (RTL.toNat x)
            - natCast (RTL.toNat (RTL.fxmul c x)) * natCast (2 ^ RTL.FRAC) := by
        mach_mpoly [natCast (RTL.toNat c), natCast (RTL.toNat x),
          natCast (RTL.toNat (RTL.fxmul c x)), natCast (2 ^ RTL.FRAC)]
      have r : -(natCast (RTL.toNat (RTL.fxmul c x)) * natCast (2 ^ RTL.FRAC))
            + (natCast (RTL.toNat (RTL.fxmul c x)) * natCast (2 ^ RTL.FRAC)
              + natCast (2 ^ RTL.FRAC))
          = natCast (2 ^ RTL.FRAC) := by
        mach_mpoly [natCast (RTL.toNat (RTL.fxmul c x)), natCast (2 ^ RTL.FRAC)]
      rw [l, r] at u; exact u
    have t := mul_lt_mul_of_pos_right hlt huu
    -- `natCast (2^F) · (ulp · ulp) = ulp`
    have e : natCast (2 ^ RTL.FRAC) * (ulp * ulp) = ulp := by
      have e2 : natCast (2 ^ RTL.FRAC) * (ulp * ulp)
          = (natCast (2 ^ RTL.FRAC) * ulp) * ulp := by
        mach_mpoly [natCast (2 ^ RTL.FRAC), ulp]
      rw [e2, ulp_scale]
      mach_mpoly [ulp]
    rw [e] at t; exact t

/-! ## ▸▸ Join 2, closed: the datapath's own error drives the trajectory bound

`fxaffine_step_error` supplies exactly the per-step hypothesis `affine_trajectory_bound` consumes,
so the two halves compose. The result below quantifies over **bit-vector trajectories produced by
the netlist** and bounds their divergence from the exact real affine trajectory by
`ulp · geom (qval c) n` — where `ulp` is not a free parameter but the datapath's own truncation.

Contrast `pid_trajectory_from_bits`, whose statement mentions no bit-level object and whose `ε` is
universally quantified. This one names `RTL.fxaffine`. That is the difference the claim auditor's
`statement_mentions` check was added to detect. -/

/-- The exact real affine trajectory started from a bit-vector's Q-value. -/
noncomputable def exactTraj (c d : List Bool) (x0 : List Bool) : Nat → Real
  | 0 => qval x0
  | k + 1 => qval c * exactTraj c d x0 k + qval d

/-- The bit-vector trajectory the netlist actually produces. -/
def fxTraj (c d : List Bool) (x0 : List Bool) : Nat → List Bool
  | 0 => x0
  | k + 1 => RTL.fxaffine c (fxTraj c d x0 k) d

/-- # ▸▸▸ **The fixed-point affine loop tracks the exact real loop, with the datapath's own ULP.**

For every `n`, the Q-value of the netlist's `n`-th state is within `ulp · geom (qval c) n` of the
exact real trajectory — and when the plant contracts, `(1 − qval c) · (ulp · geom …) ≤ ulp` turns
that into a bound independent of `n`.

**The `ε` here is `ulp`**, produced by `fxaffine_step_error` from the netlist, not supplied by the
caller. This is the composition the flagship claim asserted and did not have. -/
theorem fxaffine_traj_tracks_exact (c d x0 : List Bool) (hc0 : 0 ≤ qval c) (n : Nat) :
    abs (qval (fxTraj c d x0 n) - exactTraj c d x0 n) ≤ ulp * geom (qval c) n
    ∧ (1 - qval c) * (ulp * geom (qval c) n) ≤ ulp := by
  refine affine_trajectory_bound (c := qval c) (d := qval d) (ε := ulp)
    (xc := fun m => qval (fxTraj c d x0 m)) (xe := exactTraj c d x0)
    hc0 (le_of_lt ulp_pos) ?_ (fun k => rfl) (fun k => ?_) n
  · show abs (qval (fxTraj c d x0 0) - exactTraj c d x0 0) ≤ 0
    have e : qval (fxTraj c d x0 0) - exactTraj c d x0 0 = 0 := by
      show qval x0 - qval x0 = 0
      mach_ring
    rw [e, abs_zero]
    exact le_refl _
  · -- the per-step bound IS the datapath's truncation
    show abs (qval (RTL.fxaffine c (fxTraj c d x0 k) d)
      - (qval c * qval (fxTraj c d x0 k) + qval d)) ≤ ulp
    obtain ⟨hlo, hhi⟩ := fxaffine_step_error c (fxTraj c d x0 k) d
    refine abs_le_of ?_ ?_
    · -- computed − exact ≤ 0 ≤ ulp
      have s := add_le_add_left hlo (qval (RTL.fxaffine c (fxTraj c d x0 k) d)
        - (qval c * qval (fxTraj c d x0 k) + qval d))
      have l : qval (RTL.fxaffine c (fxTraj c d x0 k) d)
            - (qval c * qval (fxTraj c d x0 k) + qval d) + (0 : Real)
          = qval (RTL.fxaffine c (fxTraj c d x0 k) d)
            - (qval c * qval (fxTraj c d x0 k) + qval d) := by
        mach_mpoly [qval (RTL.fxaffine c (fxTraj c d x0 k) d), qval c,
          qval (fxTraj c d x0 k), qval d]
      have r : qval (RTL.fxaffine c (fxTraj c d x0 k) d)
            - (qval c * qval (fxTraj c d x0 k) + qval d)
            + (qval c * qval (fxTraj c d x0 k) + qval d
              - qval (RTL.fxaffine c (fxTraj c d x0 k) d)) = (0 : Real) := by
        mach_mpoly [qval (RTL.fxaffine c (fxTraj c d x0 k) d), qval c,
          qval (fxTraj c d x0 k), qval d]
      rw [l, r] at s
      exact le_trans s (le_of_lt ulp_pos)
    · -- exact − computed < ulp
      have e : -(qval (RTL.fxaffine c (fxTraj c d x0 k) d)
            - (qval c * qval (fxTraj c d x0 k) + qval d))
          = qval c * qval (fxTraj c d x0 k) + qval d
            - qval (RTL.fxaffine c (fxTraj c d x0 k) d) := by
        mach_mpoly [qval (RTL.fxaffine c (fxTraj c d x0 k) d), qval c,
          qval (fxTraj c d x0 k), qval d]
      rw [e]
      exact le_of_lt hhi

end Real
end MachLib
