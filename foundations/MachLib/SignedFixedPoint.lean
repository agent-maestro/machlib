import MachLib.FixedPointRealBridge

/-!
# A signed fixed-point datapath, as a difference of two unsigned ones

**Why this module exists.** `MachLib.RTL` is unsigned all the way down: `toNat` decodes a
`List Bool` as a natural number, and there is no subtraction, negation or two's-complement
anywhere in it. Every value the bit-level layer can express is therefore `≥ 0`. That is not a
missing convenience — it is the reason the closed-loop join this project advertises does not
exist. A controller's error signal is `r − y`, its output is signed, and **negative feedback
cannot be written in an unsigned model**, so no stabilising loop can be built inside `RTL` no
matter how much machinery is stacked on top. `foundations/docs/what_is_proven.md` §2 records that
as the first of four obstacles, and the other three sit behind it.

**The representation.** A signed value is a *pair* of unsigned bit-vectors, read as their
difference:

```
sval (p, n) = qval p − qval n
```

This is deliberately not two's-complement. Two's-complement needs a fixed word length, and the
width in `RTL` is not fixed: `addc` pads the shorter operand and grows the result, so there is no
wraparound to model and no place to put a sign bit. The difference representation needs no width,
introduces no new primitive, and — the point — makes **addition, negation, subtraction and
multiplication exact**, with every proof discharged by an existing `RTL` correctness lemma. All
the error stays where it already was: in the truncating multiply.

**The cost, stated honestly.** The representation is redundant (`(p, n)` and `(p + c, n + c)`
denote the same value) and it is not canonical, so nothing here is a normal form and no equality
of values is decided by equality of pairs. Nothing downstream needs that. The signed truncating
multiply loses `< 2 ulp` rather than `< 1 ulp`, because it truncates two unsigned products into
each component; that factor of two is real and is carried through the bounds rather than hidden.
-/

namespace MachLib

open Real

namespace SRTL

/-- A signed fixed-point value: a positive and a negative limb, read as their difference. -/
abbrev SVec : Type := List Bool × List Bool

/-- The exact value of a signed vector, in `MachLib.Real`. -/
noncomputable def sval (a : SVec) : Real := Real.qval a.1 - Real.qval a.2

/-- Embed an unsigned vector as a non-negative signed one. -/
def ofUnsigned (bs : List Bool) : SVec := (bs, [])

/-- Negation is a swap of the limbs — exact, and free. -/
def sneg (a : SVec) : SVec := (a.2, a.1)

/-- Addition is limbwise. -/
def sadd (a b : SVec) : SVec := (RTL.add a.1 b.1, RTL.add a.2 b.2)

/-- Subtraction is addition after a swap. **This is the primitive the unsigned layer lacks**, and
the whole reason the module exists. -/
def ssub (a b : SVec) : SVec := sadd a (sneg b)

/-! There is deliberately **no untruncated signed product** here. `RTL.mul` computes
`toNat a * toNat b`, which at `qval` scale is `qval a * qval b / ulp` — the raw product sits one
`Q`-scale too high, and restoring the scale is exactly what dropping `FRAC` bits does. A `smul`
stated as "the exact product" would be wrong by a factor of `2^FRAC`; the only signed multiply
offered is therefore the truncating one below. -/

/-- Truncating fixed-point product: the same four cross terms, each scaled by `2^FRAC` and
truncated. Each limb of the result therefore under-reports by `< 2 ulp`. -/
def sfxmul (a b : SVec) : SVec :=
  (RTL.add (RTL.fxmul a.1 b.1) (RTL.fxmul a.2 b.2),
   RTL.add (RTL.fxmul a.1 b.2) (RTL.fxmul a.2 b.1))

end SRTL

namespace Real

open SRTL

/-! ### The unsigned facts this layer stands on, restated at `qval` scale -/

/-- `qval` of a sum is the sum of the `qval`s: the adder is exact and carries no truncation. -/
theorem qval_add (a b : List Bool) :
    qval (RTL.add a b) = qval a + qval b := by
  unfold qval
  rw [RTL.add_correct, natCast_add, mul_distrib_right]

/-- The empty vector is zero. -/
theorem qval_nil : qval ([] : List Bool) = 0 := by
  unfold qval
  show natCast (RTL.toNat ([] : List Bool)) * ulp = 0
  have h : RTL.toNat ([] : List Bool) = 0 := rfl
  rw [h, natCast_zero, zero_mul]

/-- `qval` is non-negative — the fact that makes the unsigned layer unable to express feedback. -/
theorem qval_nonneg (bs : List Bool) : 0 ≤ qval bs := by
  unfold qval
  exact mul_nonneg (natCast_nonneg _) (le_of_lt ulp_pos)

/-- **The truncating multiply, at `qval` scale.** Extracted from `fxaffine_step_error` by taking
the offset to be the empty vector, which contributes `0`. -/
theorem qval_fxmul_error (a b : List Bool) :
    0 ≤ qval a * qval b - qval (RTL.fxmul a b)
    ∧ qval a * qval b - qval (RTL.fxmul a b) < ulp := by
  obtain ⟨hlo, hhi⟩ := fxaffine_step_error a b ([] : List Bool)
  have hfa : qval (RTL.fxaffine a b ([] : List Bool)) = qval (RTL.fxmul a b) := by
    show qval (RTL.add (RTL.fxmul a b) ([] : List Bool)) = qval (RTL.fxmul a b)
    rw [qval_add, qval_nil, add_zero]
  rw [hfa, qval_nil, add_zero] at hlo hhi
  exact ⟨hlo, hhi⟩

/-- Strict addition on both sides. `add_lt_add_right` does not exist in this corpus (it is on
`CLAUDE.md`'s list of order lemmas that are absent), so this goes through `add_lt_add_left` twice
with a commutation between. -/
private theorem add_lt_add_strict {a b c d : Real} (h1 : a < b) (h2 : c < d) : a + c < b + d := by
  have h3 : c + a < c + b := add_lt_add_left h1 c
  have h4 : b + c < b + d := add_lt_add_left h2 b
  have e1 : c + a = a + c := add_comm c a
  have e2 : c + b = b + c := add_comm c b
  rw [e1, e2] at h3
  exact lt_trans_ax h3 h4

/-! ### The signed layer: three exact operations and one that truncates -/

/-- Negation is exact. -/
theorem sval_sneg (a : SVec) : sval (sneg a) = -(sval a) := by
  show qval a.2 - qval a.1 = -(qval a.1 - qval a.2)
  mach_mpoly [qval a.1, qval a.2]

/-- Addition is exact. -/
theorem sval_sadd (a b : SVec) : sval (sadd a b) = sval a + sval b := by
  show qval (RTL.add a.1 b.1) - qval (RTL.add a.2 b.2)
      = (qval a.1 - qval a.2) + (qval b.1 - qval b.2)
  rw [qval_add, qval_add]
  mach_mpoly [qval a.1, qval a.2, qval b.1, qval b.2]

/-- **Subtraction is exact** — the operation the unsigned datapath cannot perform at all. -/
theorem sval_ssub (a b : SVec) : sval (ssub a b) = sval a - sval b := by
  show sval (sadd a (sneg b)) = sval a - sval b
  rw [sval_sadd, sval_sneg]
  mach_mpoly [sval a, sval b]

/-- An unsigned vector embeds with its own value. -/
theorem sval_ofUnsigned (bs : List Bool) : sval (ofUnsigned bs) = qval bs := by
  show qval bs - qval ([] : List Bool) = qval bs
  rw [qval_nil, sub_zero]

/-- **The signed truncating multiply loses less than `2 ulp`, in both directions.**

Each limb of `sfxmul` is a sum of two truncated unsigned products, and each truncation
under-reports by `< 1 ulp` and never over-reports (`qval_fxmul_error`). So the positive limb is
short by `< 2 ulp` and the negative limb is short by `< 2 ulp`, and the *difference* they denote
is therefore within `2 ulp` of the exact product on each side. The two-sidedness is what the
trajectory lemma consumes: an error that is one-sided in the unsigned world becomes two-sided as
soon as it can sit in either limb. -/
theorem sval_sfxmul_error (a b : SVec) :
    sval a * sval b - sval (sfxmul a b) < natCast 2 * ulp
    ∧ sval (sfxmul a b) - sval a * sval b < natCast 2 * ulp := by
  obtain ⟨p11lo, p11hi⟩ := qval_fxmul_error a.1 b.1
  obtain ⟨p22lo, p22hi⟩ := qval_fxmul_error a.2 b.2
  obtain ⟨p12lo, p12hi⟩ := qval_fxmul_error a.1 b.2
  obtain ⟨p21lo, p21hi⟩ := qval_fxmul_error a.2 b.1
  -- name the four truncation residues
  let e11 := qval a.1 * qval b.1 - qval (RTL.fxmul a.1 b.1)
  let e22 := qval a.2 * qval b.2 - qval (RTL.fxmul a.2 b.2)
  let e12 := qval a.1 * qval b.2 - qval (RTL.fxmul a.1 b.2)
  let e21 := qval a.2 * qval b.1 - qval (RTL.fxmul a.2 b.1)
  have hexpand : sval a * sval b - sval (sfxmul a b) = (e11 + e22) - (e12 + e21) := by
    show (qval a.1 - qval a.2) * (qval b.1 - qval b.2)
        - (qval (RTL.add (RTL.fxmul a.1 b.1) (RTL.fxmul a.2 b.2))
           - qval (RTL.add (RTL.fxmul a.1 b.2) (RTL.fxmul a.2 b.1)))
      = _
    rw [qval_add, qval_add]
    show _ = (qval a.1 * qval b.1 - qval (RTL.fxmul a.1 b.1)
              + (qval a.2 * qval b.2 - qval (RTL.fxmul a.2 b.2)))
             - (qval a.1 * qval b.2 - qval (RTL.fxmul a.1 b.2)
                + (qval a.2 * qval b.1 - qval (RTL.fxmul a.2 b.1)))
    mach_mpoly [qval a.1, qval a.2, qval b.1, qval b.2,
                qval (RTL.fxmul a.1 b.1), qval (RTL.fxmul a.2 b.2),
                qval (RTL.fxmul a.1 b.2), qval (RTL.fxmul a.2 b.1)]
  have htwo : natCast 2 * ulp = ulp + ulp := by
    have h2 : natCast 2 = 1 + 1 := by
      have e : (2 : Nat) = 0 + 1 + 1 := by omega
      rw [e, natCast_succ, natCast_succ, natCast_zero, zero_add]
    rw [h2]; mach_mpoly [ulp]
  refine ⟨?_, ?_⟩
  · -- (e11 + e22) − (e12 + e21) ≤ e11 + e22 < 2 ulp, since e12, e21 ≥ 0
    rw [hexpand, htwo]
    have hsum : e11 + e22 < ulp + ulp := add_lt_add_strict p11hi p22hi
    have hdrop : (e11 + e22) - (e12 + e21) ≤ e11 + e22 := by
      have hnn : (0 : Real) ≤ e12 + e21 := add_nonneg p12lo p21lo
      have u := add_le_add_both (le_refl (e11 + e22)) (neg_nonpos_of_nonneg hnn)
      have en : e11 + e22 + -(e12 + e21) = (e11 + e22) - (e12 + e21) := by
        mach_mpoly [e11, e22, e12, e21]
      have ez : e11 + e22 + 0 = e11 + e22 := by mach_ring
      rw [en, ez] at u; exact u
    exact lt_of_le_of_lt hdrop hsum
  · -- and symmetrically in the other direction
    have hflip : sval (sfxmul a b) - sval a * sval b = (e12 + e21) - (e11 + e22) := by
      have u := hexpand
      have e : sval (sfxmul a b) - sval a * sval b
          = -(sval a * sval b - sval (sfxmul a b)) := by
        mach_mpoly [sval a * sval b, sval (sfxmul a b)]
      rw [e, u]
      mach_mpoly [e11, e22, e12, e21]
    rw [hflip, htwo]
    have hsum : e12 + e21 < ulp + ulp := add_lt_add_strict p12hi p21hi
    have hdrop : (e12 + e21) - (e11 + e22) ≤ e12 + e21 := by
      have hnn : (0 : Real) ≤ e11 + e22 := add_nonneg p11lo p22lo
      have u := add_le_add_both (le_refl (e12 + e21)) (neg_nonpos_of_nonneg hnn)
      have en : e12 + e21 + -(e11 + e22) = (e12 + e21) - (e11 + e22) := by
        mach_mpoly [e11, e22, e12, e21]
      have ez : e12 + e21 + 0 = e12 + e21 := by mach_ring
      rw [en, ez] at u; exact u
    exact lt_of_le_of_lt hdrop hsum

end Real

namespace SRTL

/-- **The closed loop, over bits.** A proportional controller around the affine plant
`x ↦ A·x`, with the control `KP·(R − x)` fed back into the state update. Every operation is a
signed one, so the error signal `R − X` is a genuine subtraction and the feedback is genuinely
negative — neither is expressible in `MachLib.RTL`. -/
def sfxloop (A KP R X0 : SVec) : Nat → SVec
  | 0 => X0
  | k + 1 =>
      let x := sfxloop A KP R X0 k
      sadd (sfxmul A x) (sfxmul KP (ssub R x))

end SRTL

namespace Real

open SRTL

/-- The exact real trajectory of the same loop. Closing a proportional controller around an
affine plant leaves an **affine** map — `A·x + KP·(R − x) = (A − KP)·x + KP·R` — which is why the
corpus's scalar first-order trajectory lemma applies here without a vector-state generalisation.
That is a property of the P controller and not a shortcut: an integrator would leave this class,
and `what_is_proven.md` §2 says so. -/
noncomputable def exactLoop (A KP R X0 : SVec) : Nat → Real
  | 0 => sval X0
  | k + 1 => (sval A - sval KP) * exactLoop A KP R X0 k + sval KP * sval R

private theorem natCast_four_ulp : natCast 4 * ulp = natCast 2 * ulp + natCast 2 * ulp := by
  have h : natCast 4 = natCast 2 + natCast 2 := by
    have e : (4 : Nat) = 2 + 2 := by omega
    rw [e, natCast_add]
  rw [h]; mach_mpoly [natCast 2, ulp]

/-- **One step of the closed loop is within `4 ulp` of the exact affine step.** Two truncating
signed multiplies, each two-sided within `2 ulp`; the adder and the subtractor are exact and
contribute nothing. -/
theorem sfxloop_step_error (A KP R X : SVec) :
    abs (sval (sadd (sfxmul A X) (sfxmul KP (ssub R X)))
         - ((sval A - sval KP) * sval X + sval KP * sval R)) ≤ natCast 4 * ulp := by
  obtain ⟨hp1, hn1⟩ := sval_sfxmul_error A X
  obtain ⟨hp2, hn2⟩ := sval_sfxmul_error KP (ssub R X)
  have hsub : sval (ssub R X) = sval R - sval X := sval_ssub R X
  -- the residue splits into the two multiplies' residues
  have hsplit : sval (sadd (sfxmul A X) (sfxmul KP (ssub R X)))
        - ((sval A - sval KP) * sval X + sval KP * sval R)
      = (sval (sfxmul A X) - sval A * sval X)
        + (sval (sfxmul KP (ssub R X)) - sval KP * sval (ssub R X)) := by
    rw [sval_sadd, hsub]
    mach_mpoly [sval (sfxmul A X), sval (sfxmul KP (ssub R X)), sval A, sval KP, sval R, sval X]
  rw [hsplit, natCast_four_ulp]
  refine abs_le_of ?_ ?_
  · exact add_le_add_both (le_of_lt hn1) (le_of_lt hn2)
  · have e : -((sval (sfxmul A X) - sval A * sval X)
              + (sval (sfxmul KP (ssub R X)) - sval KP * sval (ssub R X)))
        = (sval A * sval X - sval (sfxmul A X))
          + (sval KP * sval (ssub R X) - sval (sfxmul KP (ssub R X))) := by
      mach_mpoly [sval (sfxmul A X), sval A * sval X,
                  sval (sfxmul KP (ssub R X)), sval KP * sval (ssub R X)]
    rw [e]
    exact add_le_add_both (le_of_lt hp1) (le_of_lt hp2)

/-- **The join, for a proportional controller: the signed bit-level closed loop tracks the exact
real closed loop.**

The subject is the datapath: `sfxloop` is built from `List Bool` pairs by `sadd`, `ssub` and the
truncating `sfxmul`, and `exactLoop` is the real recurrence it is meant to implement. The
per-step error is **derived** from the bits (`sfxloop_step_error`, `4 ulp` from two truncating
multiplies), not supplied as a hypothesis — which is the distinction `what_is_proven.md` §2 draws
between this and `pid_trajectory_from_bits`, whose `ε` is universally quantified.

The contraction hypothesis `sval KP ≤ sval A` says the proportional gain does not exceed the
plant pole, so the closed-loop map `(A − KP)` is non-negative; `affine_trajectory_bound` supplies
the rest and also returns the ultimate bound `(1 − c)·(ε·geom c n) ≤ ε`.

**What this is not.** It is a P controller, not PID: there is no integrator and no anti-windup,
and the closed-loop map stays first-order, which is exactly why the existing scalar trajectory
lemma suffices. The PID join needs a state that is not scalar, and remains open. -/
theorem sfxloop_tracks_exact (A KP R X0 : SVec) (hgain : sval KP ≤ sval A) (n : Nat) :
    abs (sval (sfxloop A KP R X0 n) - exactLoop A KP R X0 n)
      ≤ natCast 4 * ulp * geom (sval A - sval KP) n
    ∧ (1 - (sval A - sval KP)) * (natCast 4 * ulp * geom (sval A - sval KP) n)
      ≤ natCast 4 * ulp := by
  refine affine_trajectory_bound
    (c := sval A - sval KP) (d := sval KP * sval R) (ε := natCast 4 * ulp)
    (xc := fun m => sval (sfxloop A KP R X0 m)) (xe := exactLoop A KP R X0)
    (sub_nonneg_of_le hgain) ?_ ?_ (fun k => rfl) (fun k => sfxloop_step_error A KP R _) n
  · exact mul_nonneg (natCast_nonneg 4) (le_of_lt ulp_pos)
  · have e : sval (sfxloop A KP R X0 0) - exactLoop A KP R X0 0 = 0 := by
      show sval X0 - sval X0 = 0
      mach_mpoly [sval X0]
    rw [e, abs_zero]
    exact le_refl 0

/-! ### Specimens — because a conditional theorem is not evidence until its hypotheses are met

This corpus has one recorded case of a flagship theorem that was **vacuously true for weeks while
every gate passed**, because two of its hypotheses were unsatisfiable. The rule written after it
is that a capstone ships with a specimen discharging every hypothesis at a concrete point, so the
file stops compiling if a hypothesis ever becomes unsatisfiable again. These are that specimen. -/

/-- `[true]` is the bit-vector for `1`; `[false, true]` for `2` (`toNat` is little-endian). -/
private theorem toNat_one : RTL.toNat [true] = 1 := by decide

private theorem toNat_two : RTL.toNat [false, true] = 2 := by decide

/-- **The signed layer represents a negative value.** `sval ([], [true]) = −ulp < 0`, and no
`List Bool` has a negative `qval` — this is the gap the module exists to close, exhibited rather
than asserted. -/
theorem sval_neg_specimen : sval ([], [true]) < 0 := by
  show qval ([] : List Bool) - qval [true] < 0
  rw [qval_nil]
  have hq : (0 : Real) < qval [true] := by
    unfold qval
    rw [toNat_one]
    have h1 : natCast 1 = 1 := by
      have e : (1 : Nat) = 0 + 1 := by omega
      rw [e, natCast_succ, natCast_zero, zero_add]
    rw [h1, one_mul_thm]
    exact ulp_pos
  have u := add_lt_add_left hq (-qval [true])
  have e1 : -qval [true] + 0 = 0 - qval [true] := by mach_mpoly [qval [true]]
  have e2 : -qval [true] + qval [true] = 0 := by mach_ring
  rw [e1, e2] at u
  exact u

/-- **The tracking theorem's gain hypothesis is satisfiable**, at `KP = 1 ulp`, `A = 2 ulp`. -/
theorem gain_specimen : sval (ofUnsigned [true]) ≤ sval (ofUnsigned [false, true]) := by
  rw [sval_ofUnsigned, sval_ofUnsigned]
  unfold qval
  rw [toNat_one, toNat_two]
  refine mul_le_mul_of_nonneg_right ?_ (le_of_lt ulp_pos)
  exact natCast_le_mono (by omega)

/-- **The capstone, instantiated.** Every hypothesis discharged at a concrete datapath, so the
bound is a statement about actual bit vectors and not an implication with no instances. -/
theorem sfxloop_tracks_exact_specimen (n : Nat) :
    abs (sval (sfxloop (ofUnsigned [false, true]) (ofUnsigned [true])
                       (ofUnsigned [true]) (ofUnsigned []) n)
         - exactLoop (ofUnsigned [false, true]) (ofUnsigned [true])
                     (ofUnsigned [true]) (ofUnsigned []) n)
      ≤ natCast 4 * ulp
        * geom (sval (ofUnsigned [false, true]) - sval (ofUnsigned [true])) n :=
  (sfxloop_tracks_exact _ _ _ _ gain_specimen n).1

end Real

end MachLib
