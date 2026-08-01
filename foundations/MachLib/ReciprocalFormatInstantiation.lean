import MachLib.NewtonReciprocalDivision

/-!
# Instantiating the NR reciprocal bound at a concrete fixed-point format

`NewtonReciprocalDivision` proves the 2-stage Newton bound with the truncation quantum `s` as a
**free variable**. That genericity is why a narrower format costs no new proofs — see
`monogate-research/chip/PROOF_DEBT_CLASSIFICATION.md`, which found **zero of 223 hardware theorem
signatures pin a format**.

This file packages the bound for a format described by its **denominator** `D = 2^FRAC`, with
`s = 1/D`.

**Deliberately no numerals.** Writing `256` into Lean would bake Q8.8 into the file and reproduce the
one mistake the corpus avoided everywhere else. `D` stays a variable: the format is an input.

## Discharging the hypotheses at Q8.8 (`D = 256`), for the record

| hypothesis | discharged by |
|---|---|
| `hs : 0 ≤ s` | `quantum_nonneg` below, from `0 ≤ D` |
| `hreg : (3/2 + \|b\|)·s ≤ 1/4` | arithmetic at the call site: at `D = 256` it holds for `\|b\| ≤ 62.5` |
| `hinv0 : \|1 − b·y₀\| ≤ 1/2` | **MEASURED, NOT PROVED** — worst `6.607e-02` over the octave, read out of the shipped RTL at `WIDTH=16, FRAC=8`. Margin `7.57×`. See `chip/SEED_MARGIN_RESULT.md`. |

`hinv0` is a property of a *seed circuit*, not a theorem about reals. **No Lean file can discharge
it**, and it is carried as a hypothesis precisely so the measurement has somewhere to attach. The
honest reading of the Q8.8 bound is therefore: **conditional on a bench-measured seed margin, and no
stronger than that measurement.**

**Consistency note.** The regime admits `|b| ≤ 62.5`, but the measured usable domain at Q8.8 is
`|b| ∈ [0.125, 16)` — 7 octaves (`chip/NARROW_KERNEL_RESULT.md`). **Representability binds first, not
the regime**: the proof is not the limiting factor at this format.

## HALTED: the regime-simplification bridge

The intended convenience lemma was *"`(3/2 + |b|)·(1/D) ≤ 1/4` follows from `4·(3/2 + |b|) ≤ D`"*,
which would turn every format into a one-line arithmetic check. **It is not shipped**, and the
obstruction is stated as a lemma-shaped claim rather than a narrative:

> The proof needs multiplicative cancellation — from `c·a ≤ c·b` and `0 < c`, conclude `a ≤ b`. From
> this import root, **`le_of_mul_le_mul_left`, `mul_pos` and `one_div_pos_of_pos` are all
> unreachable** (checked with `tools/reachable_lemmas.py`), and re-deriving three ordered-field
> lemmas to save callers one arithmetic step is the wrong trade.

Callers discharge `hreg` directly. The bridge is a convenience, not a gap in the certification.
-/

namespace MachLib

open Real

/-- The quantum of a format with denominator `D` is non-negative — the `hs` hypothesis of every
theorem in `NewtonReciprocalDivision`, discharged once. -/
theorem quantum_nonneg {D : Real} (hD : 0 ≤ D) : (0 : Real) ≤ 1 / D :=
  div_nonneg (le_of_lt one_pos) hD

/-- **The 2-stage Newton reciprocal bound at a format of denominator `D`.**

Identical to `nr_reciprocal_2stage` with `s := 1/D` and `hs` discharged. Its value is not
mathematical — it is that the format appears **once, as an argument**, so a reader can see at a glance
that nothing else in the statement depends on it. -/
theorem nr_reciprocal_2stage_at_format
    (b y0 y1 y2 by0 by1 D : Real) (hD : 0 ≤ D)
    (hinv0 : abs (1 - b * y0) ≤ 1 / (1 + 1))
    (hb0 : abs (by0 - b * y0) ≤ 1 / D) (hy1 : abs (y1 - y0 * ((1 + 1) - by0)) ≤ 1 / D)
    (hb1 : abs (by1 - b * y1) ≤ 1 / D) (hy2 : abs (y2 - y1 * ((1 + 1) - by1)) ≤ 1 / D)
    (hreg : (1 + 1 / (1 + 1) + abs b) * (1 / D) ≤ (1 / (1 + 1)) * (1 - 1 / (1 + 1))) :
    abs (1 - b * y2)
      ≤ ((1 - b * y0) * (1 - b * y0) + (1 + 1 / (1 + 1) + abs b) * (1 / D))
        * ((1 - b * y0) * (1 - b * y0) + (1 + 1 / (1 + 1) + abs b) * (1 / D))
        + (1 + 1 / (1 + 1) + abs b) * (1 / D) :=
  nr_reciprocal_2stage b y0 y1 y2 by0 by1 (1 / D) (quantum_nonneg hD)
    hinv0 hb0 hy1 hb1 hy2 hreg

end MachLib
