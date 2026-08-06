import MachLib.KalmanRangeEnvelope
import MachLib.KalmanFormatInstantiation

/-!
# The envelope at Q8.8, and the link from the DIE's range bit to `Fits`

Two things the range arc left owed:

1. **`Fits` was never instantiated at a format.** `M` stayed free, so the Q8.8 numbers lived in a
   result document as arithmetic rather than in a theorem.
2. **`mon_fire_range` was tied to `Fits` in PROSE.** The die computes an integer test; `Fits` is a
   statement about a real magnitude. Nobody had written down the relation.

## ▸ And writing it down found an OFF-BY-ONE

**A `W`-bit signed register holds `[−2^(W−1)·s, (2^(W−1)−1)·s]` — an ASYMMETRIC window.**
`Fits M` with `M = (2^(W−1)−1)·s` is **symmetric**. They are therefore **not equivalent**: the
hardware admits exactly one value `Fits` rejects, the negative edge `−2^(W−1)·s`.

**The implication that holds is the one you want, and only that one:**

> ### `Fits M v` ⟹ the register holds `v` ⟹ **`mon_fire_range` stays silent.**

**The design-time condition is STRICTER than the runtime bit**, by exactly one representable value.
That is the sound direction — a design rule that over-constrains by one LSB is safe; one that
under-constrains is not. **The converse is FALSE and `fits_strictly_stronger` witnesses it**, rather
than the file asserting an equivalence nobody checked.

`Fits` was defined symmetrically in `FixedPointRange` for the ordinary reason (`abs v ≤ M` is what
composes with the triangle inequality everywhere else). **Keeping it symmetric and proving the
one-sided implication is better than widening it to match the hardware**, because the widened
version would not be an `abs` bound and would stop composing.

No new axioms. No `sorry`.
-/

namespace MachLib
namespace Real

/-- Q8.8's maximum representable magnitude, `(2¹⁵ − 1)·2⁻⁸`. Built from `1` and `npow` because
`MachLib.Real` has no numeral literals — the same discipline as `q88step`. -/
noncomputable def q88max : Real := (npow 15 (1 + 1) - 1) * q88step

theorem q88max_nonneg : 0 ≤ q88max := by
  have h2 : (1 : Real) ≤ 1 + 1 := le_add_of_nonneg_right (le_of_lt one_pos)
  have h1 : (1 : Real) ≤ npow 15 (1 + 1) := one_le_npow (1 + 1) h2 15
  exact mul_nonneg (sub_nonneg_of_le h1) (le_of_lt q88step_pos)

/-- **The register's window, and it is ASYMMETRIC.** A `W`-bit signed register holds
`[−(M + s), M]` where `M = (2^(W−1) − 1)·s` — one more step of headroom below zero than above.
This is what `mon_fire_range` tests, stated at `Real`. -/
def SignedFits (M s v : Real) : Prop := -(M + s) ≤ v ∧ v ≤ M

/-- **THE LINK: the design-time condition implies the runtime bit stays silent.**

`Fits M v` (symmetric, `|v| ≤ M`) gives `SignedFits M s v` (the register's asymmetric window) for
any `s ≥ 0`. So an application that discharges the envelope's `Fits` obligations has thereby
discharged `mon_fire_range` — **the chain design-rule → theorem → die is closed in the sound
direction.** -/
theorem signedFits_of_fits {M s v : Real} (hs : 0 ≤ s) (h : Fits M v) : SignedFits M s v := by
  have hb := abs_le_iff.mp h            -- -M ≤ v ∧ v ≤ M
  -- -(M + s) ≤ -M  because  M ≤ M + s
  exact ⟨le_trans (neg_le_neg (le_add_of_nonneg_right hs)) hb.1, hb.2⟩

/-- **…and the converse is FALSE, witnessed.** At the negative edge `v = −(M + s)` with `s > 0`
the register holds `v` but `Fits M v` fails. **So the two conditions are not equivalent, and the
implication above cannot be strengthened to an iff.**

Shipped as a witness rather than a remark: an equivalence claimed and not checked is exactly the
defect class this corpus keeps finding. -/
theorem fits_strictly_stronger {M s : Real} (hM : 0 ≤ M) (hs : 0 < s) :
    SignedFits M s (-(M + s)) ∧ ¬ Fits M (-(M + s)) := by
  have hMs : 0 ≤ M + s := add_nonneg hM (le_of_lt hs)
  refine ⟨⟨le_refl _, ?_⟩, ?_⟩
  · -- -(M+s) ≤ M, since M - (-(M+s)) = 2M + s ≥ 0
    refine le_of_sub_nonneg ?_
    have e : M - -(M + s) = (M + M) + s := by mach_mpoly [M, s]
    rw [e]
    exact add_nonneg (add_nonneg hM hM) (le_of_lt hs)
  · -- ¬ (|−(M+s)| ≤ M), because |−(M+s)| = M + s > M
    intro hcon
    unfold Fits at hcon
    rw [abs_neg, abs_of_nonneg hMs] at hcon
    -- M + s ≤ M  contradicts  0 < s
    have hlt : M < M + s := by
      have := add_lt_add_left hs M
      have e : M + 0 = M := add_zero M
      rwa [e] at this
    exact lt_irrefl_ax M (lt_of_lt_of_le hlt hcon)

/-- **The envelope at Q8.8.** `2R + Q ≤ q88max` and `2·Zmax ≤ q88max` discharge both range hazards
for every step after the first, at chip 2's actual format.

The document arithmetic this replaces: `q88max = 32767/256 ≈ 127.996`, so the rule admits
`R ≤ 63.998` with `Q = 0` — a measurement-noise standard deviation up to ~8 units. **That figure is
now downstream of a theorem rather than of a spreadsheet.** -/
theorem kalman_range_envelope_at_q88 {R Q Pprev x z Zmax : Real}
    (hR : 0 < R) (hQ : 0 ≤ Q) (hP : 0 ≤ Pprev)
    (hx : abs x ≤ Zmax) (hz : abs z ≤ Zmax)
    (henvS : (R + R) + Q ≤ q88max) (henvZ : Zmax + Zmax ≤ q88max) :
    Fits q88max ((kalmanVarMap R Pprev + Q) + R) ∧ Fits q88max (z - x) :=
  kalman_range_envelope hR hQ hP hx hz henvS henvZ

/-- **End to end at Q8.8: the envelope silences the die's range bit.** Both quantities the RTL
range-checks sit inside the register's window whenever the design-time envelope holds.

This is the statement chip 2 can act on: **check `2R + Q ≤ q88max` and `2·Zmax ≤ q88max` once, at
design time, and `mon_fire_range` provably cannot fire after step 0.** -/
theorem q88_envelope_silences_range_bit {R Q Pprev x z Zmax : Real}
    (hR : 0 < R) (hQ : 0 ≤ Q) (hP : 0 ≤ Pprev)
    (hx : abs x ≤ Zmax) (hz : abs z ≤ Zmax)
    (henvS : (R + R) + Q ≤ q88max) (henvZ : Zmax + Zmax ≤ q88max) :
    SignedFits q88max q88step ((kalmanVarMap R Pprev + Q) + R)
      ∧ SignedFits q88max q88step (z - x) := by
  obtain ⟨hS, hI⟩ := kalman_range_envelope_at_q88 hR hQ hP hx hz henvS henvZ
  exact ⟨signedFits_of_fits (le_of_lt q88step_pos) hS,
         signedFits_of_fits (le_of_lt q88step_pos) hI⟩

end Real
end MachLib
