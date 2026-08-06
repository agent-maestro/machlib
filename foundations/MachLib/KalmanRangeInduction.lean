import MachLib.KalmanRangeQ88

/-!
# `Fits` at EVERY step — the envelope as one statement over the whole run

`KalmanRangeEnvelope` bounds the denominator formed from *a* post-update prior. That is the
one-step fact; **the claim chip 2 actually wants is about the run.** This file closes the induction
and states it once:

> ### For every `n`, the denominator at step `n+1` fits — under `2R + Q ≤ M`, and with NO condition on `P₀`.

The induction is not on the bound (which is one line from `kalman_var_map_lt_noise`) but on
**non-negativity of the covariance**: `kalmanVarMap` needs `0 ≤ P` at each step, and that has to be
carried forward. `kalmanP_nonneg` does it; everything else is direct.

## The step-0 hole, restated at the level of the run

`kalmanSDen 0 = (P₀ + Q) + R` is **excluded by the indexing, not by an extra hypothesis.** The
theorem quantifies over `kalmanSDen (n+1)`. **That is deliberate and it is the whole shape of the
result** — no envelope on `(Q, R)` can bound a denominator built from an arbitrary `P₀`, and the
hardware was measured breaking exactly there.

Also proves `kalmanVarMap r P = postVar P r`, the two names the corpus carries for one function.
**Stated as a bridge, not a merge** — merging the definitions would touch the MMSE chain, and that
is its own decision.

No new axioms. No `sorry`.
-/

namespace MachLib
namespace Real

/-- The posterior covariance after `n` updates: predict `P + Q`, then update through the variance
map. `kalmanP 0` is the initial prior, untouched. -/
noncomputable def kalmanP (P0 Q R : Real) : Nat → Real
  | 0     => P0
  | n + 1 => kalmanVarMap R (kalmanP P0 Q R n + Q)

/-- The denominator `S = P⁻ + R = (P + Q) + R` the reciprocal sees at step `n`. -/
noncomputable def kalmanSDen (P0 Q R : Real) (n : Nat) : Real :=
  (kalmanP P0 Q R n + Q) + R

/-- **The covariance never goes negative.** Carried by induction because `kalmanVarMap`'s bounds all
require `0 ≤ P`, and each step consumes the previous step's value. -/
theorem kalmanP_nonneg {P0 Q R : Real} (hP0 : 0 ≤ P0) (hQ : 0 ≤ Q) (hR : 0 < R) :
    ∀ n : Nat, 0 ≤ kalmanP P0 Q R n
  | 0 => hP0
  | n + 1 => by
    have hprev : 0 ≤ kalmanP P0 Q R n := kalmanP_nonneg hP0 hQ hR n
    have hpq : 0 ≤ kalmanP P0 Q R n + Q := add_nonneg hprev hQ
    have hden : 0 < (kalmanP P0 Q R n + Q) + R :=
      lt_of_lt_of_le hR (le_add_of_nonneg_left hpq)
    show 0 ≤ kalmanVarMap R (kalmanP P0 Q R n + Q)
    exact div_nonneg (mul_nonneg hpq (le_of_lt hR)) (le_of_lt hden)

/-- **After one update the covariance is below the measurement noise, forever.** The map forgets
`P₀` in a single step, so this holds at every `n+1` with no hypothesis on `P₀` beyond
non-negativity. -/
theorem kalmanP_lt_noise {P0 Q R : Real} (hP0 : 0 ≤ P0) (hQ : 0 ≤ Q) (hR : 0 < R) (n : Nat) :
    kalmanP P0 Q R (n + 1) < R := by
  have hpq : 0 ≤ kalmanP P0 Q R n + Q :=
    add_nonneg (kalmanP_nonneg hP0 hQ hR n) hQ
  show kalmanVarMap R (kalmanP P0 Q R n + Q) < R
  exact kalman_var_map_lt_noise hR hpq

/-- **THE RUN-LEVEL STATEMENT.** Under `2R + Q ≤ M`, the denominator `Fits` at **every** step after
the first — one statement covering the whole run, with `P₀` unconstrained beyond `0 ≤ P₀`. -/
theorem kalmanSDen_fits_all_steps {P0 Q R M : Real}
    (hP0 : 0 ≤ P0) (hQ : 0 ≤ Q) (hR : 0 < R) (henv : (R + R) + Q ≤ M) (n : Nat) :
    Fits M (kalmanSDen P0 Q R (n + 1)) := by
  have hpq : 0 ≤ kalmanP P0 Q R n + Q :=
    add_nonneg (kalmanP_nonneg hP0 hQ hR n) hQ
  show Fits M ((kalmanVarMap R (kalmanP P0 Q R n + Q) + Q) + R)
  exact kalman_S_fits_of_envelope hR hQ hpq henv

/-- **…and at Q8.8, therefore the die's range bit is silent at every step after the first.** The
end-to-end form: one design-time check on `(Q, R)`, and `mon_fire_range` provably cannot fire on the
`S` path for the rest of the run. -/
theorem q88_range_bit_silent_all_steps {P0 Q R : Real}
    (hP0 : 0 ≤ P0) (hQ : 0 ≤ Q) (hR : 0 < R) (henv : (R + R) + Q ≤ q88max) (n : Nat) :
    SignedFits q88max q88step (kalmanSDen P0 Q R (n + 1)) :=
  signedFits_of_fits (le_of_lt q88step_pos)
    (kalmanSDen_fits_all_steps hP0 hQ hR henv n)

/-- **The duplication, bridged.** `KalmanVarianceRecursion.kalmanVarMap` and
`GaussianConjugacy.postVar` are the same function with swapped arguments — the corpus composes both.

**A bridge, not a merge.** Unifying the definitions would touch the MMSE chain
(`posterior_mean_mmse`, `postMean_eq_kalman`, the recursion files), which is a refactor deserving
its own decision. This makes the identity available to any proof that needs to cross between them,
at zero risk to what already builds. -/
theorem kalmanVarMap_eq_postVar (r P : Real) : kalmanVarMap r P = postVar P r := rfl

end Real
end MachLib
