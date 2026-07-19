import MachLib.Differentiation
import MachLib.Rolle
import MachLib.FPModel
import MachLib.FieldLemmas

/-!
# `arctan` — declared as a primitive, its 1-Lipschitz bound DERIVED via MVT

`atan` is not in MachLib's analytic base, so it is declared here as a primitive function
(like `sin`/`cos`/`sinh`) with its defining facts `atan 0 = 0` and its derivative
`atan' = 1/(1+x²)` as axioms — the same *derivative-of-a-primitive* category as
`HasDerivAt_sin`/`HasDerivAt_cos` (which are axioms). **This file adds those 3 axioms**;
everything below is then *derived* (no further axioms):

* `atan` is **1-Lipschitz** (`atan' = 1/(1+x²) ≤ 1`), via MVT — like `sin`/`cos`/`tanh`;
* `|atan x| ≤ |x|` (1-Lipschitz from `atan 0 = 0`), so `atan` *preserves* a magnitude
  bound — no need for a `π/2` constant.

`asin` (`arcsin`) is left out: its derivative `1/√(1−x²)` is unbounded near `±1`, so it
needs a domain guard — the genuinely harder case for a single stdlib kernel.

## `arcsin` / `arccos` derivative axioms (added)

The domain-guarded derivatives `HasDerivAt_arcsin` / `HasDerivAt_arccos` below close that gap:
each takes an explicit `abs x < 1` side condition (unlike `HasDerivAt_atan`, unconditional for all
`x`), mirroring the standard calculus facts `d/dx arcsin x = 1/√(1−x²)` and
`d/dx arccos x = −1/√(1−x²)` on the open interval `(−1,1)`. `arccos`'s derivative is stated as the
NEGATION of `arcsin`'s directly (not derived from an `arcsin x + arccos x = π/2` identity — that
identity is not needed by, and is not proved by, this file) — the lowest-risk axiomatisation, exactly
mirroring how `arcsin`/`arccos` are already independent primitives in `Trig.lean`. The domain-bounded
local-Lipschitz bounds these support (`[-R,R]`, `R < 1`) live in `MachLib.InverseTrigBounded`. -/

namespace MachLib.Real

/-- `d/dx arcsin x = 1/√(1−x²)`, valid on the open interval `abs x < 1` (unbounded at `±1`). -/
axiom HasDerivAt_arcsin (x : Real) (hx : abs x < 1) :
    HasDerivAt arcsin (1 / sqrt (1 - x * x)) x

/-- `d/dx arccos x = −1/√(1−x²)`, valid on the open interval `abs x < 1` (unbounded at `±1`). Stated
as the independent negation of `HasDerivAt_arcsin`, not derived from an `arcsin`/`arccos` identity. -/
axiom HasDerivAt_arccos (x : Real) (hx : abs x < 1) :
    HasDerivAt arccos (-(1 / sqrt (1 - x * x))) x

/-- `d/dx sqrt x = 1/(2·√x)`, valid for `x > 0` (the standard fact; `sqrt` has no derivative
axiom of its own yet — `Trig.lean` only gives its algebraic properties). Needed to differentiate
`arcsin`/`arccos` a SECOND time and beyond: `HasDerivAt_arcsin` gives `arcsin' = 1/√(1−x²)`
directly as an independent axiom, but going further (the `AsinTaylorRemainder`/
`AcosTaylorRemainder` hardware forward-error certificates need up to the 7th derivative) requires
differentiating THROUGH the `sqrt`, which needs this general chain-rule building block — added
here rather than a narrower one-off axiom so it composes via the existing `HasDerivAt_comp`/
`HasDerivAt_inv` combinators at every level instead of postulating each level separately. -/
axiom HasDerivAt_sqrt (x : Real) (hx : 0 < x) :
    HasDerivAt sqrt (1 / (sqrt x + sqrt x)) x

/-- `arctan`, a primitive function. -/
axiom atan : Real → Real

/-- `arctan 0 = 0` (defining). -/
axiom atan_zero : atan 0 = 0

/-- `arctan' = 1/(1+x²)` (the derivative-of-primitive axiom, like `HasDerivAt_sin`). -/
axiom HasDerivAt_atan (x : Real) : HasDerivAt atan (1 / (1 + x * x)) x

/-- `|atan'| ≤ 1` (since `1 + x² ≥ 1`). -/
theorem atan_deriv_le_one (x : Real) : abs (1 / (1 + x * x)) ≤ 1 := by
  have hge1 : (1 : Real) ≤ 1 + x * x := le_add_of_nonneg_right (mul_self_nonneg x)
  have hpos : 0 < 1 + x * x := lt_of_lt_of_le zero_lt_one_ax hge1
  rw [abs_of_nonneg (one_div_nonneg_of_pos hpos)]
  exact div_le_one_of_le_of_pos hpos hge1

/-- **`atan` is 1-Lipschitz** — `|atan a − atan b| ≤ |a − b|`, via MVT. -/
theorem atan_lipschitz (a b : Real) : abs (atan a - atan b) ≤ abs (a - b) := by
  have step : ∀ p q : Real, p < q → abs (atan q - atan p) ≤ q - p := by
    intro p q hpq
    obtain ⟨c, f', _, _, hdc, hval⟩ :=
      mean_value_theorem_ct atan p q hpq (fun c _ _ => ⟨1 / (1 + c * c), HasDerivAt_atan c⟩)
    rw [hval, HasDerivAt_unique atan f' (1 / (1 + c * c)) c hdc (HasDerivAt_atan c),
        abs_mul, abs_of_nonneg (le_of_lt (sub_pos_of_lt hpq))]
    exact le_trans (mul_le_mul_of_nonneg_right (atan_deriv_le_one c)
      (le_of_lt (sub_pos_of_lt hpq))) (le_of_eq (one_mul_thm _))
  rcases lt_total a b with h | h | h
  · rw [show abs (atan a - atan b) = abs (atan b - atan a) from by
          rw [show atan a - atan b = -(atan b - atan a) from by mach_ring, abs_neg],
        show a - b = -(b - a) from by mach_ring, abs_neg,
        abs_of_nonneg (le_of_lt (sub_pos_of_lt h))]
    exact step a b h
  · rw [h]
    have hz : atan b - atan b = 0 := by mach_ring
    rw [hz, abs_zero]; exact abs_nonneg _
  · rw [abs_of_nonneg (le_of_lt (sub_pos_of_lt h))]; exact step b a h

/-- `|atan x| ≤ |x|` (1-Lipschitz from `atan 0 = 0`), so `atan` preserves a magnitude bound. -/
theorem abs_atan_le_abs (x : Real) : abs (atan x) ≤ abs x := by
  have h := atan_lipschitz x 0
  rwa [atan_zero, show atan x - 0 = atan x from by mach_ring, show x - 0 = x from by mach_ring] at h

end MachLib.Real
