import MachLib.EMLGermSign
import MachLib.EMLDecoderOffPositives

/-!
# `Fbasis` has AT MOST ONE zero, on all of `ℝ`

`EMLGermSign.Fbasis_root` proves a root EXISTS in `(e^(−e), 1)`. It obtains that root from
`exists_unique_root_of_deriv_pos`, which also returns uniqueness — and then **discards it**
(`⟨r, hr1, hr2, hr3, _⟩`). So the corpus has known the root is unique *within that window* since
`Fbasis_root` was written, and has never said so, nor extended it off the window.

Both halves of the global statement were already present and never combined:

* `y ≤ 0` — `Fbasis_eq_exp_of_nonpos` gives `Fbasis y = exp y`, and `exp_pos` makes that `> 0`.
  There are no zeros at all on the non-positive side.
* `0 < y` — `Fbasis_strictMono` is strict monotonicity, hence injectivity, hence at most one zero.

**Why this is the lever for `OneQueryLevelSet`'s bounded half.** With uniqueness,
`Fbasis (P x / Q x) = 0` is equivalent to `P x / Q x = r` for the single root `r`, i.e. to
`P x − r · Q x = 0` — a POLYNOMIAL condition. A polynomial is identically zero or has finitely
many roots, and that dichotomy is exactly the shape `OneQueryLevelSet` asks for. The transcendental
question collapses to a polynomial one, and it collapses on a bounded interval just as well as on a
ray, which is where `queryGerm_finite_zeros_on_ray` could not reach
(`EMLZeroListFromBound`: "the other half is the bounded region below `R`").

This module states the uniqueness only. It does not claim the bounded half — the general germ is
`bipev N x (Fbasis …)`, a polynomial in `Fbasis` rather than `Fbasis` itself, and that reduction is
not made here.
-/

namespace MachLib

open Real

/-- `Fbasis` is strictly positive wherever its argument is non-positive — so every zero of
`Fbasis` is positive. -/
theorem Fbasis_pos_of_nonpos {y : Real} (hy : y ≤ 0) : 0 < Fbasis y := by
  rw [Fbasis_eq_exp_of_nonpos hy]; exact exp_pos y

/-- A zero of `Fbasis` is necessarily positive. -/
theorem pos_of_Fbasis_eq_zero {y : Real} (h : Fbasis y = 0) : 0 < y := by
  rcases lt_total 0 y with hy | hy | hy
  · exact hy
  · have hp := Fbasis_pos_of_nonpos (le_of_eq hy.symm)
    rw [h] at hp
    exact absurd hp (lt_irrefl_ax (0 : Real))
  · have hp := Fbasis_pos_of_nonpos (le_of_lt hy)
    rw [h] at hp
    exact absurd hp (lt_irrefl_ax (0 : Real))

/-- **`Fbasis` has at most one zero on all of `ℝ`.** -/
theorem Fbasis_zero_unique {a b : Real} (ha : Fbasis a = 0) (hb : Fbasis b = 0) : a = b := by
  have ha0 : 0 < a := pos_of_Fbasis_eq_zero ha
  have hb0 : 0 < b := pos_of_Fbasis_eq_zero hb
  rcases lt_total a b with h | h | h
  · have hlt := Fbasis_strictMono ha0 h
    rw [ha, hb] at hlt
    exact absurd hlt (lt_irrefl_ax (0 : Real))
  · exact h
  · have hlt := Fbasis_strictMono hb0 h
    rw [ha, hb] at hlt
    exact absurd hlt (lt_irrefl_ax (0 : Real))

/-- **`Fbasis` has exactly one zero, and it is in `(e^(−e), 1)`.**

This is the statement `Fbasis_root` could have made and did not: it obtained uniqueness from
`exists_unique_root_of_deriv_pos` and dropped it on the floor. Existence comes from there; the
`∀` half is `Fbasis_zero_unique` above, which also extends the uniqueness OFF the window — the
underlying lemma only knew `(e^(−e), 1)`, while `Fbasis` has no zeros anywhere on `y ≤ 0` and is
injective on all of `(0, ∞)`.

It is also the non-vacuity witness for this module. `Fbasis_zero_unique` alone is a statement about
zeros of `Fbasis`, and would be vacuously true of a function with none; the existential half shows
it is not (`a_theorem_can_be_vacuous_and_all_gates_pass`). -/
theorem Fbasis_exists_unique_root :
    ∃ r : Real, exp (-(exp 1)) < r ∧ r < 1 ∧ Fbasis r = 0 ∧ ∀ s : Real, Fbasis s = 0 → s = r := by
  obtain ⟨r, hr1, hr2, hr3⟩ := Fbasis_root
  exact ⟨r, hr1, hr2, hr3, fun s hs => Fbasis_zero_unique hs hr3⟩

end MachLib
