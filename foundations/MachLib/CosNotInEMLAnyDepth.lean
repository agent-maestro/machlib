import MachLib.EMLPfaffian
import MachLib.CosNotInEML
import MachLib.Linarith

/-!
# `cos ∉ EML_k(ℝ)` for ALL depths

Mirror of `sin_not_in_eml_any_depth` (in `EMLPfaffian.lean`) for cosine.
Both proofs use the same `eml_pfaffian` envelope + Khovanskii zero bound;
the only difference is the set of zeros used to overrun the bound:

  - sin's zeros at `i * π` for `i = 1, 2, ..., M+1` (in
    `EMLPfaffian.sin_not_in_eml_any_depth`).
  - cos's zeros at `i·π + π/2` for `i = 0, 1, ..., M` (this file).

## New axioms introduced (1, classical-true)

1. `eml_pfaffian_validon_from_cos_equality` — exact analog of the sin
   side axiom. Same classical smoothness-preservation argument; cos is
   smooth everywhere just like sin. A Smoothness module would discharge
   this and its sin sibling together.

`pi_div_one_plus_one_pos`/`pi_div_one_plus_one_lt_pi` (`0 < π/2`, `π/2 < π`) were
ORIGINALLY lifted as axioms here pending general `div_pos`-style infrastructure.
MachLib already had everything needed (`one_div_pos_of_pos`, `mul_lt_mul_of_pos_right`,
`div_def`, `mul_inv`) — 2026-07-15: both are now derived theorems, not axioms.

Net axiom delta: +1. The constructive infrastructure (cos zeros at
half-odd-pi, distinct-list, witness chain) is proven directly.

## What this does NOT do

- Does not modify `Trig.lean` or any pre-existing file.
- Does not introduce any new sorry.
- Does not change the sin barrier or any other prior proof.
-/

namespace MachLib

open Real

/-! ## Two small lemmas about π/2 — DERIVED (2026-07-15), no longer axioms -/

/-- `1 < 1 + 1`, hence `0 < 1 + 1`, hence `(1+1) ≠ 0`. Reused by both lemmas below. -/
private theorem one_lt_one_add_one : (1 : Real) < 1 + 1 := by
  have h := add_lt_add_left zero_lt_one_ax 1
  rwa [add_zero] at h

private theorem one_add_one_pos : (0 : Real) < 1 + 1 :=
  lt_trans_ax zero_lt_one_ax one_lt_one_add_one

private theorem one_add_one_ne_zero : (1 + 1 : Real) ≠ 0 :=
  (ne_of_lt one_add_one_pos).symm

/-- `0 < π/2`. Derived from `div_def` + `one_div_pos_of_pos` + `mul_pos` — no new axiom
needed, MachLib already had everything this required. -/
theorem pi_div_one_plus_one_pos : (0 : Real) < pi / (1 + 1) := by
  rw [div_def pi (1 + 1) one_add_one_ne_zero]
  exact mul_pos pi_pos (one_div_pos_of_pos one_add_one_pos)

/-- `π/2 < π`. Derived: `(π/2)*(1+1) = π` (via `div_def`/`mul_inv`), and `π/2 < (π/2)*(1+1)`
since `1 < 1+1` and `π/2 > 0` (`mul_lt_mul_of_pos_right`). -/
theorem pi_div_one_plus_one_lt_pi : pi / (1 + 1) < pi := by
  have hq_pos : (0 : Real) < pi / (1 + 1) := pi_div_one_plus_one_pos
  have hdouble : (pi / (1 + 1)) * (1 + 1) = pi := by
    rw [div_def pi (1 + 1) one_add_one_ne_zero, mul_assoc,
      mul_comm (1 / (1 + 1)) (1 + 1), mul_inv (1 + 1) one_add_one_ne_zero, mul_one_ax]
  have hstep : (1 : Real) * (pi / (1 + 1)) < (1 + 1) * (pi / (1 + 1)) :=
    mul_lt_mul_of_pos_right one_lt_one_add_one hq_pos
  rw [one_mul_thm, mul_comm (1 + 1) (pi / (1 + 1)), hdouble] at hstep
  exact hstep

/-! ## cos(k·π + π/2) = 0 for all Nat k -/

/-- Cos vanishes at all half-odd multiples of π. Proof by induction on
`k`, using `cos_add` together with the standing values
`cos(π/2) = 0` (CosNotInEML), `cos(π) = -1` and `sin(π) = 0` (Trig). -/
theorem cos_at_half_odd_pi (k : Nat) :
    cos (natCast k * pi + pi / (1 + 1)) = 0 := by
  induction k with
  | zero =>
    rw [natCast_zero, zero_mul, zero_add]
    exact cos_pi_div_two
  | succ n ih =>
    -- (natCast (n+1)) * pi + pi/(1+1)
    --   = (natCast n + 1) * pi + pi/(1+1)
    --   = natCast n * pi + pi + pi/(1+1)
    --   = (natCast n * pi + pi/(1+1)) + pi
    rw [natCast_succ]
    have hdistrib : (natCast n + 1) * pi = natCast n * pi + pi := by
      rw [mul_distrib_right, one_mul_thm]
    rw [hdistrib]
    have hassoc : natCast n * pi + pi + pi / (1 + 1)
                = (natCast n * pi + pi / (1 + 1)) + pi := by
      rw [add_assoc, add_comm pi (pi / (1 + 1)), ← add_assoc]
    rw [hassoc]
    -- cos((x + pi)) = cos x * cos pi - sin x * sin pi
    --              = cos x * (-1) - sin x * 0 = -cos x
    -- And IH says cos x = 0 for x = natCast n * pi + pi/(1+1), so:
    rw [cos_add, cos_pi, sin_pi, ih, mul_zero, sub_zero, zero_mul]

/-! ## Strict order on the half-odd-pi list -/

/-- The half-odd-pi expressions `natCast j * pi + pi/(1+1)` and
`natCast k * pi + pi/(1+1)` are strictly ordered when `j < k`.
Direct consequence of `natCast_mul_pi_lt` with the same offset added
to both sides. -/
theorem cos_half_odd_pi_lt {j k : Nat} (hjk : j < k) :
    natCast j * pi + pi / (1 + 1) < natCast k * pi + pi / (1 + 1) := by
  have h := natCast_mul_pi_lt hjk
  -- MachLib has add_lt_add_left only; commute to use it.
  have hL := add_lt_add_left h (pi / (1 + 1))
  -- hL : pi/(1+1) + natCast j * pi < pi/(1+1) + natCast k * pi
  rw [add_comm (pi / (1 + 1)) (natCast j * pi),
      add_comm (pi / (1 + 1)) (natCast k * pi)] at hL
  exact hL

/-- The list `[0·π + π/2, 1·π + π/2, …, M·π + π/2]` has no
duplicates. Same `List.Pairwise.map` + strict-order-injectivity pattern
as `sin_zeros_list_nodup`. -/
theorem cos_zeros_list_nodup (M : Nat) :
    ((List.range (M + 1)).map (fun i => natCast i * pi + pi / (1 + 1))).Nodup := by
  show List.Pairwise (· ≠ ·)
    ((List.range (M + 1)).map (fun i => natCast i * pi + pi / (1 + 1)))
  exact (List.nodup_range (M + 1)).map (fun i => natCast i * pi + pi / (1 + 1))
    (fun i j (_hij_neq : i ≠ j) => by
      intro hij_eq
      dsimp only at hij_eq
      rcases Nat.lt_or_ge i j with hlt | hge
      · have h := cos_half_odd_pi_lt hlt
        rw [hij_eq] at h
        exact lt_irrefl_ax _ h
      · have hlt2 : j < i := by omega
        have h := cos_half_odd_pi_lt hlt2
        rw [← hij_eq] at h
        exact lt_irrefl_ax _ h)

/-! ## Cos-equality forces validity (classical, same justification as sin)

If `t.eval x = cos x` for all `x : Real`, then `EMLPfaffianValidOn t 0 b`
holds for every `b > 0`. Same classical smoothness-preservation argument
as the sin side; see the docstring of
`eml_pfaffian_validon_from_sin_equality` in `EMLPfaffian.lean` for the
full reasoning (the same argument applies verbatim with cos in place
of sin, since both functions are globally smooth and the connectivity
argument is phase-independent).

Closure path: a Smoothness module would discharge both this axiom and
its sin sibling together; ~300-500 lines, multi-session. -/
axiom eml_pfaffian_validon_from_cos_equality
    (t : EMLTree) (hcos : ∀ x : Real, t.eval x = Real.cos x)
    (b : Real) (_hb_pos : 0 < b) :
    EMLPfaffianValidOn t 0 b

/-! ## Main theorem — moved (2026-07-15)

`cos_not_in_eml_any_depth` used to live here, applying `PfaffianFunction.zero_bound`.
Both it and the axiom it rested on (`zero_count_bound_classical`) have been deleted —
see `KhovanskiiLemma.lean`'s removal notes. The theorem now lives in
`EMLExplicitBoundCosBarrier.lean` (same name, re-proven via the constructive
`EMLExplicitBound.enc_combinedBound`), which imports this file for `cos_at_half_odd_pi`,
`cos_half_odd_pi_lt`, `cos_zeros_list_nodup`, `eml_pfaffian_validon_from_cos_equality`, and
the two `pi_div_one_plus_one_*` facts — kept here since they're still needed and moving them
would risk an import cycle (that file necessarily imports this one). -/

end MachLib
