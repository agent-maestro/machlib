import MachLib.Decimal
import MachLib.DivisionError
import MachLib.Iteration

/-!
# Sequence limits — the piece MachLib did not have

**MachLib has had no limit machinery at all.** `HighDimensional` needed one and reached for an
opaque `axiom TendstoTo : (Nat → Real) → Real → Prop` — a predicate with no content — which is why
`high_dim_ball_cube_ratio_tends_zero` carried a `sorry` since 2026-06-30: there was literally
nothing to prove about an uninterpreted symbol. The `sorry` was not a gap in the argument, it was a
gap in the vocabulary.

## What is here

* `TendstoTo f L` — the ordinary ε–N definition, Mathlib-free.
* `npow_le_one_half` — `(1/2)ⁿ ≤ 1`.
* `npow_half_mul_succ_le` — `(1/2)ⁿ·(n+1) ≤ 2`, by induction. The Bernoulli-flavoured step that
  makes geometric decay beat `1/n`.
* `npow_half_tendsto_zero` — `(1/2)ⁿ → 0`.

`Basic.archimedean` is the only axiom entering beyond the ordered field, and it is unavoidable: it
is exactly what turns "the terms get small" into "the terms get below any `ε`".

`sorryAx`-free, zero new axioms.
-/

namespace MachLib.Real

/-- **Convergence, ε–N.** Non-strict `≤` on both sides, matching the rest of MachLib's error
algebra. -/
def TendstoTo (f : Nat → Real) (L : Real) : Prop :=
  ∀ ε : Real, 0 < ε → ∃ N : Nat, ∀ n : Nat, N ≤ n → abs (f n - L) ≤ ε

/-- Non-vacuity for the definition: a constant sequence converges. If `TendstoTo` were
unsatisfiable everything below would be worthless. -/
theorem tendstoTo_const (c : Real) : TendstoTo (fun _ => c) c := by
  intro ε hε
  exact ⟨0, fun n _ => by
    rw [show c - c = (0 : Real) from by mach_ring, abs_zero]; exact le_of_lt hε⟩

/-- `natCast` is monotone. Proven inline rather than imported: the two existing copies live in
`RiemannIntegralMonotone` and `TanHardwareForwardError`, and pulling either in to get three lines
would make this foundational file depend on integration or on a hardware kernel's error analysis. -/
theorem natCast_le_of_le {i n : Nat} (h : i ≤ n) : natCast i ≤ natCast n := by
  obtain ⟨d, hd⟩ := Nat.le.dest h
  rw [← hd, natCast_add]
  exact le_add_of_nonneg_right (natCast_nonneg d)

private theorem half_pos : (0 : Real) < 1 / (1 + 1) :=
  one_div_pos_of_pos (add_pos one_pos one_pos)

private theorem half_le_one : (1 : Real) / (1 + 1) ≤ 1 :=
  div_le_one_of_le_of_pos (add_pos one_pos one_pos) (le_add_of_nonneg_right (le_of_lt one_pos))

/-- `(1/2)ⁿ ≤ 1`. -/
theorem npow_le_one_half : ∀ n : Nat, npow n (1 / (1 + 1)) ≤ 1
  | 0 => le_refl 1
  | n + 1 => by
      rw [npow_succ]
      refine le_trans (mul_le_mul' (le_of_lt half_pos) half_le_one
        (npow_nonneg (le_of_lt half_pos) n) (npow_le_one_half n)) ?_
      exact le_of_eq (by mach_ring)

/-- **`(1/2)ⁿ·(n+1) ≤ 2`** — the induction that makes geometric decay beat `1/n`.

Step: `(1/2)ⁿ⁺¹·(n+2) = ((1/2)ⁿ·(n+1) + (1/2)ⁿ)·(1/2) ≤ (2 + 1)·(1/2) ≤ 2`. -/
theorem npow_half_mul_succ_le : ∀ n : Nat, npow n (1 / (1 + 1)) * natCast (n + 1) ≤ 1 + 1
  | 0 => by
      rw [show npow 0 (1 / (1 + 1)) = (1 : Real) from rfl, natCast_succ, natCast_zero,
          show (1 : Real) * ((0 : Real) + 1) = 1 from by mach_ring]
      exact le_add_of_nonneg_left (le_of_lt one_pos)
  | n + 1 => by
      have ih := npow_half_mul_succ_le n
      have hle1 := npow_le_one_half n
      have hrw : npow (n + 1) (1 / (1 + 1)) * natCast (n + 1 + 1)
          = (npow n (1 / (1 + 1)) * natCast (n + 1) + npow n (1 / (1 + 1))) * (1 / (1 + 1)) := by
        rw [npow_succ, natCast_succ]
        mach_mpoly [natCast (n + 1), npow n (1 / (1 + 1)), (1 / (1 + 1) : Real)]
      rw [hrw]
      refine le_trans (mul_le_mul_of_nonneg_right (add_le_add_both ih hle1)
        (le_of_lt half_pos)) ?_
      -- 3·(1/2) ≤ 2, i.e. 3 ≤ 4 after clearing the divisor
      refine le_of_mul_le_mul_right_pos ?_ (add_pos one_pos one_pos)
      rw [show ((1 : Real) + 1 + 1) * (1 / (1 + 1)) * (1 + 1)
            = ((1 : Real) + 1 + 1) * ((1 / (1 + 1)) * (1 + 1)) from by mach_ring,
          show (1 : Real) / (1 + 1) * (1 + 1) = 1 from by
            rw [div_mul_cancel (two_ne_zero)],
          show ((1 : Real) + 1 + 1) * 1 = 1 + 1 + 1 from by mach_ring,
          show ((1 : Real) + 1) * (1 + 1) = 1 + 1 + 1 + 1 from by mach_ring]
      exact le_add_of_nonneg_right (le_of_lt one_pos)

/-- **`(1/2)ⁿ → 0`.** Geometric decay beats every `ε`, via `npow_half_mul_succ_le` and
`archimedean`. Everything that converges geometrically in MachLib can route through this. -/
theorem npow_half_tendsto_zero : TendstoTo (fun n => npow n (1 / (1 + 1))) 0 := by
  intro ε hε
  obtain ⟨m, hm⟩ := archimedean ((1 + 1) / ε)
  refine ⟨m, fun n hn => ?_⟩
  have hpow_nonneg : 0 ≤ npow n (1 / (1 + 1)) := npow_nonneg (le_of_lt half_pos) n
  rw [show npow n (1 / (1 + 1)) - 0 = npow n (1 / (1 + 1)) from by mach_ring,
      abs_of_nonneg hpow_nonneg]
  -- 2 < ε·m ≤ ε·(n+1), and (1/2)^n·(n+1) ≤ 2, so (1/2)^n·(n+1) ≤ ε·(n+1); cancel (n+1) > 0
  have hstep : (1 + 1 : Real) < ε * natCast m := by
    have h := mul_lt_mul_of_pos_right hm hε
    rw [div_mul_cancel (ne_of_gt hε)] at h
    rw [mul_comm]; exact h
  have hmn : natCast m ≤ natCast (n + 1) :=
    natCast_le_of_le (Nat.le_trans hn (Nat.le_succ n))
  have hpos : (0 : Real) < natCast (n + 1) := natCast_succ_pos n
  refine le_of_mul_le_mul_right_pos ?_ hpos
  refine le_trans (npow_half_mul_succ_le n) ?_
  refine le_trans (le_of_lt hstep) ?_
  exact mul_le_mul_of_nonneg_left hmn (le_of_lt hε)

end MachLib.Real
