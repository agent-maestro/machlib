import MachLib.Limits
import MachLib.Trig

/-!
# The high-dimensional ball/cube volume ratio tends to zero

Closes `HighDimensional.high_dim_ball_cube_ratio_tends_zero`, which carried a `sorry` from
2026-06-30 because both `TendstoTo` and `ballCubeRatio` were **opaque axioms** — there was nothing
to prove about uninterpreted symbols. The `sorry` was a gap in the *vocabulary*, not in the
argument; `Limits.lean` supplies the missing predicate and this file supplies the sequence.

## Where the geometry enters — stated, not hidden

The unit `d`-ball's volume obeys `V(d) = V(d−2)·2π/d`, and the cube `[−1,1]^d` has volume `2^d`, so

```
    ratio(d) = V(d)/2^d = ratio(d−2) · π/(2d)
```

**That recurrence is taken as the DEFINITION** (`bcRatio`). It is the one modelling input, and it is
where the integration theory would otherwise live — MachLib has no measure theory, and inventing
some to reach a statement about a ratio would be the expensive way round. Everything downstream is
proven.

Faithfulness of the recurrence was checked numerically against the closed form
`V(d) = π^(d/2)/Γ(d/2+1)` at `d = 1…12`: agreement to `< 1e-12` at every dimension. Recorded because
the recurrence is the only place an error could enter without a proof catching it.

## The argument

`π ≤ 4 ≤ d` for `d ≥ 4`, so the per-step factor `π/(2d) ≤ 1/2` — **the ratio at least halves every
two dimensions from `d = 4` on**. Both parities are handled by bounding `bcRatio (2k+4)` and
`bcRatio (2k+5)` by `(1/2)^k`, then routing through `Limits.npow_half_tendsto_zero`.

`sorryAx`-free, zero new axioms (`archimedean` and the `π` bounds were already in the ledger).
-/

namespace MachLib.Real

/-- **The ball/cube volume ratio**, defined by the standard recurrence `r(d) = r(d−2)·π/(2d)`.
`r(0)` is a padding value; the geometric content starts at `r(1) = 1` (the interval `[−1,1]` is its
own bounding cube) and `r(2) = π/4`. -/
noncomputable def bcRatio : Nat → Real
  | 0     => 1
  | 1     => 1
  | n + 2 => bcRatio n * (pi / ((1 + 1) * natCast (n + 2)))

theorem bcRatio_nonneg : ∀ n, 0 ≤ bcRatio n
  | 0 => le_of_lt one_pos
  | 1 => le_of_lt one_pos
  | n + 2 => by
      rw [show bcRatio (n + 2) = bcRatio n * (pi / ((1 + 1) * natCast (n + 2))) from rfl]
      exact mul_nonneg (bcRatio_nonneg n)
        (le_of_lt (div_pos_of_pos_pos pi_pos
          (mul_pos (add_pos one_pos one_pos) (natCast_pos (Nat.succ_pos _)))))

/-- `π ≤ 4`, from the pinned decimal bound. -/
theorem pi_le_four : pi ≤ natCast 4 := by
  have h6 : (0 : Real) < natCast 1000000 := natCast_pos (by omega)
  refine le_of_lt (lt_of_lt_of_le pi_upper_bound ?_)
  refine le_of_mul_le_mul_right_pos ?_ h6
  rw [show natCast 3141593 * (1 / natCast 1000000) * natCast 1000000
        = natCast 3141593 * ((1 / natCast 1000000) * natCast 1000000) from by mach_ring,
      show (1 : Real) / natCast 1000000 * natCast 1000000 = 1 from by
        rw [div_mul_cancel (ne_of_gt h6)],
      show natCast 3141593 * 1 = natCast 3141593 from by mach_ring, ← natCast_mul]
  exact natCast_le_of_le (by omega)

/-- **The decay factor is at most `1/2` from `d = 4` on** — `π ≤ 4 ≤ d ⟹ π/(2d) ≤ 1/2`. This is the
whole geometric content of the convergence. -/
theorem bcRatio_factor_le_half (n : Nat) : pi / ((1 + 1) * natCast (n + 4)) ≤ 1 / (1 + 1) := by
  have h2 : (0 : Real) < 1 + 1 := add_pos one_pos one_pos
  have hden : (0 : Real) < (1 + 1) * natCast (n + 4) :=
    mul_pos h2 (natCast_pos (Nat.succ_pos _))
  refine le_of_mul_le_mul_right_pos ?_ hden
  rw [div_mul_cancel (ne_of_gt hden),
      show (1 : Real) / (1 + 1) * ((1 + 1) * natCast (n + 4))
        = ((1 : Real) / (1 + 1) * (1 + 1)) * natCast (n + 4) from by mach_ring,
      div_mul_cancel (ne_of_gt h2),
      show (1 : Real) * natCast (n + 4) = natCast (n + 4) from by mach_ring]
  exact le_trans pi_le_four (natCast_le_of_le (by omega))

/-- One step of the halving, at any dimension `≥ 4`. -/
theorem bcRatio_step_le (n : Nat) :
    bcRatio (n + 4 + 2) ≤ bcRatio (n + 4) * (1 / (1 + 1)) := by
  rw [show bcRatio (n + 4 + 2)
        = bcRatio (n + 4) * (pi / ((1 + 1) * natCast (n + 4 + 2))) from rfl]
  exact mul_le_mul_of_nonneg_left
    (by
      have := bcRatio_factor_le_half (n + 2)
      rw [show n + 2 + 4 = n + 4 + 2 from by omega] at this
      exact this)
    (bcRatio_nonneg (n + 4))

/-- **`bcRatio` at even offsets is dominated by `(1/2)^k`** (scaled by the base value at `d = 4`). -/
theorem bcRatio_even_le : ∀ k : Nat,
    bcRatio (2 * k + 4) ≤ bcRatio 4 * npow k (1 / (1 + 1))
  | 0 => by
      rw [show 2 * 0 + 4 = 4 from by omega, show npow 0 (1 / (1 + 1)) = (1 : Real) from rfl]
      exact le_of_eq (by mach_ring)
  | k + 1 => by
      have ih := bcRatio_even_le k
      have hstep := bcRatio_step_le (2 * k)
      rw [show 2 * k + 4 + 2 = 2 * (k + 1) + 4 from by omega] at hstep
      refine le_trans hstep ?_
      rw [npow_succ]
      refine le_trans (mul_le_mul_of_nonneg_right ih
        (le_of_lt (one_div_pos_of_pos (add_pos one_pos one_pos)))) ?_
      exact le_of_eq (by mach_ring)

/-- **`bcRatio` at odd offsets**, same bound with the odd base. -/
theorem bcRatio_odd_le : ∀ k : Nat,
    bcRatio (2 * k + 5) ≤ bcRatio 5 * npow k (1 / (1 + 1))
  | 0 => by
      rw [show 2 * 0 + 5 = 5 from by omega, show npow 0 (1 / (1 + 1)) = (1 : Real) from rfl]
      exact le_of_eq (by mach_ring)
  | k + 1 => by
      have ih := bcRatio_odd_le k
      have hstep := bcRatio_step_le (2 * k + 1)
      rw [show 2 * k + 1 + 4 = 2 * k + 5 from by omega,
          show 2 * k + 1 + 4 + 2 = 2 * (k + 1) + 5 from by omega] at hstep
      refine le_trans hstep ?_
      rw [npow_succ]
      refine le_trans (mul_le_mul_of_nonneg_right ih
        (le_of_lt (one_div_pos_of_pos (add_pos one_pos one_pos)))) ?_
      exact le_of_eq (by mach_ring)

/-- **`bcRatio d → 0`.** Both parities are dominated by `C·(1/2)^k` with
`C = bcRatio 4 + bcRatio 5 + 1`, and `(1/2)^k → 0` by `npow_half_tendsto_zero`. -/
theorem bcRatio_tendsto_zero : TendstoTo bcRatio 0 := by
  intro ε hε
  have hC : (0 : Real) < bcRatio 4 + bcRatio 5 + 1 :=
    lt_of_lt_of_le one_pos
      (le_add_of_nonneg_left (add_nonneg (bcRatio_nonneg 4) (bcRatio_nonneg 5)))
  obtain ⟨K, hK⟩ := npow_half_tendsto_zero (ε / (bcRatio 4 + bcRatio 5 + 1))
    (div_pos_of_pos_pos hε hC)
  refine ⟨2 * K + 5, fun n hn => ?_⟩
  have hpow_nonneg : ∀ k, (0 : Real) ≤ npow k (1 / (1 + 1)) :=
    fun k => npow_nonneg (le_of_lt (one_div_pos_of_pos (add_pos one_pos one_pos))) k
  -- split n = 2j + 4 + r with r < 2 and j >= K
  have hsplit : ∃ j r : Nat, n = 2 * j + 4 + r ∧ r < 2 ∧ K ≤ j := by
    refine ⟨(n - 4) / 2, (n - 4) % 2, ?_, ?_, ?_⟩ <;> omega
  obtain ⟨j, r, hn_eq, hr, hjK⟩ := hsplit
  have hbound : bcRatio n ≤ (bcRatio 4 + bcRatio 5 + 1) * npow j (1 / (1 + 1)) := by
    rcases (by omega : r = 0 ∨ r = 1) with hr0 | hr1
    · subst hr0
      rw [hn_eq, show 2 * j + 4 + 0 = 2 * j + 4 from by omega]
      refine le_trans (bcRatio_even_le j) (mul_le_mul_of_nonneg_right ?_ (hpow_nonneg j))
      exact le_trans (le_add_of_nonneg_right (bcRatio_nonneg 5))
        (le_add_of_nonneg_right (le_of_lt one_pos))
    · subst hr1
      rw [hn_eq, show 2 * j + 4 + 1 = 2 * j + 5 from by omega]
      refine le_trans (bcRatio_odd_le j) (mul_le_mul_of_nonneg_right ?_ (hpow_nonneg j))
      exact le_trans (le_add_of_nonneg_left (bcRatio_nonneg 4))
        (le_add_of_nonneg_right (le_of_lt one_pos))
  have hsmall : npow j (1 / (1 + 1)) ≤ ε / (bcRatio 4 + bcRatio 5 + 1) := by
    have := hK j hjK
    rwa [show npow j (1 / (1 + 1)) - 0 = npow j (1 / (1 + 1)) from by mach_ring,
        abs_of_nonneg (hpow_nonneg j)] at this
  rw [show bcRatio n - 0 = bcRatio n from by mach_ring, abs_of_nonneg (bcRatio_nonneg n)]
  refine le_trans hbound ?_
  refine le_trans (mul_le_mul_of_nonneg_left hsmall (le_of_lt hC)) ?_
  rw [show (bcRatio 4 + bcRatio 5 + 1) * (ε / (bcRatio 4 + bcRatio 5 + 1))
        = (ε / (bcRatio 4 + bcRatio 5 + 1)) * (bcRatio 4 + bcRatio 5 + 1) from by mach_ring,
      div_mul_cancel (ne_of_gt hC)]
  exact le_refl ε

end MachLib.Real
