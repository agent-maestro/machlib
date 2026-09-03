import MachLib.EMLDepth2LogLower

/-!
# `log` of a depth-≤2 tree has an exponential CEILING

The companion to `depth_le_two_log_lower_at_infinity`, and the second of the two lemmas
`EMLDecayLadderStep`'s route map named as what the depth-4 decay rung waits on. **Both now exist.**

```
∃ C X₀, 1 ≤ X₀ ∧ ∀ x ≥ X₀,  log (B.eval x) ≤ exp x + C
```

for every `B` of depth ≤ 2, with no hypothesis on `B`. Depth 1's version
(`depth_le_one_log_le_linear`) has a *linear* ceiling `x + C`; one level of nesting costs a full
tower step, matching the floor's degradation in the companion file.

## The `eml` branch

With `v = exp (A.eval x) − log (C₂.eval x)` and `M = max 1 (−Cl)`, where `Cl` is depth 1's log
floor for `C₂`, so `−log (C₂.eval x) ≤ M` and `v ≤ exp (A.eval x) + M`:

* `v ≤ 0` — `log v = 0` by totalisation, and the constant is non-negative.
* `v > 0`, `A.eval x < 0` — then `exp (A.eval x) ≤ 1`, so `v ≤ 1 + M` outright and `log v` is
  bounded by a constant. No growth argument needed.
* `v > 0`, `A.eval x ≥ 0` — then `exp (A.eval x) ≥ 1`, so `exp A + M ≤ exp A · (1 + M)` and
  `log_mul` splits it into `A.eval x + log (1 + M)`. `depth_le_one_le_exp_shift` closes it with
  `A.eval x ≤ exp x + D`.

The middle case is why `M ≥ 1` is forced rather than convenient: `M > 0` is what makes
`exp A + M ≤ exp A · (1 + M)` follow from `exp A ≥ 1`, and clamping at `1` also keeps `log (1 + M)`
non-negative so the same constant serves the `v ≤ 0` branch.

## Scope

This does not prove `NodeDecayBound 3 3`. Both named prerequisites are now theorems, but the rung
itself is the depth-3 analogue of `depth3DecayExp_holds` and still has to be written. The ledger is
unchanged.
-/

namespace MachLib

open Real

private theorem log_nonneg_one_le {x : Real} (hx : 1 ≤ x) : (0 : Real) ≤ log x := by
  have h := log_mono (a := 1) (b := x) zero_lt_one_ax hx
  rw [log_one] at h; exact h

theorem depth_le_two_log_le_linear (B : EMLTree) (hB : B.depth ≤ 2) :
    ∃ C X₀ : Real, 1 ≤ X₀ ∧ ∀ x : Real, X₀ ≤ x → log (B.eval x) ≤ exp x + C := by
  cases B with
  | const c =>
      refine ⟨log c, 1, le_refl 1, fun x _ => ?_⟩
      show log c ≤ exp x + log c
      have u := add_le_add_wit (le_of_lt (exp_pos x)) (le_refl (log c))
      have e : (0 : Real) + log c = log c := by mach_ring
      rw [e] at u; exact u
  | var =>
      refine ⟨0, 1, le_refl 1, fun x hx => ?_⟩
      show log x ≤ exp x + 0
      have h1 : log x ≤ x := log_le_self_ge_one hx
      have h2 : x ≤ exp x := le_of_lt (exp_grows_strictly_thm x)
      have e : exp x + (0 : Real) = exp x := by mach_ring
      rw [e]; exact le_trans h1 h2
  | eml A C₂ =>
      have hA : A.depth ≤ 1 := by
        simp only [EMLTree.depth] at hB
        have := Nat.le_max_left A.depth C₂.depth; omega
      have hC2 : C₂.depth ≤ 1 := by
        simp only [EMLTree.depth] at hB
        have := Nat.le_max_right A.depth C₂.depth; omega
      obtain ⟨D, hD⟩ := depth_le_one_le_exp_shift A hA
      obtain ⟨Cl, Xl, hXl, hlow⟩ := depth_le_one_log_lower_at_infinity C₂ hC2
      -- M := 1 + |Cl| bounds -log C₂ above and is ≥ 1
      -- M bounds -log C₂ from above and is >= 1, so 1 + M > 0 and log (1+M) >= 0.
      -- `set` is a Mathlib tactic and MachLib has no Mathlib; introduce the abbreviation
      -- with a core-Lean existential instead (cf. `by_contra`, `le_or_lt`, `push_neg`).
      obtain ⟨M, hMdef⟩ : ∃ M : Real, M = max 1 (-Cl) := ⟨_, rfl⟩
      have hM1 : (1 : Real) ≤ M := by rw [hMdef]; exact le_max_left _ _
      have hMCl : -Cl ≤ M := by rw [hMdef]; exact le_max_right _ _
      have hM0 : (0 : Real) < M := lt_of_lt_of_le zero_lt_one_ax hM1
      have h1M : (1 : Real) ≤ 1 + M := by
        have u := add_le_add_wit (le_refl (1 : Real)) (le_of_lt hM0)
        have e : (1 : Real) + 0 = 1 := by mach_ring
        rw [e] at u; exact u
      have h1M0 : (0 : Real) < 1 + M := lt_of_lt_of_le zero_lt_one_ax h1M
      have hLog1M : (0 : Real) ≤ log (1 + M) := log_nonneg_one_le h1M
      refine ⟨max (D + log (1 + M)) (log (1 + M)), max 1 Xl, le_max_left 1 Xl, fun x hx => ?_⟩
      have hx1 : (1 : Real) ≤ x := le_trans (le_max_left 1 Xl) hx
      have hxl : Xl ≤ x := le_trans (le_max_right 1 Xl) hx
      have hCge : (0 : Real) ≤ max (D + log (1 + M)) (log (1 + M)) :=
        le_trans hLog1M (le_max_right _ _)
      show log (exp (A.eval x) - log (C₂.eval x)) ≤ exp x + max (D + log (1 + M)) (log (1 + M))
      -- -log C₂ ≤ M on the ray
      have hnegC : -log (C₂.eval x) ≤ M := le_trans (neg_le_neg_wit (hlow x hxl)) hMCl
      rcases lt_total 0 (exp (A.eval x) - log (C₂.eval x)) with hv | hv | hv
      · have hub : exp (A.eval x) - log (C₂.eval x) ≤ exp (A.eval x) + M := by
          have u := add_le_add_wit (le_refl (exp (A.eval x))) hnegC
          have e : exp (A.eval x) + -log (C₂.eval x)
              = exp (A.eval x) - log (C₂.eval x) := by mach_ring
          rw [e] at u; exact u
        have hmain : (0 : Real) ≤ A.eval x →
            log (exp (A.eval x) - log (C₂.eval x))
              ≤ exp x + max (D + log (1 + M)) (log (1 + M)) := by
          intro hA0
          have hexp1 : (1 : Real) ≤ exp (A.eval x) := by
            have := exp_monotone hA0; rw [exp_zero] at this; exact this
          -- exp A + M ≤ exp A * (1 + M), because exp A ≥ 1 and M > 0
          have hprod : exp (A.eval x) + M ≤ exp (A.eval x) * (1 + M) := by
            have hMe : M ≤ exp (A.eval x) * M :=
              le_trans (by have e : (1:Real) * M = M := by mach_ring
                           rw [e]; exact le_refl M)
                       (mul_le_mul_of_nonneg_right hexp1 (le_of_lt hM0))
            have u := add_le_add_wit (le_refl (exp (A.eval x))) hMe
            have e : exp (A.eval x) * (1 + M)
                = exp (A.eval x) + exp (A.eval x) * M := by mach_ring
            rw [e]; exact u
          have hle : exp (A.eval x) - log (C₂.eval x) ≤ exp (A.eval x) * (1 + M) :=
            le_trans hub hprod
          have hlm := log_mono hv hle
          rw [log_mul (exp_pos (A.eval x)) h1M0, log_exp] at hlm
          have hAx := hD x hx1
          have u := add_le_add_wit hAx (le_refl (log (1 + M)))
          have hchain : A.eval x + log (1 + M) ≤ exp x + D + log (1 + M) := by
            have e : exp x + D + log (1 + M) = exp x + D + log (1 + M) := by mach_ring
            rw [e]; exact u
          refine le_trans hlm (le_trans hchain ?_)
          have hmx : D + log (1 + M) ≤ max (D + log (1 + M)) (log (1 + M)) := le_max_left _ _
          have v2 := add_le_add_wit (le_refl (exp x)) hmx
          have e2 : exp x + D + log (1 + M) = exp x + (D + log (1 + M)) := by mach_ring
          rw [e2]; exact v2
        rcases lt_total (A.eval x) 0 with hA0 | hA0 | hA0
        · -- exp A < 1, so the node is bounded by 1 + M outright
          have hexp1 : exp (A.eval x) ≤ 1 := by
            have := exp_monotone (le_of_lt hA0); rw [exp_zero] at this; exact this
          have hle : exp (A.eval x) - log (C₂.eval x) ≤ 1 + M :=
            le_trans hub (add_le_add_wit hexp1 (le_refl M))
          have hlm := log_mono hv hle
          exact le_trans hlm (le_trans (le_trans (le_max_right (D + log (1 + M)) (log (1 + M)))
            (by have u := add_le_add_wit (le_of_lt (exp_pos x))
                  (le_refl (max (D + log (1 + M)) (log (1 + M))))
                have e : (0 : Real) + max (D + log (1 + M)) (log (1 + M))
                    = max (D + log (1 + M)) (log (1 + M)) := by mach_ring
                rw [e] at u; exact u)) (le_refl _))
        · exact hmain (le_of_eq hA0.symm)
        · exact hmain (le_of_lt hA0)
      · rw [← hv, log_nonpos (le_refl 0)]
        have u := add_le_add_wit (le_of_lt (exp_pos x)) hCge
        have e : (0 : Real) + 0 = 0 := by mach_ring
        rw [e] at u; exact u
      · rw [log_nonpos (le_of_lt hv)]
        have u := add_le_add_wit (le_of_lt (exp_pos x)) hCge
        have e : (0 : Real) + 0 = 0 := by mach_ring
        rw [e] at u; exact u

end MachLib
