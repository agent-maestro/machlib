import MachLib.EMLTowerAfterSign

/-!
# The decay bound does not iterate: `V₃` is false

`(dd)` discharged the *crossing* half of `V_j` at every depth and said the **rate** half was
untouched. It is worse than untouched. The rate statement, generalised one rung from where it is
proved, is **false** — so the programme `EMLCertifiedSynthesis` describes for `TowerReducesToSign`
("proving the growth/decay pair iterates at every depth — `U_j` and `V_j` for all `j`") cannot
succeed in that form.

## The statement and the witness

`depth_le_two_decay_on_ray` is `V₂`:

```
t.depth ≤ 2 → ∃ C X₀, 1 ≤ X₀ ∧ ∀ x ≥ X₀, 0 < t.eval x → -log (t.eval x) ≤ C + log x
```

`V₃` is the same with `≤ 3`. Take

```
expVar    = eml var (const 1)              value  exp x − log 1  = exp x        depth 1
oneSubX   = eml (const 0) expVar           value  exp 0 − log(exp x) = 1 − x    depth 2
decayFast = eml oneSubX (const 0)          value  exp(1 − x) − log 0 = exp(1−x) depth 3
```

`decayFast` is **positive everywhere**, so the guard never protects it, and

```
-log (decayFast.eval x) = x − 1
```

which outruns `C + log x` for every `C`. `not_decay_on_ray_depth_three` proves it, taking
`x := exp y` for `y ≥ max (C+1) X₀` and closing with the unconditional `exp_gt_two_x`.

`decayFast_depth` is `by decide`: depth **exactly** 3, one rung above where `V₂` holds. `V₂` is
untouched.

## Why this is the interesting failure

Nothing exotic is involved. `log 0 = 0` makes `eml A (const 0)` compute `exp ∘ A`, and
`eml (const 0) (expTree var)` computes `1 − x`; composing the two gives a positive tree decaying like
`e·exp(−x)`. **Three nodes and the totalisation convention**, not asymptotic cancellation.

That also says where the statement went wrong. `V_j`'s right-hand side `C + log x` is a **log-scale**
bound — it says `t x ≥ e^{-C}/x`, i.e. no positive tree decays faster than a constant over `x`. That
is true through depth 2 and false at depth 3, because depth 3 is exactly where a tree can put a
*linear* function inside an `exp`.

## What survives, and the shape a repair would take

`decayFast` has `-log t x = x − 1`, which is comfortably inside a **tower-form** envelope. So the
natural repair is to let the decay bound grow with depth — `-log (t x) ≤ envelope k M x` rather than
`C + log x` — mirroring what `EMLGrowthEnvelope` already does on the growth side. Nothing here proves
such a form iterates; it is recorded as the shape the evidence points at, not as a result.

`TowerLowerBound` stays **open**, and no ledger row moves: `V_j` was never a ledger row, it is the
route the ledger's note describes. What changes is that the note's route is now known to be closed
off, which is worth more than another session spent trying to make it work.
-/

namespace MachLib

open Real

noncomputable def expVar : EMLTree := EMLTree.eml EMLTree.var (EMLTree.const 1)
noncomputable def oneSubX : EMLTree := EMLTree.eml (EMLTree.const 0) expVar
noncomputable def decayFast : EMLTree := EMLTree.eml oneSubX (EMLTree.const 0)

/-- Depth **exactly** 3 — one rung above where `V₂` is proved. -/
theorem decayFast_depth : decayFast.depth = 3 := by decide

theorem expVar_eval (x : Real) : expVar.eval x = exp x := by
  show exp x - log (1 : Real) = exp x
  rw [log_one]; mach_ring

theorem oneSubX_eval (x : Real) : oneSubX.eval x = 1 - x := by
  show exp (0 : Real) - log (expVar.eval x) = 1 - x
  rw [expVar_eval x, log_exp, exp_zero]

theorem decayFast_eval (x : Real) : decayFast.eval x = exp (1 - x) := by
  show exp (oneSubX.eval x) - log (0 : Real) = exp (1 - x)
  rw [oneSubX_eval x, log_nonpos (le_refl (0 : Real))]
  mach_ring

theorem decayFast_pos (x : Real) : 0 < decayFast.eval x := by
  rw [decayFast_eval x]; exact exp_pos _

/-- **V₃ is FALSE.** -/
theorem not_decay_on_ray_depth_three :
    ¬ ∃ C X₀ : Real, 1 ≤ X₀ ∧ ∀ x : Real, X₀ ≤ x → 0 < decayFast.eval x →
        -log (decayFast.eval x) ≤ C + log x := by
  rintro ⟨C, X₀, hX₀, h⟩
  -- pick y ≥ max (C+1) X₀, then x := exp y
  obtain ⟨y, hyC, hyX⟩ : ∃ y : Real, C + 1 ≤ y ∧ X₀ ≤ y :=
    ⟨MachLib.Real.max (C + 1) X₀, le_max_left _ _, le_max_right _ _⟩
  have hy0 : (0 : Real) < y := lt_of_lt_of_le (lt_of_lt_of_le zero_lt_one_ax hX₀) hyX
  have h2y : (1 + 1) * y < exp y := exp_gt_two_x y
  have hyy : y < exp y := by
    have e : (1 : Real) * y = y := by mach_ring
    have h11 : (1 : Real) ≤ 1 + 1 := by
      have w := add_lt_add_left zero_lt_one_ax 1
      have e0 : (1 : Real) + 0 = 1 := by mach_ring
      rw [e0] at w; exact le_of_lt w
    have hle : (1 : Real) * y ≤ (1 + 1) * y :=
      mul_le_mul_of_nonneg_right h11 (le_of_lt hy0)
    rw [e] at hle
    exact lt_of_le_of_lt hle h2y
  have hxX : X₀ ≤ exp y := le_trans hyX (le_of_lt hyy)
  have hb := h (exp y) hxX (decayFast_pos _)
  rw [decayFast_eval (exp y), log_exp, log_exp] at hb
  -- hb : -(1 - exp y) ≤ C + y
  have hb' : exp y - 1 ≤ C + y := by
    have e : -(1 - exp y) = exp y - 1 := by mach_ring
    rw [e] at hb; exact hb
  -- but exp y - 1 > C + y
  have hgt : C + y < exp y - 1 := by
    have s1 : C + y ≤ y - 1 + y := by
      have v := add_le_add_wit (by
        have w := add_le_add_wit hyC (le_refl (-(1 : Real)))
        have e1 : C + 1 + -(1 : Real) = C := by mach_ring
        have e2 : y + -(1 : Real) = y - 1 := by mach_ring
        rw [e1, e2] at w; exact w) (le_refl y)
      exact v
    have s2 : y - 1 + y < exp y - 1 := by
      have e : (1 + 1) * y = y + y := by mach_ring
      rw [e] at h2y
      have v := add_lt_add_left h2y (-(1 : Real))
      have e1 : -(1 : Real) + (y + y) = y - 1 + y := by mach_ring
      have e2 : -(1 : Real) + exp y = exp y - 1 := by mach_ring
      rw [e1, e2] at v; exact v
    exact lt_of_le_of_lt s1 s2
  exact lt_irrefl_ax _ (lt_of_le_of_lt hb' hgt)


end MachLib
