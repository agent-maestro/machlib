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


/-! ## §2 — the rate grows with depth, so no fixed bound can work

`V₃` fails against a **linear** `-log`. The obvious repair is to allow a bigger right-hand side. This
section shows the repair cannot be a *fixed* one: one rung further, the linear form fails too.

```
expXplus1  = eml var (const (exp (-1)))   exp x − log(exp(−1)) = exp x + 1        depth 1
expExpX1   = eml expXplus1 (const 1)      exp(exp x + 1) − log 1                  depth 2
negExpX    = eml (const 0) expExpX1       1 − (exp x + 1) = −exp x                depth 3
decayFaster= eml negExpX (const 0)        exp(−exp x) − log 0                     depth 4
```

`-log (decayFaster.eval x) = exp x`, so `not_linear_decay_bound_depth_four` rules out every
`C + x`. And `decayFast_linear_bound` shows the depth-3 witness **does** satisfy that bound, with
`C = 0`. So this is a genuine **separation between depth 3 and depth 4**, not just another failure.

The pattern is visible in the construction: each extra `eml` node buys one more `exp` in the decay
exponent, because `log 0 = 0` turns `eml A (const 0)` into `exp ∘ A` and `eml (const 0) (expTree s)`
into `−s`. So the decay rate at depth `j` is a tower of height growing with `j`.

**Consequence for the repair.** Any correct `V_j` must be **depth-indexed** — `-log (t x) ≤ E_{f(j)}(x)`
with the height growing in `j`, not a single envelope serving all depths. That is a sharper
requirement than `(de)` recorded, and it is what the two witnesses jointly establish. Whether such a
depth-indexed form actually iterates is still not proved here.
-/

-- exp x + 1, depth 1:  exp x - log (exp (-1)) = exp x + 1
noncomputable def expXplus1 : EMLTree := EMLTree.eml EMLTree.var (EMLTree.const (exp (-1)))
-- exp (exp x + 1), depth 2
noncomputable def expExpX1 : EMLTree := EMLTree.eml expXplus1 (EMLTree.const 1)
-- -exp x, depth 3:  exp 0 - log (exp (exp x + 1)) = 1 - (exp x + 1)
noncomputable def negExpX : EMLTree := EMLTree.eml (EMLTree.const 0) expExpX1
-- exp (-exp x), depth 4
noncomputable def decayFaster : EMLTree := EMLTree.eml negExpX (EMLTree.const 0)

theorem decayFaster_depth : decayFaster.depth = 4 := by decide

theorem expXplus1_eval (x : Real) : expXplus1.eval x = exp x + 1 := by
  show exp x - log (exp (-1 : Real)) = exp x + 1
  rw [log_exp]; mach_ring

theorem expExpX1_eval (x : Real) : expExpX1.eval x = exp (exp x + 1) := by
  show exp (expXplus1.eval x) - log (1 : Real) = exp (exp x + 1)
  rw [expXplus1_eval x, log_one]; mach_ring

theorem negExpX_eval (x : Real) : negExpX.eval x = -exp x := by
  show exp (0 : Real) - log (expExpX1.eval x) = -exp x
  rw [expExpX1_eval x, log_exp, exp_zero]; mach_ring

theorem decayFaster_eval (x : Real) : decayFaster.eval x = exp (-exp x) := by
  show exp (negExpX.eval x) - log (0 : Real) = exp (-exp x)
  rw [negExpX_eval x, log_nonpos (le_refl (0 : Real))]; mach_ring

theorem decayFaster_pos (x : Real) : 0 < decayFaster.eval x := by
  rw [decayFaster_eval x]; exact exp_pos _

/-- **Not even a linear bound survives at depth 4.** -/
theorem not_linear_decay_bound_depth_four :
    ¬ ∃ C X₀ : Real, 1 ≤ X₀ ∧ ∀ x : Real, X₀ ≤ x → 0 < decayFaster.eval x →
        -log (decayFaster.eval x) ≤ C + x := by
  rintro ⟨C, X₀, hX₀, h⟩
  obtain ⟨x, hxX, hxC⟩ : ∃ x : Real, X₀ ≤ x ∧ C < x :=
    ⟨MachLib.Real.max X₀ (C + 1), le_max_left _ _,
      lt_of_lt_of_le (by
        have v := add_lt_add_left zero_lt_one_ax C
        have e : C + 0 = C := by mach_ring
        rw [e] at v; exact v) (le_max_right X₀ (C + 1))⟩
  have hb := h x hxX (decayFaster_pos x)
  rw [decayFaster_eval x, log_exp] at hb
  -- hb : -(-exp x) ≤ C + x
  have hb' : exp x ≤ C + x := by
    have e : -(-exp x) = exp x := by mach_ring
    rw [e] at hb; exact hb
  have h2 : (1 + 1) * x < exp x := exp_gt_two_x x
  have hlt : C + x < exp x := by
    have e : (1 + 1) * x = x + x := by mach_ring
    rw [e] at h2
    have hCx : C + x < x + x := by
      have v := add_lt_add_left hxC x
      have e1 : x + C = C + x := by mach_ring
      have e2 : x + x = x + x := by mach_ring
      rw [e1] at v; exact v
    exact lt_trans_ax hCx h2
  exact lt_irrefl_ax _ (lt_of_le_of_lt hb' hlt)

/-- Depth 3's witness DOES satisfy the linear bound — so this is a genuine separation. -/
theorem decayFast_linear_bound :
    ∃ C X₀ : Real, 1 ≤ X₀ ∧ ∀ x : Real, X₀ ≤ x → 0 < decayFast.eval x →
      -log (decayFast.eval x) ≤ C + x := by
  refine ⟨0, 1, le_refl 1, fun x _ _ => ?_⟩
  rw [decayFast_eval x, log_exp]
  have e : -(1 - x) = x - 1 := by mach_ring
  rw [e]
  have v := add_lt_add_left zero_lt_one_ax (x - 1)
  have e1 : x - 1 + 0 = x - 1 := by mach_ring
  have e2 : x - 1 + 1 = x := by mach_ring
  rw [e1, e2] at v
  have e3 : (0 : Real) + x = x := by mach_ring
  rw [e3]; exact le_of_lt v


end MachLib
