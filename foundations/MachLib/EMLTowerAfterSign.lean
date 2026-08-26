import MachLib.EMLAnalyticDischarge
import MachLib.EMLCertifiedSynthesis

/-!
# What discharging `SignHardCase` did, and did not, do to the tower

Two consequences, both small, both worth stating so the ledger reads correctly.

## The two rows collapsed into one

`TowerReducesToSign` is literally `SignHardCase → TowerLowerBound`. With `signHardCase_holds` in
hand its antecedent is a theorem, so it is now **equivalent** to `TowerLowerBound`
(`towerReducesToSign_iff_towerLowerBound`). Two ledger rows that looked like separate debts are one
debt stated twice.

Stated as an `Iff` on purpose: a theorem whose bare conclusion is `TowerLowerBound` would read to
`obligation_ledger_check.dischargers_of` as an unconditional discharge of an open row, which is the
shape canary 5 exists to catch. The equivalence is the honest form and the gate skips it.

## The crossing obstruction is gone from `V_j`'s shape

`depth_le_two_decay_on_ray` reads

```
∃ C X₀, 1 ≤ X₀ ∧ ∀ x ≥ X₀, 0 < t.eval x → -log (t.eval x) ≤ C + log x
```

and the guard is not decoration. Near a zero crossing from above `t → 0⁺`, so `-log t → +∞` and no
fixed `C` survives; the statement is rescued only by pushing `X₀` past the last crossing. That —
finiteness of sign changes — was recorded as the *binding* obstruction to an all-depth theory.

`evSign_all` supplies it at every depth, unconditionally, and
`decay_on_ray_of_positive_ray` cashes it: past the sign ray either the tree is **uniformly positive**
(no crossings to push past) or the guard is **never satisfied** (the statement is vacuous there). So
the guarded form follows from the unguarded form on a positivity ray, for **every** tree at **every**
depth, with no classification and no hand analysis.

## What that does *not* buy

The **rate**. `V_j` is quantitative — `-log t x ≤ C + log x` — and sign-definiteness supplies the ray,
not the bound. At depth ≤ 2 the rate comes from the depth-≤1 classification, by hand; for general `j`
there is still no classification and nothing here supplies one.

So `TowerLowerBound` stays open, and the honest summary is that one of the two ingredients `V_j`
needs is now free while the other is untouched. `EMLCertifiedSynthesis`'s own note that the reduction
"is not a formality" remains correct — this narrows it, it does not close it.
-/

namespace MachLib

open Real

/-- **The two obligations are one.** `SignHardCase` is a theorem, so `TowerReducesToSign` — which is
`SignHardCase → TowerLowerBound` — says exactly `TowerLowerBound`.

An `Iff` rather than two implications so the obligation gate does not read it as a discharge. -/
theorem towerReducesToSign_iff_towerLowerBound :
    EMLTree.TowerReducesToSign ↔ EMLTree.TowerLowerBound := by
  unfold EMLTree.TowerReducesToSign
  exact ⟨fun h => h signHardCase_holds, fun h _ => h⟩

/-- **The crossing obstruction, discharged.** The guarded decay statement follows from the unguarded
one on a positivity ray — for every tree, at every depth.

Both branches of `evSign_all` are used: on the positive branch the hypothesis applies with no
crossings to avoid, and on the non-positive branch the guard `0 < t.eval x` is unsatisfiable, so the
conclusion holds vacuously with any constant. -/
theorem decay_on_ray_of_positive_ray (t : EMLTree)
    (h : ∀ X : Real, 1 ≤ X → (∀ x : Real, X ≤ x → 0 < t.eval x) →
           ∃ C X₀ : Real, 1 ≤ X₀ ∧ X ≤ X₀ ∧
             ∀ x : Real, X₀ ≤ x → -log (t.eval x) ≤ C + log x) :
    ∃ C X₀ : Real, 1 ≤ X₀ ∧ ∀ x : Real, X₀ ≤ x → 0 < t.eval x →
      -log (t.eval x) ≤ C + log x := by
  rcases evSign_all t with ⟨X, hX1, hpos⟩ | ⟨X, hX1, hnp⟩
  · obtain ⟨C, X₀, hX01, _, hbound⟩ := h X hX1 hpos
    exact ⟨C, X₀, hX01, fun x hx _ => hbound x hx⟩
  · refine ⟨0, X, hX1, fun x hx hgt => ?_⟩
    exact absurd (hnp x hx) (fun hle => (ne_of_lt (lt_of_lt_of_le hgt hle)) rfl)

/-- **Discrimination.** The hypothesis of `decay_on_ray_of_positive_ray` is satisfiable: `var` is
positive on every ray from `1`, and `-log x ≤ 0 + log x` there. So the reduction is not vacuous. -/
theorem decay_on_ray_specimen :
    ∃ C X₀ : Real, 1 ≤ X₀ ∧ ∀ x : Real, X₀ ≤ x → 0 < (EMLTree.var).eval x →
      -log ((EMLTree.var).eval x) ≤ C + log x := by
  refine decay_on_ray_of_positive_ray EMLTree.var (fun X hX1 _ => ⟨0, X, hX1, le_refl X, ?_⟩)
  intro x hx
  have hx1 : (1 : Real) ≤ x := le_trans hX1 hx
  have hlog : (0 : Real) ≤ log x := by
    have hl1 : log (1 : Real) = 0 := by
      have hz : exp (0 : Real) = 1 := exp_zero
      rw [← hz, log_exp]
    have hm := log_le_log zero_lt_one_ax hx1
    rw [hl1] at hm; exact hm
  show -log x ≤ 0 + log x
  have v := add_le_add_wit hlog hlog
  have e1 : (0 : Real) + 0 = 0 := by mach_ring
  rw [e1] at v
  have w := add_le_add_wit (le_refl (-log x)) v
  have e2 : -log x + 0 = -log x := by mach_ring
  have e3 : -log x + (log x + log x) = log x := by mach_ring
  rw [e2, e3] at w
  have e4 : (0 : Real) + log x = log x := by mach_ring
  rw [e4]; exact w

end MachLib
