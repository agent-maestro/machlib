import MachLib.IterExpDepthNBudget5
import MachLib.IterExpDepthNBudgetMono

/-!
# Chain-N explicit bound — `budgetMax` (monotone-in-`D` upper bound on `budgetN5`) for the depth induction

Step-6 needs the per-poly `budgetN5 m D q` (degrees `≤ D`) bounded by a MONOTONE function of `D` alone, so the
depth-below `Ndep` can be evaluated at a `D`-only argument. `budgetMax m D` is that bound: `invPhiG` at
`degreeY_top := D` and `ir := descentBound (m+2) D` (the caps). `budgetN5 m D q ≤ budgetMax m D` via `invPhiG`'s
monotonicity in the level `d` (`degreeY_top ≤ D`) and inner rank `ir` (`rankRec_inner_lt`), and `budgetMax` is
monotone in `D`.
-/

namespace MachLib.IterExpDepthN

open MachLib.MultiPolyMod MachLib.MultiPolyMod.MultiPoly
open MachLib.ExplicitBound

/-- `invPhiG` monotone in the inner rank `ir`. -/
theorem invPhiG_mono_ir (cap : Nat → Nat) (hcap : ∀ {B B' : Nat}, B ≤ B' → cap B ≤ cap B')
    (Nleaf d B : Nat) {ir ir' : Nat} (h : ir ≤ ir') :
    invPhiG cap Nleaf d ir B ≤ invPhiG cap Nleaf d ir' B := by
  cases d with
  | zero => exact Nat.le_refl _
  | succ d =>
    show ir + levelBudgetG cap Nleaf d (B + ir + 1) ≤ ir' + levelBudgetG cap Nleaf d (B + ir' + 1)
    exact Nat.add_le_add h (levelBudgetG_mono_B cap hcap Nleaf d (by omega))

/-- `invPhiG` monotone in the level `d`. -/
theorem invPhiG_mono_d (cap : Nat → Nat) (hcap : ∀ {B B' : Nat}, B ≤ B' → cap B ≤ cap B')
    (Nleaf ir B : Nat) {d d' : Nat} (h : d ≤ d') :
    invPhiG cap Nleaf d ir B ≤ invPhiG cap Nleaf d' ir B := by
  cases d with
  | zero =>
    cases d' with
    | zero => exact Nat.le_refl _
    | succ e =>
      show Nleaf ≤ ir + levelBudgetG cap Nleaf e (B + ir + 1)
      exact Nat.le_trans (Nleaf_le_levelBudgetG cap Nleaf e (B + ir + 1)) (Nat.le_add_left _ _)
  | succ c =>
    cases d' with
    | zero => exact (Nat.not_succ_le_zero c h).elim
    | succ e =>
      show ir + levelBudgetG cap Nleaf c (B + ir + 1) ≤ ir + levelBudgetG cap Nleaf e (B + ir + 1)
      exact Nat.add_le_add_left (levelBudgetG_mono_d cap hcap Nleaf (B + ir + 1) (by omega)) ir

/-- The monotone-in-`D` budget cap: `invPhiG` at the `D`-caps. Computable — the whole `Ndep`
recurrence is closed-form `Nat` arithmetic (`#eval`-able, though the values are hyper-exponential
in the depth, so evaluating past a small depth overflows the interpreter stack). -/
def budgetMax (m D : Nat) : Nat :=
  invPhiG (descentBound (m + 2)) 0 D (descentBound (m + 2) D) D

/-- **`budgetN5 m D q ≤ budgetMax m D`** when `q`'s degrees are `≤ D`. -/
theorem budgetN5_le_budgetMax (m : Nat) (p : MultiPoly (m + 3)) (D : Nat)
    (hpx : MultiPoly.degreeX p + 2 ≤ D) (hpy : ∀ i : Fin (m + 3), MultiPoly.degreeY i p ≤ D) :
    budgetN5 m D p ≤ budgetMax m D := by
  unfold budgetN5 budgetMax
  refine Nat.le_trans
    (invPhiG_mono_ir (descentBound (m + 2)) (fun {_ _} h => descentBound_mono (m + 2) h) 0
      (MultiPoly.degreeY (⟨m + 2, by omega⟩ : Fin (m + 3)) p) D
      (Nat.le_of_lt (rankRec_inner_lt m p D hpx hpy)))
    (invPhiG_mono_d (descentBound (m + 2)) (fun {_ _} h => descentBound_mono (m + 2) h) 0
      (descentBound (m + 2) D) D (hpy _))

/-- `budgetMax m` is monotone in `D`. -/
theorem budgetMax_mono (m : Nat) {D D' : Nat} (h : D ≤ D') : budgetMax m D ≤ budgetMax m D' := by
  unfold budgetMax
  have hcap : ∀ {B B' : Nat}, B ≤ B' → descentBound (m + 2) B ≤ descentBound (m + 2) B' :=
    fun {_ _} hh => descentBound_mono (m + 2) hh
  exact Nat.le_trans (invPhiG_mono_d (descentBound (m + 2)) hcap 0 (descentBound (m + 2) D) D h)
    (Nat.le_trans (invPhiG_mono_ir (descentBound (m + 2)) hcap 0 D' D (descentBound_mono (m + 2) h))
      (invPhiG_mono_B (descentBound (m + 2)) hcap 0 D' (descentBound (m + 2) D') h))

end MachLib.IterExpDepthN
