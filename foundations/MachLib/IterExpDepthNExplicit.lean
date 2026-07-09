import MachLib.IterExpDepthNStepExplicit
import MachLib.IterExpDepthNBudgetMax
import MachLib.ChainExp2ExplicitInvPhiMono
import MachLib.ChainExp2ExplicitTool

/-!
# The arbitrary-depth EXPLICIT (quantitative) Khovanskii bound

`chainN_khovanskii_bound_explicit` — for every depth `m` and every chain-`(m+2)` polynomial `p` whose syntactic
degrees are `≤ D`, the number of zeros of `chainNFn (m+2) p` on any interval where it is not identically zero is
`≤ Ndep m D`, an EXPLICIT natural-number ceiling built from the kernel's degree bound `D` alone.

`Ndep` is defined by recursion on depth:
* `Ndep 0 D = invPhi (D+2) D (D·(D+3)+(D+2)) D` — the chain-2 tool `khovBound` maximised over degrees `≤ D`.
* `Ndep (m+1) D = budgetMax m (D+2) + Ndep m ((D+2) + budgetMax m (D+2))` — the outer reduce budget
  (`budgetMax`, the monotone cap on `budgetN5`) plus the depth-below leaf evaluated at the grown argument.

The proof is the outer depth induction: base = `chain2_khovanskii_bound_syntactic` bounded by `khovBound_le_Ndep0`;
step = `chainN_bound_step_explicit` (the WF reduce/trim/lift recursion) with `budgetN5 ≤ budgetMax` and `Ndep m`
monotone. Everything is `#print axioms`-clean of `zero_count_bound_classical` (it never enters this arc).
-/

namespace MachLib.IterExpDepthN

open MachLib.MultiPolyMod MachLib.MultiPolyMod.MultiPoly
open MachLib.ExplicitBound
open MachLib.ChainExp2NoZeros

/-- The explicit depth-indexed zero-count ceiling. `Ndep m D` bounds `chainNFn (m+2) q` for every `q` with
degrees `≤ D`. -/
noncomputable def Ndep : Nat → Nat → Nat
  | 0,     D => invPhi (D + 2) D (D * (D + 3) + (D + 2)) D
  | m + 1, D => budgetMax m (D + 2) + Ndep m ((D + 2) + budgetMax m (D + 2))

/-- `Ndep m` is monotone in the degree bound `D`. -/
theorem Ndep_mono : ∀ (m : Nat) {D D' : Nat}, D ≤ D' → Ndep m D ≤ Ndep m D' := by
  intro m
  induction m with
  | zero =>
    intro D D' h
    show invPhi (D + 2) D (D * (D + 3) + (D + 2)) D
        ≤ invPhi (D' + 2) D' (D' * (D' + 3) + (D' + 2)) D'
    refine Nat.le_trans (invPhi_mono_B _ _ _ (show D + 2 ≤ D' + 2 by omega)) ?_
    refine Nat.le_trans (invPhi_mono_d _ _ _ h) ?_
    refine Nat.le_trans (invPhi_mono_ir _ _ _ ?_) (invPhi_mono_g _ _ _ h)
    have hmul : D * (D + 3) ≤ D' * (D' + 3) := Nat.mul_le_mul h (by omega)
    omega
  | succ m ih =>
    intro D D' h
    show budgetMax m (D + 2) + Ndep m ((D + 2) + budgetMax m (D + 2))
        ≤ budgetMax m (D' + 2) + Ndep m ((D' + 2) + budgetMax m (D' + 2))
    have hbm : budgetMax m (D + 2) ≤ budgetMax m (D' + 2) := budgetMax_mono m (by omega)
    exact Nat.add_le_add hbm (ih (Nat.add_le_add (by omega) hbm))

/-- **Base bound.** The chain-2 tool `khovBound q` is dominated by `Ndep 0 D` when `q`'s degrees are `≤ D`
(monotonicity of `invPhi` in all four arguments). -/
theorem khovBound_le_Ndep0 (p : MultiPoly 2) (D : Nat)
    (hx : MultiPoly.degreeX p ≤ D) (hy : ∀ i : Fin 2, MultiPoly.degreeY i p ≤ D) :
    khovBound p ≤ Ndep 0 D := by
  show khovBound p ≤ invPhi (D + 2) D (D * (D + 3) + (D + 2)) D
  unfold khovBound
  have hy0 : MultiPoly.degreeY (⟨0, by omega⟩ : Fin 2) p ≤ D := hy _
  have hy1 : MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) p ≤ D := hy _
  refine Nat.le_trans (invPhi_mono_B _ _ _ (show MultiPoly.degreeX p + 2 ≤ D + 2 by omega)) ?_
  refine Nat.le_trans (invPhi_mono_d _ _ _ hy1) ?_
  refine Nat.le_trans (invPhi_mono_ir _ _ _ ?_) (invPhi_mono_g _ _ _ hy0)
  have hmul : MultiPoly.degreeY (⟨0, by omega⟩ : Fin 2) p * (MultiPoly.degreeX p + 2 + 1)
      ≤ D * (D + 3) := Nat.mul_le_mul hy0 (by omega)
  omega

/-- **The arbitrary-depth explicit Khovanskii bound.** For every depth `m`, chain-`(m+2)` polynomial `p` with
degrees `≤ D`, and interval `(a,b)` on which `chainNFn (m+2) p` is not identically zero, the zero count is
`≤ Ndep m D`. Outer induction on depth: base = chain-2 tool; step = `chainN_bound_step_explicit`. -/
theorem chainN_khovanskii_bound_explicit :
    ∀ (m : Nat) (p : MultiPoly (m + 2)) (D : Nat) (a b : Real), a < b →
      MultiPoly.degreeX p ≤ D → (∀ i : Fin (m + 2), MultiPoly.degreeY i p ≤ D) →
      (∃ z, a < z ∧ z < b ∧ (chainNFn (m + 2) p).eval z ≠ 0) →
      ∀ zeros : List Real, zeros.Nodup →
        (∀ z ∈ zeros, a < z ∧ z < b ∧ (chainNFn (m + 2) p).eval z = 0) → zeros.length ≤ Ndep m D := by
  intro m
  induction m with
  | zero =>
    intro p D a b hab hx hy hne zeros hnd hz
    exact Nat.le_trans (chain2_khovanskii_bound_syntactic p a b hab hne zeros hnd hz)
      (khovBound_le_Ndep0 p D hx hy)
  | succ m ih =>
    intro p D a b hab hx hy hne zeros hnd hz
    have hstep := chainN_bound_step_explicit m (Ndep m) (fun {_ _} h => Ndep_mono m h) ih p a b hab
      (D + 2) (by omega) (fun i => Nat.le_trans (hy i) (by omega)) hne zeros hnd hz
    refine Nat.le_trans hstep ?_
    show budgetN5 m (D + 2) p + Ndep m ((D + 2) + budgetN5 m (D + 2) p)
        ≤ budgetMax m (D + 2) + Ndep m ((D + 2) + budgetMax m (D + 2))
    have hb : budgetN5 m (D + 2) p ≤ budgetMax m (D + 2) :=
      budgetN5_le_budgetMax m p (D + 2) (by omega) (fun i => Nat.le_trans (hy i) (by omega))
    exact Nat.add_le_add hb (Ndep_mono m (Nat.add_le_add_left hb (D + 2)))

end MachLib.IterExpDepthN
