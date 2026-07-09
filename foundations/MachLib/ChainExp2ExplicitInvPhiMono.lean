import MachLib.ChainExp2ExplicitLevelBudget

/-!
# Chain-2 explicit bound — full monotonicity of `invPhi` (all four arguments)

`ChainExp2ExplicitLevelBudget` proves `invPhi_mono_ir` (and `levelBudget_mono_G`/`_d`). The depth induction
needs `invPhi` monotone in ALL of `B`, `d`, `g`, `ir` — because the base case `Ndep 0 D = invPhi (D+2) D … D`
must dominate `khovBound q` for every `q` whose degrees are `≤ D`, and must itself be monotone in `D`. This
file supplies the missing three: `levelBudget_mono_B`, then `invPhi_mono_B`, `invPhi_mono_d`, `invPhi_mono_g`.
-/

namespace MachLib.ExplicitBound

/-- **`levelBudget` monotone in the x-degree budget `B`.** A larger `B` enlarges each per-level block
`(G+1)(B+1)` and every recursive `G`-argument, so the whole budget grows. -/
theorem levelBudget_mono_B :
    ∀ (d : Nat) {B B' : Nat}, B ≤ B' → ∀ (G : Nat), levelBudget B d G ≤ levelBudget B' d G
  | 0, B, B', h, G => by
      show (G + 1) * (B + 1) ≤ (G + 1) * (B' + 1)
      exact Nat.mul_le_mul (Nat.le_refl _) (Nat.add_le_add_right h 1)
  | d + 1, B, B', h, G => by
      show (G + 1) * (B + 1) + levelBudget B d (G + (G + 1) * (B + 1))
          ≤ (G + 1) * (B' + 1) + levelBudget B' d (G + (G + 1) * (B' + 1))
      have hmul : (G + 1) * (B + 1) ≤ (G + 1) * (B' + 1) :=
        Nat.mul_le_mul (Nat.le_refl _) (Nat.add_le_add_right h 1)
      refine Nat.add_le_add hmul (Nat.le_trans (levelBudget_mono_B d h _) ?_)
      exact levelBudget_mono_G B' d (Nat.add_le_add_left hmul G)

/-- `invPhi` monotone in the x-degree budget `B`. -/
theorem invPhi_mono_B (d ir g : Nat) {B B' : Nat} (h : B ≤ B') :
    invPhi B d ir g ≤ invPhi B' d ir g := by
  cases d with
  | zero => exact Nat.le_refl _
  | succ d =>
    show ir + levelBudget B d (g + ir + 1) ≤ ir + levelBudget B' d (g + ir + 1)
    exact Nat.add_le_add_left (levelBudget_mono_B d h _) ir

/-- `invPhi` monotone in the `degreeY₁` level `d`. -/
theorem invPhi_mono_d (B ir g : Nat) {d d' : Nat} (h : d ≤ d') :
    invPhi B d ir g ≤ invPhi B d' ir g := by
  cases d with
  | zero =>
    cases d' with
    | zero => exact Nat.le_refl _
    | succ e => exact Nat.le_add_right _ _
  | succ c =>
    cases d' with
    | zero => exact (Nat.not_succ_le_zero c h).elim
    | succ e =>
      show ir + levelBudget B c (g + ir + 1) ≤ ir + levelBudget B e (g + ir + 1)
      exact Nat.add_le_add_left (levelBudget_mono_d B _ (by omega)) ir

/-- `invPhi` monotone in the `degreeY₀` budget `g`. -/
theorem invPhi_mono_g (B d ir : Nat) {g g' : Nat} (h : g ≤ g') :
    invPhi B d ir g ≤ invPhi B d ir g' := by
  cases d with
  | zero => exact Nat.le_refl _
  | succ d =>
    show ir + levelBudget B d (g + ir + 1) ≤ ir + levelBudget B d (g' + ir + 1)
    exact Nat.add_le_add_left (levelBudget_mono_G B d (by omega)) ir

end MachLib.ExplicitBound
