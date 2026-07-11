import MachLib.PfaffianGeneralStepExplicit
import MachLib.PfaffianGeneralBudgetMaxA
import MachLib.PfaffianGeneralBase2Explicit

/-!
# The arbitrary-depth EXPLICIT (quantitative) Khovanskii bound for general exp-type Pfaffian chains

`pfaffian_khovanskii_bound_gen_explicit` — for every depth `M`, every positive-coherent exp-type
Pfaffian chain of format `D` (all relation degrees `≤ D`), and every polynomial `p` of syntactic degree
`≤ Dq`, the number of zeros of `pfaffianChainFn c p` on any interval where it is not identically zero is
`≤ NgenA D M Dq`, an EXPLICIT `Nat` ceiling built from the format `D` and the degree `Dq` alone.

This is the general-chain analog of `chainN_khovanskii_bound_explicit`. `NgenA` mirrors the closed
build's `Ndep`, with the α-format machinery in place of the tower's `α = 1`:
* `NgenA D 0 Dq = descentBoundA (D+1) 2 (Dq+2)` — the chain-2 tool `Ngen2` capped over format `≤ D`,
  degrees `≤ Dq` (`Ngen2_le_descentBoundA`).
* `NgenA D (m+1) Dq = budgetMaxA D m (Dq+2) + NgenA D m ((Dq+2) + budgetMaxA D m (Dq+2))` — the outer
  reduce budget cap (`budgetMaxA`, monotone bound on `budgetN5A`) plus the depth-below leaf at the grown
  argument.

Outer depth induction: base = `pfaffian_bound2_gen_explicit` capped by `Ngen2_le_descentBoundA`; step =
`pfaffian_bound_step_explicit` (the α-budget M5⁺ recursion) with `budgetN5A ≤ budgetMaxA` and `NgenA D m`
monotone. `rolle_ct` remains the sole analytic axiom.
-/

namespace MachLib.PfaffianGeneralReduce

open MachLib.Real
open MachLib.MultiPolyMod MachLib.MultiPolyMod.MultiPoly MachLib.PfaffianChainMod
open MachLib.PfaffianChainMod.PfaffianFn MachLib.IterExpDepthN
open MachLib.PfaffianGeneralVehExpo MachLib.ChainExp2CanonMeasure

/-! ## `descentBoundA` monotone in the format `α` -/

/-- **`dLevelA` monotone jointly in the inner function and the format `α`.** If `inner ≤ inner'`
pointwise (with `inner'` `B`-monotone) and `α ≤ α'`, then `dLevelA inner α d B ≤ dLevelA inner' α' d B`.
The joint step `descentBoundA_mono_α` needs at each level. -/
theorem dLevelA_mono_inner_α (inner inner' : Nat → Nat)
    (hmono' : ∀ {B B' : Nat}, B ≤ B' → inner' B ≤ inner' B')
    (hpt : ∀ B, inner B ≤ inner' B) {α α' : Nat} (hα : α ≤ α') :
    ∀ (d B : Nat), dLevelA inner α d B ≤ dLevelA inner' α' d B
  | 0, B => hpt B
  | d + 1, B => by
      show inner B + dLevelA inner α d (B + inner B + α)
         ≤ inner' B + dLevelA inner' α' d (B + inner' B + α')
      refine Nat.add_le_add (hpt B) ?_
      refine Nat.le_trans (dLevelA_mono_inner_α inner inner' hmono' hpt hα d (B + inner B + α)) ?_
      exact dLevelA_mono_B inner' hmono' α' d (by have := hpt B; omega)

/-- **`descentBoundA α n` is monotone in the format `α`.** By induction on depth `n`: the base scales
`α·(B+1)`, the step is `dLevelA_mono_inner_α` with the inner descent's IH. -/
theorem descentBoundA_mono_α :
    ∀ (n : Nat) {α α' : Nat}, α ≤ α' → ∀ (B : Nat), descentBoundA α n B ≤ descentBoundA α' n B
  | 0, α, α', hα, B => by
      show α * (B + 1) ≤ α' * (B + 1)
      exact Nat.mul_le_mul hα (Nat.le_refl _)
  | n + 1, α, α', hα, B => by
      show dLevelA (descentBoundA α n) α B B ≤ dLevelA (descentBoundA α' n) α' B B
      exact dLevelA_mono_inner_α (descentBoundA α n) (descentBoundA α' n)
        (fun {_ _} h => descentBoundA_mono α' n h)
        (fun B' => descentBoundA_mono_α n hα B') hα B B

/-! ## The chain-2 base cap -/

/-- **`Ngen2` is capped by a format/degree-only ceiling.** For a chain of format `≤ D` and a polynomial
of degree `≤ Dq`, `Ngen2 c2 q ≤ descentBoundA (D+1) 2 (Dq+2)`. Combines `rankRecA_lt_descentBoundA` (the
measure fits under `Bcap2`) with the two caps `α2 c2 ≤ D+1` and `Bcap2 q ≤ Dq+2`. -/
theorem Ngen2_le_descentBoundA (c2 : PfaffianChain 2) (q : MultiPoly 2) (D : Nat)
    (hfmtX : ∀ i : Fin 2, MultiPoly.degreeX (c2.relations i) ≤ D)
    (hfmtY : ∀ i j : Fin 2, MultiPoly.degreeY j (c2.relations i) ≤ D)
    (Dq : Nat) (hqx : MultiPoly.degreeX q ≤ Dq) (hqy : ∀ i : Fin 2, MultiPoly.degreeY i q ≤ Dq) :
    Ngen2 c2 q ≤ descentBoundA (D + 1) 2 (Dq + 2) := by
  have hα2 : α2 c2 ≤ D + 1 := by
    unfold α2
    refine Nat.add_le_add_right (Nat.max_le.mpr ⟨Nat.max_le.mpr ⟨?_, ?_⟩, ?_⟩) 1
    · unfold formatX2; exact Nat.max_le.mpr ⟨hfmtX _, hfmtX _⟩
    · unfold formatY2; exact Nat.max_le.mpr ⟨hfmtY _ _, hfmtY _ _⟩
    · unfold formatY2; exact Nat.max_le.mpr ⟨hfmtY _ _, hfmtY _ _⟩
  have hbcap : Bcap2 q ≤ Dq + 2 := by
    unfold Bcap2
    exact Nat.add_le_add_right (Nat.max_le.mpr ⟨Nat.max_le.mpr ⟨hqy _, hqy _⟩, hqx⟩) 2
  have hlt : Ngen2 c2 q < descentBoundA (α2 c2) 2 (Bcap2 q) := by
    unfold Ngen2
    exact rankRecA_lt_descentBoundA (α2 c2) 2 (Bcap2 q) (chain2MeasureCanon q)
      (one_le_α2 c2) (measure_le_Bcap2 q)
  calc Ngen2 c2 q ≤ descentBoundA (α2 c2) 2 (Bcap2 q) := Nat.le_of_lt hlt
    _ ≤ descentBoundA (α2 c2) 2 (Dq + 2) := descentBoundA_mono (α2 c2) 2 hbcap
    _ ≤ descentBoundA (D + 1) 2 (Dq + 2) := descentBoundA_mono_α 2 hα2 (Dq + 2)

/-! ## The explicit depth-indexed ceiling `NgenA` -/

/-- The explicit depth-indexed zero-count ceiling for format-`D` chains. `NgenA D M Dq` bounds
`pfaffianChainFn c p` for every format-`D` depth-`(M+2)` chain `c` and every `p` with degrees `≤ Dq`.
Computable closed-form `Nat` recurrence (the values are a height-`M` tower, so evaluation past a small
depth overflows the interpreter). -/
def NgenA (D : Nat) : Nat → Nat → Nat
  | 0,     Dq => descentBoundA (D + 1) 2 (Dq + 2)
  | m + 1, Dq => budgetMaxA D m (Dq + 2) + NgenA D m ((Dq + 2) + budgetMaxA D m (Dq + 2))

/-- `NgenA D m` is monotone in the degree bound `Dq`. -/
theorem NgenA_mono (D : Nat) :
    ∀ (m : Nat) {Dq Dq' : Nat}, Dq ≤ Dq' → NgenA D m Dq ≤ NgenA D m Dq' := by
  intro m
  induction m with
  | zero =>
    intro Dq Dq' h
    show descentBoundA (D + 1) 2 (Dq + 2) ≤ descentBoundA (D + 1) 2 (Dq' + 2)
    exact descentBoundA_mono (D + 1) 2 (by omega)
  | succ m ih =>
    intro Dq Dq' h
    show budgetMaxA D m (Dq + 2) + NgenA D m ((Dq + 2) + budgetMaxA D m (Dq + 2))
        ≤ budgetMaxA D m (Dq' + 2) + NgenA D m ((Dq' + 2) + budgetMaxA D m (Dq' + 2))
    have hbm : budgetMaxA D m (Dq + 2) ≤ budgetMaxA D m (Dq' + 2) := budgetMaxA_mono D m (by omega)
    exact Nat.add_le_add hbm (ih (Nat.add_le_add (by omega) hbm))

/-! ## The arbitrary-depth explicit bound -/

set_option maxHeartbeats 1000000 in
/-- **THE arbitrary-depth explicit Khovanskii bound for positive-coherent exp-type Pfaffian chains.**
For every depth `M`, format-`D` positive-coherent exp-chain `c`, and polynomial `p` of degree `≤ Dq`
non-vanishing somewhere on `(a,b)`, the zero count on `(a,b)` is `≤ NgenA D M Dq` — an explicit ceiling
in the format `D` and degree `Dq` alone. Outer induction on depth: base = the chain-2 tool
(`pfaffian_bound2_gen_explicit`) capped by `Ngen2_le_descentBoundA`; step = `pfaffian_bound_step_explicit`
with `budgetN5A ≤ budgetMaxA` and `NgenA D m` monotone. `rolle_ct` is the sole analytic axiom. -/
theorem pfaffian_khovanskii_bound_gen_explicit (D : Nat) (hD : 1 ≤ D) (a b : Real) (hab : a < b) :
    ∀ (M : Nat) (c : PfaffianChain (M + 2)), IsExpChain c → c.IsCoherentOn a b →
      (∀ z, a < z → z < b → ∀ i : Fin (M + 2), 0 < c.evals i z) →
      (∀ i : Fin (M + 2), MultiPoly.degreeX (c.relations i) ≤ D) →
      (∀ i j : Fin (M + 2), MultiPoly.degreeY j (c.relations i) ≤ D) →
      ∀ (p : MultiPoly (M + 2)) (Dq : Nat),
        MultiPoly.degreeX p ≤ Dq → (∀ i : Fin (M + 2), MultiPoly.degreeY i p ≤ Dq) →
        (∃ z, a < z ∧ z < b ∧ (pfaffianChainFn c p).eval z ≠ 0) →
        ∀ zeros : List Real, zeros.Nodup →
          (∀ z ∈ zeros, a < z ∧ z < b ∧ (pfaffianChainFn c p).eval z = 0) →
          zeros.length ≤ NgenA D M Dq := by
  intro M
  induction M with
  | zero =>
    intro c hexp hcoh hposit hfmtX hfmtY p Dq hpx hpy hne zeros hnd hz
    exact Nat.le_trans
      (pfaffian_bound2_gen_explicit c hexp a b hab hcoh hposit p hne zeros hnd hz)
      (Ngen2_le_descentBoundA c p D hfmtX hfmtY Dq hpx hpy)
  | succ M ih =>
    intro c hexp hcoh hposit hfmtX hfmtY p Dq hpx hpy hne zeros hnd hz
    have hstep := pfaffian_bound_step_explicit c hexp a b hab hcoh hposit D hD hfmtX hfmtY
      (NgenA D M) (fun {_ _} h => NgenA_mono D M h)
      (fun q Dq' hqx hqy hne' zeros' hnd' hz' =>
        ih (chainRestrict c) (IsExpChain_chainRestrict c hexp)
          (chainRestrict_isCoherentOn c hexp a b hcoh) (positivity_chainRestrict c a b hposit)
          (degreeX_chainRestrict_relations_le c D hfmtX)
          (degreeY_chainRestrict_relations_le c D hfmtY)
          q Dq' hqx hqy hne' zeros' hnd' hz')
      p (Dq + 2) (by omega) (fun i => Nat.le_trans (hpy i) (by omega)) hne zeros hnd hz
    refine Nat.le_trans hstep ?_
    show budgetN5A D M (Dq + 2) p + NgenA D M ((Dq + 2) + budgetN5A D M (Dq + 2) p)
        ≤ budgetMaxA D M (Dq + 2) + NgenA D M ((Dq + 2) + budgetMaxA D M (Dq + 2))
    have hb : budgetN5A D M (Dq + 2) p ≤ budgetMaxA D M (Dq + 2) :=
      budgetN5A_le_budgetMaxA D M hD p (Dq + 2) (by omega) (fun i => Nat.le_trans (hpy i) (by omega))
    exact Nat.add_le_add hb (NgenA_mono D M (Nat.add_le_add_left hb (Dq + 2)))

end MachLib.PfaffianGeneralReduce
