import MachLib.IterExpDepth3Descent
import MachLib.ChainExp2NoZeros

/-!
# The MP3 → MP2 bridge: dropping `y₂` from `y₂`-free depth-3 polys

The key to depth-3 termination. A `y₂`-free `MultiPoly 3` (a poly in `x, y₀, y₁`) projects via the
framework's `MultiPoly.dropLastY : MultiPoly 3 → MultiPoly 2`, and — crucially — the projection is
eval-preserving across the chains: `eval q [IterExpChain 3] = eval (dropLastY q) [IterExpChain 2]`,
because both chains agree on `y₀ = eˣ`, `y₁ = e^{eˣ}` and `q` ignores `y₂`.

This lets the depth-3 inner measure be `chain2MeasureCanon (dropLastY (lcY₂ p))` — a genuine depth-2
canonical measure on the dropped leading coefficient — so the proven depth-2 descent transfers instead
of re-deriving the whole canonical-measure apparatus at depth 3. Path B; no `sorry`.
-/

namespace MachLib.IterExpDepth3Bridge

open MachLib.Real
open MachLib.MultiPolyMod
open MachLib.PfaffianChainMod
open MachLib.PfaffianChainMod.PfaffianFn
open MachLib.IterExpChainMod

/-- The restricted chain values of `IterExpChain 3` (first two slots) are exactly `IterExpChain 2`'s. -/
theorem chainValues3_restrict_eq (z : Real) :
    (fun i : Fin 2 => (IterExpChain 3).chainValues z ⟨i.val, by omega⟩)
      = (IterExpChain 2).chainValues z := by
  funext i
  rw [IterExpChain_chainValues, IterExpChain_chainValues]

/-- **The bridge eval-preservation.** For a `y₂`-free `q : MultiPoly 3`,
`eval q [IterExpChain 3] = eval (dropLastY q) [IterExpChain 2]`. -/
theorem dropLastY_eval_IterExp3 (q : MultiPoly 3)
    (hq : MultiPoly.degreeY (⟨2, by omega⟩ : Fin 3) q = 0) (z : Real) :
    MultiPoly.eval q z ((IterExpChain 3).chainValues z)
      = MultiPoly.eval (MultiPoly.dropLastY q) z ((IterExpChain 2).chainValues z) := by
  rw [← MultiPoly.eval_dropLastY q hq z ((IterExpChain 3).chainValues z), chainValues3_restrict_eq]

/-- `dropLastY` on `IterExpChain`'s relation polynomials (`prodVarYUpTo k`, `k < 2`) gives the
`IterExpChain 2` relation. The `varY` structural core of the `cTD` commutation below. -/
theorem dropLastY_prodVarYUpTo (k : Nat) (hk2 : k < 2) :
    MultiPoly.dropLastY (prodVarYUpTo k (by omega) : MultiPoly 3)
      = (prodVarYUpTo k hk2 : MultiPoly 2) := by
  match k, hk2 with
  | 0, _ => rfl
  | 1, _ => rfl

/-- **`degreeY₁` is preserved by `dropLastY`** (holds for every `q` — `dropLastY` only zeros out the
`y₂` variable, which carries no `y₁`-degree). Needed so the reduce's multiplier constant `d₁` matches
after the drop. -/
theorem degreeY1_dropLastY (q : MultiPoly 3) :
    MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) (MultiPoly.dropLastY q)
      = MultiPoly.degreeY (⟨1, by omega⟩ : Fin 3) q := by
  induction q with
  | const c => rfl
  | varX => rfl
  | varY i =>
    rcases i with ⟨v, hv⟩
    by_cases h : v < 2
    · show MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2)
            (if h : v < 2 then MultiPoly.varY (⟨v, h⟩ : Fin 2) else MultiPoly.const 0)
         = MultiPoly.degreeY (⟨1, by omega⟩ : Fin 3) (MultiPoly.varY (⟨v, hv⟩ : Fin 3))
      rw [dif_pos h]
      show (if (⟨1, by omega⟩ : Fin 2) = (⟨v, h⟩ : Fin 2) then 1 else 0)
         = (if (⟨1, by omega⟩ : Fin 3) = (⟨v, hv⟩ : Fin 3) then 1 else 0)
      by_cases hv1 : v = 1
      · rw [if_pos (by rw [Fin.mk.injEq]; omega), if_pos (by rw [Fin.mk.injEq]; omega)]
      · rw [if_neg (by rw [Fin.mk.injEq]; omega), if_neg (by rw [Fin.mk.injEq]; omega)]
    · show MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2)
            (if h : v < 2 then MultiPoly.varY (⟨v, h⟩ : Fin 2) else MultiPoly.const 0)
         = MultiPoly.degreeY (⟨1, by omega⟩ : Fin 3) (MultiPoly.varY (⟨v, hv⟩ : Fin 3))
      rw [dif_neg h]
      show (0 : Nat) = (if (⟨1, by omega⟩ : Fin 3) = (⟨v, hv⟩ : Fin 3) then 1 else 0)
      rw [if_neg (by rw [Fin.mk.injEq]; omega)]
  | add p q ihp ihq =>
    show Nat.max (MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) (MultiPoly.dropLastY p))
                 (MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) (MultiPoly.dropLastY q))
       = Nat.max (MultiPoly.degreeY (⟨1, by omega⟩ : Fin 3) p)
                 (MultiPoly.degreeY (⟨1, by omega⟩ : Fin 3) q)
    rw [ihp, ihq]
  | sub p q ihp ihq =>
    show Nat.max (MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) (MultiPoly.dropLastY p))
                 (MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) (MultiPoly.dropLastY q))
       = Nat.max (MultiPoly.degreeY (⟨1, by omega⟩ : Fin 3) p)
                 (MultiPoly.degreeY (⟨1, by omega⟩ : Fin 3) q)
    rw [ihp, ihq]
  | mul p q ihp ihq =>
    show MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) (MultiPoly.dropLastY p)
           + MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) (MultiPoly.dropLastY q)
       = MultiPoly.degreeY (⟨1, by omega⟩ : Fin 3) p
           + MultiPoly.degreeY (⟨1, by omega⟩ : Fin 3) q
    rw [ihp, ihq]

/-- **`dropLastY` commutes with the chain total derivative** for `y₂`-free polys:
`dropLastY (cTD₃ q) = cTD₂ (dropLastY q)`. The relation polys match under `dropLastY`
(`dropLastY_prodVarYUpTo`); the `y₂`-injecting relation only fires on `∂/∂y₂ q = 0`. -/
theorem dropLastY_cTD_commute (q : MultiPoly 3)
    (hq : MultiPoly.degreeY (⟨2, by omega⟩ : Fin 3) q = 0) :
    MultiPoly.dropLastY (chainTotalDeriv (IterExpChain 3) q)
      = chainTotalDeriv (IterExpChain 2) (MultiPoly.dropLastY q) := by
  induction q with
  | const c => rfl
  | varX => rfl
  | varY i =>
    rcases i with ⟨v, hv⟩
    have hv2 : v < 2 := by
      by_cases hvv : v < 2
      · exact hvv
      · exfalso
        have hveq : v = 2 := by omega
        subst hveq
        have hd1 : MultiPoly.degreeY (⟨2, by omega⟩ : Fin 3) (MultiPoly.varY (⟨2, hv⟩ : Fin 3)) = 1 := by
          show (if (⟨2, by omega⟩ : Fin 3) = (⟨2, hv⟩ : Fin 3) then 1 else 0) = 1
          rw [if_pos rfl]
        rw [hd1] at hq
        exact absurd hq (by omega)
    have hd : MultiPoly.dropLastY (MultiPoly.varY (⟨v, hv⟩ : Fin 3))
            = MultiPoly.varY (⟨v, hv2⟩ : Fin 2) := by
      show (if h : v < 2 then MultiPoly.varY (⟨v, h⟩ : Fin 2) else MultiPoly.const 0)
         = MultiPoly.varY (⟨v, hv2⟩ : Fin 2)
      rw [dif_pos hv2]
    show MultiPoly.dropLastY (prodVarYUpTo v hv : MultiPoly 3)
       = chainTotalDeriv (IterExpChain 2) (MultiPoly.dropLastY (MultiPoly.varY (⟨v, hv⟩ : Fin 3)))
    rw [dropLastY_prodVarYUpTo v hv2, hd]
    rfl
  | add p q ihp ihq =>
    have hp : MultiPoly.degreeY (⟨2, by omega⟩ : Fin 3) p = 0 := by
      have hle : MultiPoly.degreeY (⟨2, by omega⟩ : Fin 3) p
               ≤ Nat.max (MultiPoly.degreeY (⟨2, by omega⟩ : Fin 3) p)
                         (MultiPoly.degreeY (⟨2, by omega⟩ : Fin 3) q) := Nat.le_max_left _ _
      have hthis : MultiPoly.degreeY (⟨2, by omega⟩ : Fin 3) (MultiPoly.add p q)
           = Nat.max (MultiPoly.degreeY (⟨2, by omega⟩ : Fin 3) p)
                     (MultiPoly.degreeY (⟨2, by omega⟩ : Fin 3) q) := rfl
      omega
    have hq2 : MultiPoly.degreeY (⟨2, by omega⟩ : Fin 3) q = 0 := by
      have hle : MultiPoly.degreeY (⟨2, by omega⟩ : Fin 3) q
               ≤ Nat.max (MultiPoly.degreeY (⟨2, by omega⟩ : Fin 3) p)
                         (MultiPoly.degreeY (⟨2, by omega⟩ : Fin 3) q) := Nat.le_max_right _ _
      have hthis : MultiPoly.degreeY (⟨2, by omega⟩ : Fin 3) (MultiPoly.add p q)
           = Nat.max (MultiPoly.degreeY (⟨2, by omega⟩ : Fin 3) p)
                     (MultiPoly.degreeY (⟨2, by omega⟩ : Fin 3) q) := rfl
      omega
    show MultiPoly.add (MultiPoly.dropLastY (chainTotalDeriv (IterExpChain 3) p))
                       (MultiPoly.dropLastY (chainTotalDeriv (IterExpChain 3) q))
       = MultiPoly.add (chainTotalDeriv (IterExpChain 2) (MultiPoly.dropLastY p))
                       (chainTotalDeriv (IterExpChain 2) (MultiPoly.dropLastY q))
    rw [ihp hp, ihq hq2]
  | sub p q ihp ihq =>
    have hp : MultiPoly.degreeY (⟨2, by omega⟩ : Fin 3) p = 0 := by
      have hle : MultiPoly.degreeY (⟨2, by omega⟩ : Fin 3) p
               ≤ Nat.max (MultiPoly.degreeY (⟨2, by omega⟩ : Fin 3) p)
                         (MultiPoly.degreeY (⟨2, by omega⟩ : Fin 3) q) := Nat.le_max_left _ _
      have hthis : MultiPoly.degreeY (⟨2, by omega⟩ : Fin 3) (MultiPoly.sub p q)
           = Nat.max (MultiPoly.degreeY (⟨2, by omega⟩ : Fin 3) p)
                     (MultiPoly.degreeY (⟨2, by omega⟩ : Fin 3) q) := rfl
      omega
    have hq2 : MultiPoly.degreeY (⟨2, by omega⟩ : Fin 3) q = 0 := by
      have hle : MultiPoly.degreeY (⟨2, by omega⟩ : Fin 3) q
               ≤ Nat.max (MultiPoly.degreeY (⟨2, by omega⟩ : Fin 3) p)
                         (MultiPoly.degreeY (⟨2, by omega⟩ : Fin 3) q) := Nat.le_max_right _ _
      have hthis : MultiPoly.degreeY (⟨2, by omega⟩ : Fin 3) (MultiPoly.sub p q)
           = Nat.max (MultiPoly.degreeY (⟨2, by omega⟩ : Fin 3) p)
                     (MultiPoly.degreeY (⟨2, by omega⟩ : Fin 3) q) := rfl
      omega
    show MultiPoly.sub (MultiPoly.dropLastY (chainTotalDeriv (IterExpChain 3) p))
                       (MultiPoly.dropLastY (chainTotalDeriv (IterExpChain 3) q))
       = MultiPoly.sub (chainTotalDeriv (IterExpChain 2) (MultiPoly.dropLastY p))
                       (chainTotalDeriv (IterExpChain 2) (MultiPoly.dropLastY q))
    rw [ihp hp, ihq hq2]
  | mul p q ihp ihq =>
    have hp : MultiPoly.degreeY (⟨2, by omega⟩ : Fin 3) p = 0 := by
      have hthis : MultiPoly.degreeY (⟨2, by omega⟩ : Fin 3) (MultiPoly.mul p q)
           = MultiPoly.degreeY (⟨2, by omega⟩ : Fin 3) p
             + MultiPoly.degreeY (⟨2, by omega⟩ : Fin 3) q := rfl
      omega
    have hq2 : MultiPoly.degreeY (⟨2, by omega⟩ : Fin 3) q = 0 := by
      have hthis : MultiPoly.degreeY (⟨2, by omega⟩ : Fin 3) (MultiPoly.mul p q)
           = MultiPoly.degreeY (⟨2, by omega⟩ : Fin 3) p
             + MultiPoly.degreeY (⟨2, by omega⟩ : Fin 3) q := rfl
      omega
    -- cTD(mul p q) = add (mul (cTD p) q) (mul p (cTD q)); dropLastY distributes over add/mul.
    show MultiPoly.add
           (MultiPoly.mul (MultiPoly.dropLastY (chainTotalDeriv (IterExpChain 3) p))
                          (MultiPoly.dropLastY q))
           (MultiPoly.mul (MultiPoly.dropLastY p)
                          (MultiPoly.dropLastY (chainTotalDeriv (IterExpChain 3) q)))
       = MultiPoly.add
           (MultiPoly.mul (chainTotalDeriv (IterExpChain 2) (MultiPoly.dropLastY p))
                          (MultiPoly.dropLastY q))
           (MultiPoly.mul (MultiPoly.dropLastY p)
                          (chainTotalDeriv (IterExpChain 2) (MultiPoly.dropLastY q)))
    rw [ihp hp, ihq hq2]

end MachLib.IterExpDepth3Bridge
