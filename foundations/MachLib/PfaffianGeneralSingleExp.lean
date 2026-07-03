import MachLib.PfaffianGeneralHnzWF

/-!
# Generalize — the single-exponential (depth-1 / y₀-level) machinery for general exp-type chains

The depth-2 base descent `hBaseHnz` bottoms out at the single-exp descent on the leading `y₁`-coefficient
(a `y₁`-free `MultiPoly 2`), reducing its `y₀`-structure. `singleExpMeasureCanon` is chain-agnostic, but
the ∀N reduce `seReduce` and its descent (`ChainExp2*`, ~1900 lines) are IterExp-specific (`G₀ = 1`). The
KEY de-risking fact: for a general `G₀` the reduce's leading `y₀`-coefficient is *identically* `(lc)'ₓ`
(the `G₀` terms cancel — `d·G₀·lcY₀` from the identity injection meets `d·G₀·lcY₀` from the `cdegY0·G₀`
multiplier), so the descent reuses the IterExp result plus a 2-case split. This file ports the y₀-level cTD
machinery (`degreeY0_cTD_eq_of_y1free`, `leadingCoeffY0_cTD_eval`) to arbitrary exp-type chains, threading
the extra `G₀` factor.
-/
namespace MachLib.PfaffianGeneralReduce
open MachLib.Real MachLib.MultiPolyMod MachLib.PfaffianChainMod
open MachLib.PfaffianChainMod.PfaffianFn MachLib.IterExpDepthN MachLib.IterExpTopIdentity

private theorem degY1L {a b : MultiPoly 2}
    (h : MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) (MultiPoly.add a b) = 0) :
    MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) a = 0 :=
  Nat.le_zero.mp (h ▸ Nat.le_max_left _ _)
private theorem degY1R {a b : MultiPoly 2}
    (h : MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) (MultiPoly.add a b) = 0) :
    MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) b = 0 :=
  Nat.le_zero.mp (h ▸ Nat.le_max_right _ _)
private theorem degY1Ls {a b : MultiPoly 2}
    (h : MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) (MultiPoly.sub a b) = 0) :
    MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) a = 0 :=
  Nat.le_zero.mp (h ▸ Nat.le_max_left _ _)
private theorem degY1Rs {a b : MultiPoly 2}
    (h : MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) (MultiPoly.sub a b) = 0) :
    MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) b = 0 :=
  Nat.le_zero.mp (h ▸ Nat.le_max_right _ _)

/-- **General y₀-degree preservation.** For a `y₁`-free `q`, `chainTotalDeriv c'` preserves the `y₀`-degree,
for any exp-type chain (`relations 0 = G₀·y₀`, `degreeY₀ G₀ = 0`). Generalizes `degreeY0_cTD_eq_of_y1free`
(only the `varY 0` case changes: `degreeY₀(relations 0) = 1` from exp-type, not `rfl`). -/
theorem degreeY0_cTD_eq_of_y1free_gen {c' : PfaffianChain 2} (G0 : MultiPoly 2)
    (hrel0 : c'.relations (⟨0, by omega⟩ : Fin 2) = MultiPoly.mul G0 (MultiPoly.varY (⟨0, by omega⟩ : Fin 2)))
    (hG0 : MultiPoly.degreeY (⟨0, by omega⟩ : Fin 2) G0 = 0) (q : MultiPoly 2) :
    MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) q = 0 →
    MultiPoly.degreeY (⟨0, by omega⟩ : Fin 2) (chainTotalDeriv c' q)
      = MultiPoly.degreeY (⟨0, by omega⟩ : Fin 2) q := by
  have hvar0 : MultiPoly.degreeY (⟨0, by omega⟩ : Fin 2) (MultiPoly.varY (⟨0, by omega⟩ : Fin 2)) = 1 := by
    show (if (⟨0, by omega⟩ : Fin 2) = (⟨0, by omega⟩ : Fin 2) then 1 else 0) = 1; rw [if_pos rfl]
  induction q with
  | const c => intro _; rfl
  | varX => intro _; rfl
  | varY j =>
    intro hy1
    rcases j with ⟨v, hv⟩
    match v, hv with
    | 0, _ =>
      show MultiPoly.degreeY (⟨0, by omega⟩ : Fin 2) (c'.relations (⟨0, by omega⟩ : Fin 2))
         = MultiPoly.degreeY (⟨0, by omega⟩ : Fin 2) (MultiPoly.varY (⟨0, by omega⟩ : Fin 2))
      rw [hrel0, degreeY_mul' (⟨0, by omega⟩ : Fin 2) G0 (MultiPoly.varY (⟨0, by omega⟩ : Fin 2)), hG0, hvar0]
    | 1, _ => simp [MultiPoly.degreeY] at hy1
  | add p q ihp ihq =>
    intro hy1
    show Nat.max (MultiPoly.degreeY (⟨0, by omega⟩ : Fin 2) (chainTotalDeriv c' p))
                 (MultiPoly.degreeY (⟨0, by omega⟩ : Fin 2) (chainTotalDeriv c' q))
       = Nat.max (MultiPoly.degreeY (⟨0, by omega⟩ : Fin 2) p) (MultiPoly.degreeY (⟨0, by omega⟩ : Fin 2) q)
    rw [ihp (degY1L hy1), ihq (degY1R hy1)]
  | sub p q ihp ihq =>
    intro hy1
    show Nat.max (MultiPoly.degreeY (⟨0, by omega⟩ : Fin 2) (chainTotalDeriv c' p))
                 (MultiPoly.degreeY (⟨0, by omega⟩ : Fin 2) (chainTotalDeriv c' q))
       = Nat.max (MultiPoly.degreeY (⟨0, by omega⟩ : Fin 2) p) (MultiPoly.degreeY (⟨0, by omega⟩ : Fin 2) q)
    rw [ihp (degY1Ls hy1), ihq (degY1Rs hy1)]
  | mul p q ihp ihq =>
    intro hy1
    have hp1 : MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) p = 0 := by
      have h' : MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) p + MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) q = 0 := hy1
      omega
    have hq1 : MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) q = 0 := by
      have h' : MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) p + MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) q = 0 := hy1
      omega
    show Nat.max (MultiPoly.degreeY (⟨0, by omega⟩ : Fin 2) (chainTotalDeriv c' p)
                  + MultiPoly.degreeY (⟨0, by omega⟩ : Fin 2) q)
                 (MultiPoly.degreeY (⟨0, by omega⟩ : Fin 2) p
                  + MultiPoly.degreeY (⟨0, by omega⟩ : Fin 2) (chainTotalDeriv c' q))
       = MultiPoly.degreeY (⟨0, by omega⟩ : Fin 2) p + MultiPoly.degreeY (⟨0, by omega⟩ : Fin 2) q
    rw [ihp hp1, ihq hq1]; exact Nat.max_self _

end MachLib.PfaffianGeneralReduce
