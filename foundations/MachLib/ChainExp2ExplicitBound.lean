import MachLib.ChainExp2NoZeros
import MachLib.ExplicitBoundRank
import MachLib.IterExpChain

/-!
# Explicit chain-2 Khovanskii bound — degree-preservation foundations

The finiteness theorem `chain2_khovanskii_bound_unconditional` gives `∃ N` via well-founded recursion.
To turn that into an EXPLICIT `N(degrees)` we linearize the nested-lex measure with `rankLex A B`
(`ExplicitBoundRank.lean`), which needs global upper bounds `A ≥ cdegY0(lcY₁ q)` and `B ≥ (x-degree of q)`
over every `q` the recursion reaches. This file proves the two DEGREE-PRESERVATION facts those bounds rest
on — the crux of the explicit bound:

  * `cdegY0_lcY1_reduce_le` — the reduce never raises `cdegY0(lcY₁ ·)` (the A-bound). Falls straight out of
    the nested-lex descent (`chain2Reduce_nestedLT_canon`) + fst-preservation.
  * `degreeX_chain2Reduce_le` — the reduce never raises the whole-poly x-degree (the B-bound), since the
    total derivative is x-degree-non-increasing (relations are x-free) and the reduce multiplier is x-free.

Remaining for the full explicit bound: the trim analogs (`dropLeadingYAt ⟨1⟩`), the bridge
(measure x-component ≤ `degreeX`), and threading the `(A,B)` invariant + `rankLex_succ_le` through the WF
recursion. -/

namespace MachLib.ChainExp2Explicit
open MachLib.Real MachLib.MultiPolyMod MachLib.MultiPolyMod.MultiPoly
open MachLib.PfaffianChainMod MachLib.PfaffianChainMod.PfaffianFn MachLib.IterExpChainMod
open MachLib.ChainExp2CanonMeasure MachLib.ChainExp2Reducer MachLib.ChainExp2PhantomDescent
open MachLib.ChainExp2CdegInv MachLib.LexProd

/-! ### The degreeY₀ GROWTH side — the source of the exponential-in-degreeY₁ bound

Unlike x-degree (non-increasing), `degreeY₀` GROWS by ≤ 1 per reduce (the reduce multiplier has a `y₀`
factor, and `chainTotalDeriv` replaces each `varY i` by `relations i` of `degreeY₀ = 1`). Compounded across
the `degreeY₁` trim levels, this `+1`-per-step is exactly why the explicit bound from this descent is
exponential in `degreeY₁`. These lemmas formalize the per-step growth (the accounting's foundation). -/

/-- `degreeY₀(prodVarYUpTo …) = 1` — every tower relation has exactly one `y₀` factor. -/
theorem degreeY0_prodVarYUpTo {N : Nat} (hN : 0 < N) (k : Nat) (hk : k < N) :
    MultiPoly.degreeY (⟨0, hN⟩ : Fin N) (prodVarYUpTo k hk) = 1 := by
  induction k with
  | zero =>
    show (if (⟨0, hN⟩ : Fin N) = (⟨0, hk⟩ : Fin N) then 1 else 0) = 1
    rw [if_pos (Fin.ext rfl)]
  | succ n ih =>
    show MultiPoly.degreeY (⟨0, hN⟩ : Fin N) (prodVarYUpTo n (Nat.lt_of_succ_lt hk))
        + MultiPoly.degreeY (⟨0, hN⟩ : Fin N) (MultiPoly.varY (⟨n + 1, hk⟩ : Fin N)) = 1
    rw [ih (Nat.lt_of_succ_lt hk)]
    show 1 + (if (⟨0, hN⟩ : Fin N) = (⟨n + 1, hk⟩ : Fin N) then 1 else 0) = 1
    rw [if_neg (by intro h; have := congrArg Fin.val h; simp at this)]

/-- **degreeY₀ grows by at most 1 under `chainTotalDeriv`.** Structural induction on the Leibniz recursion;
each `varY i` becomes `relations i` (`degreeY₀ = 1`), the product rule keeps the `+1` bound additive. -/
theorem degreeY0_chainTotalDeriv_le (q : MultiPoly 2) :
    MultiPoly.degreeY (⟨0, by omega⟩ : Fin 2) (chainTotalDeriv (IterExpChain 2) q)
    ≤ MultiPoly.degreeY (⟨0, by omega⟩ : Fin 2) q + 1 := by
  induction q with
  | const c => exact Nat.zero_le _
  | varX => exact Nat.zero_le _
  | varY i =>
    show MultiPoly.degreeY (⟨0, by omega⟩ : Fin 2) (prodVarYUpTo i.val i.isLt)
        ≤ MultiPoly.degreeY (⟨0, by omega⟩ : Fin 2) (MultiPoly.varY i) + 1
    rw [degreeY0_prodVarYUpTo (by omega) i.val i.isLt]; omega
  | add p q ihp ihq =>
    refine Nat.max_le.mpr ⟨?_, ?_⟩
    · exact Nat.le_trans ihp (Nat.add_le_add_right (Nat.le_max_left _ _) 1)
    · exact Nat.le_trans ihq (Nat.add_le_add_right (Nat.le_max_right _ _) 1)
  | sub p q ihp ihq =>
    refine Nat.max_le.mpr ⟨?_, ?_⟩
    · exact Nat.le_trans ihp (Nat.add_le_add_right (Nat.le_max_left _ _) 1)
    · exact Nat.le_trans ihq (Nat.add_le_add_right (Nat.le_max_right _ _) 1)
  | mul p q ihp ihq =>
    show Nat.max (MultiPoly.degreeY (⟨0, by omega⟩ : Fin 2) (chainTotalDeriv (IterExpChain 2) p)
                    + MultiPoly.degreeY (⟨0, by omega⟩ : Fin 2) q)
                 (MultiPoly.degreeY (⟨0, by omega⟩ : Fin 2) p
                    + MultiPoly.degreeY (⟨0, by omega⟩ : Fin 2) (chainTotalDeriv (IterExpChain 2) q))
      ≤ MultiPoly.degreeY (⟨0, by omega⟩ : Fin 2) p + MultiPoly.degreeY (⟨0, by omega⟩ : Fin 2) q + 1
    refine Nat.max_le.mpr ⟨?_, ?_⟩
    · have := ihp; omega
    · have := ihq; omega

/-- **degreeY₀ grows by at most 1 under the chain-2 reduce.** The multiplier `(degreeY₁ q)·y₀ + c` has
`degreeY₀ = 1` and `cTD` grows `degreeY₀` by ≤ 1 — so the reduce grows it by ≤ 1. Per-step growth for the
exponential explicit-bound accounting (the trim then switches `lcY₁` to a coefficient these reduces grew,
which is why a global `A ≥ cdegY0(lcY₁ q)` is a degree functional of the ORIGINAL p, not a constant). -/
theorem degreeY0_chain2Reduce_le (c : Real) (q : MultiPoly 2) :
    MultiPoly.degreeY (⟨0, by omega⟩ : Fin 2) (chain2Reduce c q)
    ≤ MultiPoly.degreeY (⟨0, by omega⟩ : Fin 2) q + 1 := by
  unfold chain2Reduce
  refine Nat.max_le.mpr ⟨degreeY0_chainTotalDeriv_le q, ?_⟩
  show (1 + MultiPoly.degreeY (⟨0, by omega⟩ : Fin 2) q) ≤ MultiPoly.degreeY (⟨0, by omega⟩ : Fin 2) q + 1
  omega

/-- **cdegY0 non-increase under the reduce (A-bound).** The reduce ties `degreeY₁` and drops the inner
`singleExpMeasureCanon(lcY₁ ·)` in lex — so its first component `cdegY0(lcY₁ ·)` can only stay or fall. -/
theorem cdegY0_lcY1_reduce_le (p : MultiPoly 2)
    (hnz : (singleExpMeasureCanon (MultiPoly.leadingCoeffY (⟨1, by omega⟩ : Fin 2) p)).2 ≠ 0) :
    cdegY0 (MultiPoly.leadingCoeffY (⟨1, by omega⟩ : Fin 2)
      (chain2Reduce (MachLib.Real.natCast (cdegY0 (MultiPoly.leadingCoeffY (⟨1, by omega⟩ : Fin 2) p))) p))
    ≤ cdegY0 (MultiPoly.leadingCoeffY (⟨1, by omega⟩ : Fin 2) p) := by
  have h := chain2Reduce_nestedLT_canon p hnz
  have hfst := chain2MeasureCanon_fst_chain2Reduce
    (MachLib.Real.natCast (cdegY0 (MultiPoly.leadingCoeffY (⟨1, by omega⟩ : Fin 2) p))) p
  rcases h with hlt | ⟨_, hinner⟩
  · exact absurd (hfst ▸ hlt) (Nat.lt_irrefl _)
  · rcases hinner with ha | ⟨haeq, _⟩
    · exact Nat.le_of_lt ha
    · exact Nat.le_of_eq haeq

/-- `degreeX(prodVarYUpTo …) = 0` — the iterated-exp tower relations are x-free. -/
theorem degreeX_prodVarYUpTo_zero {N : Nat} (k : Nat) (hk : k < N) :
    MultiPoly.degreeX (prodVarYUpTo k hk : MultiPoly N) = 0 := by
  induction k with
  | zero => rfl
  | succ n ih =>
    show MultiPoly.degreeX (prodVarYUpTo n (Nat.lt_of_succ_lt hk))
        + MultiPoly.degreeX (MultiPoly.varY (⟨n + 1, hk⟩ : Fin N)) = 0
    rw [ih (Nat.lt_of_succ_lt hk), degreeX_varY]

/-- **degreeX non-increase under the chain-2 reduce (B-bound).** `chain2Reduce = cTD(p) − mult·p`; `cTD`
doesn't raise x-degree (relations x-free) and `mult = (degreeY₁ p)·y₀ + c` is x-free, so the whole x-degree
can only stay or fall. The x-component of the canonical measure is `≤ degreeX` of the polynomial, so
`degreeX(p₀)` globally bounds it over the recursion. -/
theorem degreeX_chain2Reduce_le (c : Real) (p : MultiPoly 2) :
    MultiPoly.degreeX (chain2Reduce c p) ≤ MultiPoly.degreeX p := by
  have h_rel_x : ∀ j : Fin 2, MultiPoly.degreeX ((IterExpChain 2).relations j) = 0 :=
    fun j => degreeX_prodVarYUpTo_zero j.val j.isLt
  unfold chain2Reduce
  refine Nat.max_le.mpr ⟨degreeX_chainTotalDeriv_le (IterExpChain 2) h_rel_x p, ?_⟩
  show (0 : Nat) + MultiPoly.degreeX p ≤ MultiPoly.degreeX p
  omega

end MachLib.ChainExp2Explicit
