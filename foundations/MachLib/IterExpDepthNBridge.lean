import MachLib.IterExpDepthNGraded

/-!
# The `dropLastY` bridge, for every depth `N = M+2`

The depth-`N` → depth-`(N-1)` recursion (brick #3, `chainNReduce_graded_cancels`) leaves an honest
reduce of `lcY_top p`. To feed the depth-induction hypothesis, `lcY_top p` — a `MultiPoly (M+2)` that
is free of the top variable — must be viewed one level down as a `MultiPoly (M+1)` over the shorter
chain `IterExpChain (M+1)`. `MultiPoly.dropLastY` does the syntactic projection; this file lands the
generic-`M` facts that make it eval-faithful, the ∀M analog of `IterExpDepth3Bridge`:

* `chainValues_restrict_eq`   — the `(M+2)`-chain's values, restricted to the first `M+1` slots, ARE
                                the `(M+1)`-chain's values.
* `dropLastY_eval_IterExp`    — for a top-free `q`, evaluating `q` along `IterExpChain (M+2)` equals
                                evaluating `dropLastY q` along `IterExpChain (M+1)`.
* `dropLastY_prodVarYUpTo`    — the relation polynomials `y₀·…·y_{k-1}` (`k < M+1`) match under the drop.
* `dropLastY_cTD_commute`     — for a top-free `q`, `dropLastY (cTD_{M+2} q) = cTD_{M+1} (dropLastY q)`.

Together: the depth-`(M+2)` reduce's dropped top coefficient IS a depth-`(M+1)` reduce, so the
induction on depth closes. No `sorry`.
-/

namespace MachLib.IterExpDepthN

open MachLib.Real
open MachLib.MultiPolyMod
open MachLib.PfaffianChainMod
open MachLib.PfaffianChainMod.PfaffianFn
open MachLib.IterExpChainMod

/-- `Nat.max a b = 0 → a = 0 ∧ b = 0` (Mathlib-free; `omega` here doesn't reduce `Nat.max`). Stated on
abstract `a b` so it sidesteps the differing `Fin` index proof-terms that block `omega` on the raw
`degreeY` atoms. -/
private theorem nat_max_eq_zero {a b : Nat} (h : Nat.max a b = 0) : a = 0 ∧ b = 0 := by
  have hla : a ≤ Nat.max a b := Nat.le_max_left a b
  have hlb : b ≤ Nat.max a b := Nat.le_max_right a b
  omega

/-- The `(M+2)`-chain's values, restricted to the first `M+1` coordinates, are the `(M+1)`-chain's. -/
theorem chainValues_restrict_eq (M : Nat) (z : Real) :
    (fun i : Fin (M + 1) => (IterExpChain (M + 2)).chainValues z ⟨i.val, by omega⟩)
      = (IterExpChain (M + 1)).chainValues z := by
  funext i
  rw [IterExpChain_chainValues, IterExpChain_chainValues]

/-- **The bridge eval-preservation, `∀M`.** For a top-free `q : MultiPoly (M+2)`,
`eval q [IterExpChain (M+2)] = eval (dropLastY q) [IterExpChain (M+1)]`. -/
theorem dropLastY_eval_IterExp (M : Nat) (q : MultiPoly (M + 2))
    (hq : MultiPoly.degreeY (⟨M + 1, by omega⟩ : Fin (M + 2)) q = 0) (z : Real) :
    MultiPoly.eval q z ((IterExpChain (M + 2)).chainValues z)
      = MultiPoly.eval (MultiPoly.dropLastY q) z ((IterExpChain (M + 1)).chainValues z) := by
  rw [← MultiPoly.eval_dropLastY q hq z ((IterExpChain (M + 2)).chainValues z),
      chainValues_restrict_eq]

/-- The relation polynomials `y₀·…·y_{k-1}` (`k < M+1`) are preserved by `dropLastY`. -/
theorem dropLastY_prodVarYUpTo (M : Nat) :
    ∀ (k : Nat) (hk : k < M + 1),
      MultiPoly.dropLastY (prodVarYUpTo k (by omega) : MultiPoly (M + 2))
        = (prodVarYUpTo k hk : MultiPoly (M + 1)) := by
  intro k
  induction k with
  | zero =>
    intro hk
    show MultiPoly.dropLastY (MultiPoly.varY (⟨0, by omega⟩ : Fin (M + 2)))
       = MultiPoly.varY (⟨0, hk⟩ : Fin (M + 1))
    show (if h : (0 : Nat) < M + 1 then MultiPoly.varY (⟨0, h⟩ : Fin (M + 1)) else MultiPoly.const 0)
       = MultiPoly.varY (⟨0, hk⟩ : Fin (M + 1))
    rw [dif_pos hk]
  | succ n ih =>
    intro hk
    have hn : n < M + 1 := by omega
    show MultiPoly.dropLastY (MultiPoly.mul (prodVarYUpTo n (by omega))
            (MultiPoly.varY (⟨n + 1, by omega⟩ : Fin (M + 2))))
       = MultiPoly.mul (prodVarYUpTo n hn) (MultiPoly.varY (⟨n + 1, hk⟩ : Fin (M + 1)))
    show MultiPoly.mul (MultiPoly.dropLastY (prodVarYUpTo n (by omega)))
            (MultiPoly.dropLastY (MultiPoly.varY (⟨n + 1, by omega⟩ : Fin (M + 2))))
       = MultiPoly.mul (prodVarYUpTo n hn) (MultiPoly.varY (⟨n + 1, hk⟩ : Fin (M + 1)))
    rw [ih hn]
    congr 1
    show (if h : n + 1 < M + 1 then MultiPoly.varY (⟨n + 1, h⟩ : Fin (M + 1)) else MultiPoly.const 0)
       = MultiPoly.varY (⟨n + 1, hk⟩ : Fin (M + 1))
    rw [dif_pos hk]

/-- **`dropLastY` commutes with the chain total derivative, `∀M`**, for top-free polys:
`dropLastY (cTD_{M+2} q) = cTD_{M+1} (dropLastY q)`. The `varY` case uses `dropLastY_prodVarYUpTo`
(the relation polys match); the top-injecting relation only fires where `q` has no top degree. -/
theorem dropLastY_cTD_commute (M : Nat) (q : MultiPoly (M + 2))
    (hq : MultiPoly.degreeY (⟨M + 1, by omega⟩ : Fin (M + 2)) q = 0) :
    MultiPoly.dropLastY (chainTotalDeriv (IterExpChain (M + 2)) q)
      = chainTotalDeriv (IterExpChain (M + 1)) (MultiPoly.dropLastY q) := by
  induction q with
  | const c => rfl
  | varX => rfl
  | varY i =>
    rcases i with ⟨v, hv⟩
    have hv2 : v < M + 1 := by
      by_cases hvv : v < M + 1
      · exact hvv
      · exfalso
        have hveq : v = M + 1 := by omega
        subst hveq
        have hd1 : MultiPoly.degreeY (⟨M + 1, by omega⟩ : Fin (M + 2))
                     (MultiPoly.varY (⟨M + 1, hv⟩ : Fin (M + 2))) = 1 := by
          show (if (⟨M + 1, by omega⟩ : Fin (M + 2)) = (⟨M + 1, hv⟩ : Fin (M + 2)) then 1 else 0) = 1
          rw [if_pos (by rw [Fin.mk.injEq])]
        rw [hd1] at hq
        exact absurd hq (by omega)
    have hd : MultiPoly.dropLastY (MultiPoly.varY (⟨v, hv⟩ : Fin (M + 2)))
            = MultiPoly.varY (⟨v, hv2⟩ : Fin (M + 1)) := by
      show (if h : v < M + 1 then MultiPoly.varY (⟨v, h⟩ : Fin (M + 1)) else MultiPoly.const 0)
         = MultiPoly.varY (⟨v, hv2⟩ : Fin (M + 1))
      rw [dif_pos hv2]
    show MultiPoly.dropLastY (prodVarYUpTo v hv : MultiPoly (M + 2))
       = chainTotalDeriv (IterExpChain (M + 1)) (MultiPoly.dropLastY (MultiPoly.varY (⟨v, hv⟩ : Fin (M + 2))))
    rw [dropLastY_prodVarYUpTo M v hv2, hd]
    rfl
  | add p q ihp ihq =>
    have h0 : Nat.max (MultiPoly.degreeY (⟨M + 1, by omega⟩ : Fin (M + 2)) p)
                      (MultiPoly.degreeY (⟨M + 1, by omega⟩ : Fin (M + 2)) q) = 0 := hq
    have hp : MultiPoly.degreeY (⟨M + 1, by omega⟩ : Fin (M + 2)) p = 0 := (nat_max_eq_zero h0).1
    have hq2 : MultiPoly.degreeY (⟨M + 1, by omega⟩ : Fin (M + 2)) q = 0 := (nat_max_eq_zero h0).2
    show MultiPoly.add (MultiPoly.dropLastY (chainTotalDeriv (IterExpChain (M + 2)) p))
                       (MultiPoly.dropLastY (chainTotalDeriv (IterExpChain (M + 2)) q))
       = MultiPoly.add (chainTotalDeriv (IterExpChain (M + 1)) (MultiPoly.dropLastY p))
                       (chainTotalDeriv (IterExpChain (M + 1)) (MultiPoly.dropLastY q))
    rw [ihp hp, ihq hq2]
  | sub p q ihp ihq =>
    have h0 : Nat.max (MultiPoly.degreeY (⟨M + 1, by omega⟩ : Fin (M + 2)) p)
                      (MultiPoly.degreeY (⟨M + 1, by omega⟩ : Fin (M + 2)) q) = 0 := hq
    have hp : MultiPoly.degreeY (⟨M + 1, by omega⟩ : Fin (M + 2)) p = 0 := (nat_max_eq_zero h0).1
    have hq2 : MultiPoly.degreeY (⟨M + 1, by omega⟩ : Fin (M + 2)) q = 0 := (nat_max_eq_zero h0).2
    show MultiPoly.sub (MultiPoly.dropLastY (chainTotalDeriv (IterExpChain (M + 2)) p))
                       (MultiPoly.dropLastY (chainTotalDeriv (IterExpChain (M + 2)) q))
       = MultiPoly.sub (chainTotalDeriv (IterExpChain (M + 1)) (MultiPoly.dropLastY p))
                       (chainTotalDeriv (IterExpChain (M + 1)) (MultiPoly.dropLastY q))
    rw [ihp hp, ihq hq2]
  | mul p q ihp ihq =>
    have hp : MultiPoly.degreeY (⟨M + 1, by omega⟩ : Fin (M + 2)) p = 0 := by
      have : MultiPoly.degreeY (⟨M + 1, by omega⟩ : Fin (M + 2)) (MultiPoly.mul p q)
           = MultiPoly.degreeY (⟨M + 1, by omega⟩ : Fin (M + 2)) p
             + MultiPoly.degreeY (⟨M + 1, by omega⟩ : Fin (M + 2)) q := rfl
      omega
    have hq2 : MultiPoly.degreeY (⟨M + 1, by omega⟩ : Fin (M + 2)) q = 0 := by
      have : MultiPoly.degreeY (⟨M + 1, by omega⟩ : Fin (M + 2)) (MultiPoly.mul p q)
           = MultiPoly.degreeY (⟨M + 1, by omega⟩ : Fin (M + 2)) p
             + MultiPoly.degreeY (⟨M + 1, by omega⟩ : Fin (M + 2)) q := rfl
      omega
    show MultiPoly.add
           (MultiPoly.mul (MultiPoly.dropLastY (chainTotalDeriv (IterExpChain (M + 2)) p))
                          (MultiPoly.dropLastY q))
           (MultiPoly.mul (MultiPoly.dropLastY p)
                          (MultiPoly.dropLastY (chainTotalDeriv (IterExpChain (M + 2)) q)))
       = MultiPoly.add
           (MultiPoly.mul (chainTotalDeriv (IterExpChain (M + 1)) (MultiPoly.dropLastY p))
                          (MultiPoly.dropLastY q))
           (MultiPoly.mul (MultiPoly.dropLastY p)
                          (chainTotalDeriv (IterExpChain (M + 1)) (MultiPoly.dropLastY q)))
    rw [ihp hp, ihq hq2]

end MachLib.IterExpDepthN
