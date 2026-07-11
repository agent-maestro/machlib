import MachLib.IterExpDepthNBudgetGen

/-!
# Growth-tolerant reduce closures for the general Pfaffian explicit bound (step 4 crux)

The general single-variable Pfaffian *explicit* bound
(`monogate-research/roadmap/pfaffian-general-explicit-bound-design.md`) ports the closed `chainN`
explicit build over the general reduce `chainReduce`. Assembling the reduce arm surfaced the budget-port
crux (analogous to chainN §4″): the existing cap-generic reduce closure `invPhiG_reduce` tolerates the
cap argument `B` growing by only **`+1`** per reduce (`hB : B' ≤ B + 1`). That is exactly right for the
iterated-exp *tower*, whose relations are x-free (format `α = 1` — `degreeX` non-increasing under
reduce). But a **general** coherent exp-chain grows `degreeX` by its Khovanskii format `α` per reduce
(`degreeX_chainReduce_le_format`), so `B' ≤ B + α`, and `invPhiG_reduce` no longer applies when `α > 1`.

The resolution is a strictly more general closure: the budget still drops by the Rolle `+1` as long as
the inner rank strictly drops **and** the cap growth is *compensated* by the inner-rank drop
(`B' + ir' ≤ B + ir`), rather than capping the growth at `+1`. This survives any `α`, provided the inner
rank drops enough to keep `B + ir` from rising — which the format-scaled inner rank supplies. Pure
`Nat`; recovers `invPhiG_reduce` as the `B' ≤ B+1` special case.
-/

namespace MachLib.IterExpDepthN

/-- **Growth-tolerant reduce closure.** Generalises `invPhiG_reduce` from `hB : B' ≤ B+1` to the
compensated condition `hBir : B' + ir' ≤ B + ir`. The budget drops by the Rolle `+1` whenever the inner
rank strictly drops (`ir'+1 ≤ ir`) and the cap growth is absorbed by that drop. Recovers `invPhiG_reduce`
(there `B' ≤ B+1` and `ir'+1 ≤ ir` give `B'+ir' ≤ B+1+ir' ≤ B+ir`). -/
theorem invPhiG_reduce_grow (cap : Nat → Nat)
    (hcap : ∀ {B B' : Nat}, B ≤ B' → cap B ≤ cap B')
    (Nleaf d ir ir' B B' : Nat) (hir : ir' + 1 ≤ ir) (hBir : B' + ir' ≤ B + ir) :
    invPhiG cap Nleaf (d + 1) ir' B' + 1 ≤ invPhiG cap Nleaf (d + 1) ir B := by
  show ir' + levelBudgetG cap Nleaf d (B' + ir' + 1) + 1
       ≤ ir + levelBudgetG cap Nleaf d (B + ir + 1)
  have hmono := levelBudgetG_mono_B cap hcap Nleaf d
    (show B' + ir' + 1 ≤ B + ir + 1 from by omega)
  omega

/-- **Amount-carrying growth-tolerant reduce closure.** `invPhiG_reduce_grow` outputs only the Rolle
`+1`; the depth-`N` step's `Ndep`-monotonicity argument needs the budget to drop by the *full* format
`k` (= the reduce's `degreeX` growth `B → B+k`), not just `1`. The same proof delivers it: the inner
rank drop `ir' + k ≤ ir` passes straight through the `levelBudgetG` monotonicity. Recovers
`invPhiG_reduce_grow` at `k = 1`. -/
theorem invPhiG_reduce_grow_amt (cap : Nat → Nat)
    (hcap : ∀ {B B' : Nat}, B ≤ B' → cap B ≤ cap B')
    (Nleaf d ir ir' B B' k : Nat) (hir : ir' + k ≤ ir) (hBir : B' + ir' ≤ B + ir) :
    invPhiG cap Nleaf (d + 1) ir' B' + k ≤ invPhiG cap Nleaf (d + 1) ir B := by
  show ir' + levelBudgetG cap Nleaf d (B' + ir' + 1) + k
       ≤ ir + levelBudgetG cap Nleaf d (B + ir + 1)
  have hmono := levelBudgetG_mono_B cap hcap Nleaf d
    (show B' + ir' + 1 ≤ B + ir + 1 from by omega)
  omega

/-- **Format-shaped reduce closure.** The form the general base's reduce arm consumes directly: with the
chain format `α ≥ 1`, an inner-rank drop of at least `α` (`ir' + α ≤ ir` — the format-scaled inner rank
falling by ≥ 1 structural unit) and cap growth of at most `α` (`B' ≤ B + α` — `degreeX` grows by ≤ the
format) close the reduce step. The `α`-drop both covers the Rolle `+1` and compensates the cap growth. -/
theorem invPhiG_reduce_format (cap : Nat → Nat)
    (hcap : ∀ {B B' : Nat}, B ≤ B' → cap B ≤ cap B')
    (Nleaf d ir ir' B B' α : Nat) (hα : 1 ≤ α) (hir : ir' + α ≤ ir) (hB : B' ≤ B + α) :
    invPhiG cap Nleaf (d + 1) ir' B' + 1 ≤ invPhiG cap Nleaf (d + 1) ir B := by
  apply invPhiG_reduce_grow cap hcap Nleaf d ir ir' B B'
  · omega
  · omega

/-- **α-scaled reduce closure — the chain-side interface.** The chain supplies a *structural* inner rank
`irs` (the `nestedOrder`/`rankRec` linearisation) that drops by ≥ 1 per reduce (`irs'+1 ≤ irs`) and a
`degreeX` growth of ≤ `α` (`B' ≤ B+α`). Using the **α-scaled** rank `α·irs` in the invariant converts the
structural `≥1` drop into the `≥α` drop `invPhiG_reduce_format` demands (`α·irs' + α = α·(irs'+1) ≤
α·irs`), so the reduce step closes for any format `α ≥ 1`. The scaling costs a factor `α` in the bound —
exactly the format dependence `Ngen(M, deg, α)`. -/
theorem invPhiG_reduce_scaled (cap : Nat → Nat)
    (hcap : ∀ {B B' : Nat}, B ≤ B' → cap B ≤ cap B')
    (Nleaf d irs irs' B B' α : Nat) (hα : 1 ≤ α) (hstruct : irs' + 1 ≤ irs) (hB : B' ≤ B + α) :
    invPhiG cap Nleaf (d + 1) (α * irs') B' + 1 ≤ invPhiG cap Nleaf (d + 1) (α * irs) B := by
  refine invPhiG_reduce_format cap hcap Nleaf d (α * irs) (α * irs') B B' α hα ?_ hB
  have hstep : α * (irs' + 1) ≤ α * irs := Nat.mul_le_mul (Nat.le_refl α) hstruct
  rw [Nat.mul_succ] at hstep
  exact hstep

end MachLib.IterExpDepthN
