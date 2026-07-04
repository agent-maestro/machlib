import MachLib.PfaffianGeneralBoundUncond
import MachLib.IterExpDepthNBoundUncond
import MachLib.IterExpChain
import MachLib.Exp
namespace MachLib.PfaffianGeneralReduce
open MachLib.Real MachLib.MultiPolyMod MachLib.MultiPolyMod.MultiPoly MachLib.PfaffianChainMod
open MachLib.IterExpTopIdentity MachLib.IterExpDepthN MachLib.IterExpChainMod

/-- `iterExp n x = exp(…) > 0` at every level. -/
theorem iterExp_pos (n : Nat) (x : Real) : 0 < iterExp n x := by
  cases n with
  | zero => exact exp_pos x
  | succ m => exact exp_pos (iterExp m x)

/-- The exp-type factor `Gᵢ = y₀·…·y_{i-1}` (empty product `= 1` at level 0). Written as
`prodVarYUpTo (i-1)`, so `Gᵢ·yᵢ = prodVarYUpTo i` for `i ≥ 1` (matching `IterExpChain`) and `1·y₀` at 0. -/
noncomputable def prodVarYBelow {N : Nat} : (k : Nat) → k < N → MultiPoly N
  | 0,     _  => MultiPoly.const 1
  | n + 1, hk => prodVarYUpTo n (Nat.lt_of_succ_lt hk)

theorem degreeY_prodVarYBelow_self {N : Nat} (k : Nat) (hk : k < N) (i : Fin N) (hi : i.val = k) :
    MultiPoly.degreeY i (prodVarYBelow k hk) = 0 := by
  cases k with
  | zero => exact degreeY_const i 1
  | succ n => exact degreeY_prodVarYUpTo_zero_of_lt n (Nat.lt_of_succ_lt hk) i (by omega)

theorem degreeY_prodVarYBelow_gt {N : Nat} (k : Nat) (hk : k < N) (i j : Fin N)
    (hi : i.val = k) (hj : j.val > i.val) :
    MultiPoly.degreeY j (prodVarYBelow k hk) = 0 := by
  cases k with
  | zero => exact degreeY_const j 1
  | succ n => exact degreeY_prodVarYUpTo_zero_of_lt n (Nat.lt_of_succ_lt hk) j (by omega)

/-- `Gᵢ·yᵢ` evaluates the same as `IterExpChain`'s relation `prodVarYUpTo i`. -/
theorem prodVarYBelow_mul_varY_eval {N : Nat} (k : Nat) (hk : k < N) (i : Fin N) (hi : i.val = k)
    (x : Real) (env : Fin N → Real) :
    MultiPoly.eval (MultiPoly.mul (prodVarYBelow k hk) (MultiPoly.varY i)) x env
      = MultiPoly.eval (prodVarYUpTo k hk) x env := by
  cases k with
  | zero =>
    show MultiPoly.eval (MultiPoly.mul (MultiPoly.const 1) (MultiPoly.varY i)) x env
       = MultiPoly.eval (MultiPoly.varY (⟨0, hk⟩ : Fin N)) x env
    rw [MultiPoly.eval_mul, MultiPoly.eval_const, MultiPoly.eval_varY, MultiPoly.eval_varY, one_mul_thm,
        show i = (⟨0, hk⟩ : Fin N) from Fin.ext hi]
  | succ n =>
    show MultiPoly.eval (MultiPoly.mul (prodVarYUpTo n (Nat.lt_of_succ_lt hk)) (MultiPoly.varY i)) x env
       = MultiPoly.eval (prodVarYUpTo (n + 1) hk) x env
    rw [prodVarYUpTo_succ n hk, MultiPoly.eval_mul, MultiPoly.eval_mul, MultiPoly.eval_varY,
        MultiPoly.eval_varY, show i = (⟨n + 1, hk⟩ : Fin N) from Fin.ext hi]

/-- **The normalized iterated-exp chain.** SAME chain functions (`evals = iterExp`) as `IterExpChain`, but
relations written uniformly in exp-type form `Gᵢ·yᵢ` — so it satisfies the general bound's `IsExpChain`
hypothesis (which `IterExpChain` fails only because its level-0 relation is the bare `y₀`, not `1·y₀`). -/
noncomputable def IterExpChainNorm (N : Nat) : PfaffianChain N :=
  { evals := (IterExpChain N).evals,
    relations := fun i => MultiPoly.mul (prodVarYBelow i.val i.isLt) (MultiPoly.varY i) }

theorem IterExpChainNorm_isExp (N : Nat) : IsExpChain (IterExpChainNorm N) := by
  intro i
  refine ⟨⟨prodVarYBelow i.val i.isLt, degreeY_prodVarYBelow_self i.val i.isLt i rfl, rfl⟩, ?_⟩
  intro j hij
  show MultiPoly.degreeY j (MultiPoly.mul (prodVarYBelow i.val i.isLt) (MultiPoly.varY i)) = 0
  rw [degreeY_mul' j (prodVarYBelow i.val i.isLt) (MultiPoly.varY i),
      degreeY_prodVarYBelow_gt i.val i.isLt i j rfl hij]
  have hij' : i ≠ j := fun h => (Nat.ne_of_lt hij) (congrArg Fin.val h)
  show 0 + (if j = i then 1 else 0) = 0
  rw [if_neg (Ne.symm hij')]

theorem IterExpChainNorm_coh (N : Nat) (a b : Real) : (IterExpChainNorm N).IsCoherentOn a b := by
  intro x hxa hxb i
  have h := IterExpChain_isCoherentOn N a b x hxa hxb i
  show HasDerivAt ((IterExpChain N).evals i)
    (MultiPoly.eval (MultiPoly.mul (prodVarYBelow i.val i.isLt) (MultiPoly.varY i)) x
      ((IterExpChain N).chainValues x)) x
  rw [prodVarYBelow_mul_varY_eval i.val i.isLt i rfl x ((IterExpChain N).chainValues x)]
  exact h

theorem IterExpChainNorm_pos (N : Nat) (a b : Real) :
    ∀ z, a < z → z < b → ∀ i : Fin N, 0 < (IterExpChainNorm N).evals i z := by
  intro z _ _ i
  exact iterExp_pos i.val z

/-- **BRIDGE: the specific `chainNFn` finiteness, RE-DERIVED via the general bound.** The clean statement of
`chainN_khovanskii_bound_unconditional` — Khovanskii finiteness for the concrete iterated-exp chain at every
depth — obtained by instantiating the GENERAL `pfaffian_khovanskii_bound_gen_uncond` at `IterExpChainNorm`.
The `chainNFn` eval is definitionally equal to `pfaffianChainFn IterExpChainNorm` (same `evals`), so the
general result transfers with no rewriting. Validates the generalization strictly subsumes the specific arc. -/
theorem chainNFn_khovanskii_via_general (m : Nat) (p : MultiPoly (m + 2)) (a b : Real) (hab : a < b)
    (hne : ∃ z, a < z ∧ z < b ∧ (chainNFn (m + 2) p).eval z ≠ 0) :
    ∃ N : Nat, ∀ zeros : List Real, zeros.Nodup →
      (∀ z ∈ zeros, a < z ∧ z < b ∧ (chainNFn (m + 2) p).eval z = 0) → zeros.length ≤ N :=
  pfaffian_khovanskii_bound_gen_uncond a b hab m (IterExpChainNorm (m + 2))
    (IterExpChainNorm_isExp (m + 2)) (IterExpChainNorm_coh (m + 2) a b)
    (IterExpChainNorm_pos (m + 2) a b) p hne

end MachLib.PfaffianGeneralReduce
