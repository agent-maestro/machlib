import MachLib.ChainExp2SDR

/-!
# The general `leadingCoeffY₁`-under-`chainTotalDeriv` identity for chain-2 (Piece 3 core)

The descent that closes chain-2 termination rests on computing `lcY₁(chain2Reduce c p)`, which needs the
*general* (any-environment) identity — the chain-2 analog of single-exp's
`leadingCoeffY_chainTotalDeriv_eval_SingleExp_*` (`ChainExp2PathC`):

  `eval(lcY₁(cTD₂ p)) x env = eval(cTD₂(lcY₁ p)) x env  +  d · eval(y₀ · lcY₁ p) x env`,  `d = degreeY₁ p`.

The extra term carries a `y₀` factor (vs single-exp's bare `d·lcY₀ p`) because `y₁' = y₀·y₁`. Setting
`y₀ = 0` recovers the existing `ChainExp2SDR.lcY1_cTD_eval_zero_IterExp2`.

We build it the way the single-exp version was built: **case by case**. This file ships the **base cases**
(`const`, `varX`, `varY 0`, `varY 1`); the inductive `add`/`sub`/`mul` cases and the final assembly follow
(separate lemmas, same skeleton as `ChainExp2SDR.lcY1_cTD_eval_zero_IterExp2`). `ChainExp2SDR` is untouched
(Path B); no `sorry`.

The heart of *why* chain-2 differs is the `varY 1` base case: `cTD₂(y₁) = y₀·y₁`, so `lcY₁(cTD₂ y₁) = y₀`,
whereas `cTD₂(lcY₁ y₁) = cTD₂(1) = 0` — the whole `eval` is carried by the `d·y₀·lcY₁` term (`d = 1`).
-/

namespace MachLib.ChainExp2LcY1CTD

open MachLib.Real
open MachLib.MultiPolyMod
open MachLib.PfaffianChainMod
open MachLib.PfaffianChainMod.PfaffianFn
open MachLib.IterExpChainMod
open MachLib.ChainExp2SDR

/-- **Base cases** of the general chain-2 `leadingCoeffY₁`-under-`cTD` identity, for `const`, `varX`,
`varY 0`, `varY 1`. The `varY 1` conjunct is the structural reason chain-2 needs the `y₀` factor. -/
theorem leadingCoeffY1_cTD_eval_IterExp2_base (x : Real) (env : Fin 2 → Real) :
    (∀ c : Real,
      MultiPoly.eval (MultiPoly.leadingCoeffY (⟨1, by omega⟩ : Fin 2)
          (chainTotalDeriv (IterExpChain 2) (MultiPoly.const c : MultiPoly 2))) x env
      = MultiPoly.eval (chainTotalDeriv (IterExpChain 2)
          (MultiPoly.leadingCoeffY (⟨1, by omega⟩ : Fin 2) (MultiPoly.const c))) x env
        + MachLib.Real.natCast (MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) (MultiPoly.const c))
          * MultiPoly.eval (MultiPoly.mul (MultiPoly.varY (⟨0, by omega⟩ : Fin 2))
              (MultiPoly.leadingCoeffY (⟨1, by omega⟩ : Fin 2) (MultiPoly.const c))) x env)
  ∧ (MultiPoly.eval (MultiPoly.leadingCoeffY (⟨1, by omega⟩ : Fin 2)
          (chainTotalDeriv (IterExpChain 2) (MultiPoly.varX : MultiPoly 2))) x env
      = MultiPoly.eval (chainTotalDeriv (IterExpChain 2)
          (MultiPoly.leadingCoeffY (⟨1, by omega⟩ : Fin 2) (MultiPoly.varX : MultiPoly 2))) x env
        + MachLib.Real.natCast (MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) (MultiPoly.varX : MultiPoly 2))
          * MultiPoly.eval (MultiPoly.mul (MultiPoly.varY (⟨0, by omega⟩ : Fin 2))
              (MultiPoly.leadingCoeffY (⟨1, by omega⟩ : Fin 2) (MultiPoly.varX : MultiPoly 2))) x env)
  ∧ (MultiPoly.eval (MultiPoly.leadingCoeffY (⟨1, by omega⟩ : Fin 2)
          (chainTotalDeriv (IterExpChain 2) (MultiPoly.varY (⟨0, by omega⟩ : Fin 2)))) x env
      = MultiPoly.eval (chainTotalDeriv (IterExpChain 2)
          (MultiPoly.leadingCoeffY (⟨1, by omega⟩ : Fin 2) (MultiPoly.varY (⟨0, by omega⟩ : Fin 2)))) x env
        + MachLib.Real.natCast (MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2)
            (MultiPoly.varY (⟨0, by omega⟩ : Fin 2)))
          * MultiPoly.eval (MultiPoly.mul (MultiPoly.varY (⟨0, by omega⟩ : Fin 2))
              (MultiPoly.leadingCoeffY (⟨1, by omega⟩ : Fin 2)
                (MultiPoly.varY (⟨0, by omega⟩ : Fin 2)))) x env)
  ∧ (MultiPoly.eval (MultiPoly.leadingCoeffY (⟨1, by omega⟩ : Fin 2)
          (chainTotalDeriv (IterExpChain 2) (MultiPoly.varY (⟨1, by omega⟩ : Fin 2)))) x env
      = MultiPoly.eval (chainTotalDeriv (IterExpChain 2)
          (MultiPoly.leadingCoeffY (⟨1, by omega⟩ : Fin 2) (MultiPoly.varY (⟨1, by omega⟩ : Fin 2)))) x env
        + MachLib.Real.natCast (MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2)
            (MultiPoly.varY (⟨1, by omega⟩ : Fin 2)))
          * MultiPoly.eval (MultiPoly.mul (MultiPoly.varY (⟨0, by omega⟩ : Fin 2))
              (MultiPoly.leadingCoeffY (⟨1, by omega⟩ : Fin 2)
                (MultiPoly.varY (⟨1, by omega⟩ : Fin 2)))) x env) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- const c: cTD₂(const c)=0, lcY₁(0)=0 ⇒ LHS 0; lcY₁(const c)=const c, cTD₂=0 ⇒ RHS 0; degreeY₁=0.
    intro c
    show (0 : Real) = 0 + MachLib.Real.natCast 0
        * (env (⟨0, by omega⟩ : Fin 2) * c)
    rw [MachLib.Real.natCast_zero]; mach_ring
  · -- varX: cTD₂(varX)=const 1, lcY₁(1)=1 ⇒ LHS 1; lcY₁(varX)=varX, cTD₂=1 ⇒ RHS 1; degreeY₁=0.
    show (1 : Real) = 1 + MachLib.Real.natCast 0
        * (env (⟨0, by omega⟩ : Fin 2) * x)
    rw [MachLib.Real.natCast_zero]; mach_ring
  · -- varY 0: cTD₂(y₀)=y₀, lcY₁(y₀)=y₀ ⇒ LHS env 0; RHS env 0; degreeY₁(y₀)=0.
    show env (⟨0, by omega⟩ : Fin 2)
        = env (⟨0, by omega⟩ : Fin 2) + MachLib.Real.natCast 0
          * (env (⟨0, by omega⟩ : Fin 2) * env (⟨0, by omega⟩ : Fin 2))
    rw [MachLib.Real.natCast_zero]; mach_ring
  · -- varY 1: cTD₂(y₁)=y₀·y₁ ⇒ lcY₁=y₀ ⇒ LHS env 0 · 1; lcY₁(y₁)=1, cTD₂(1)=0 ⇒ RHS 0; degreeY₁=1.
    show env (⟨0, by omega⟩ : Fin 2) * (1 : Real)
        = 0 + MachLib.Real.natCast 1
          * (env (⟨0, by omega⟩ : Fin 2) * (1 : Real))
    rw [MachLib.Real.natCast_succ, MachLib.Real.natCast_zero]; mach_ring

/-! ### `leadingCoeffY`-of-`add` helpers (the `add` analogs of the existing `…_sub_…` lemmas) -/

private theorem lcY_add_of_gt {n : Nat} (i : Fin n) (p q : MultiPoly n)
    (h : MultiPoly.degreeY i q < MultiPoly.degreeY i p) :
    MultiPoly.leadingCoeffY i (MultiPoly.add p q) = MultiPoly.leadingCoeffY i p := by
  show (if MultiPoly.degreeY i p > MultiPoly.degreeY i q then MultiPoly.leadingCoeffY i p
        else if MultiPoly.degreeY i q > MultiPoly.degreeY i p then MultiPoly.leadingCoeffY i q
        else MultiPoly.add (MultiPoly.leadingCoeffY i p) (MultiPoly.leadingCoeffY i q))
       = MultiPoly.leadingCoeffY i p
  rw [if_pos h]

private theorem lcY_add_of_lt {n : Nat} (i : Fin n) (p q : MultiPoly n)
    (h : MultiPoly.degreeY i p < MultiPoly.degreeY i q) :
    MultiPoly.leadingCoeffY i (MultiPoly.add p q) = MultiPoly.leadingCoeffY i q := by
  show (if MultiPoly.degreeY i p > MultiPoly.degreeY i q then MultiPoly.leadingCoeffY i p
        else if MultiPoly.degreeY i q > MultiPoly.degreeY i p then MultiPoly.leadingCoeffY i q
        else MultiPoly.add (MultiPoly.leadingCoeffY i p) (MultiPoly.leadingCoeffY i q))
       = MultiPoly.leadingCoeffY i q
  rw [if_neg (Nat.not_lt.mpr (Nat.le_of_lt h)), if_pos h]

private theorem lcY_add_of_eq {n : Nat} (i : Fin n) (p q : MultiPoly n)
    (h : MultiPoly.degreeY i p = MultiPoly.degreeY i q) :
    MultiPoly.leadingCoeffY i (MultiPoly.add p q)
      = MultiPoly.add (MultiPoly.leadingCoeffY i p) (MultiPoly.leadingCoeffY i q) := by
  show (if MultiPoly.degreeY i p > MultiPoly.degreeY i q then MultiPoly.leadingCoeffY i p
        else if MultiPoly.degreeY i q > MultiPoly.degreeY i p then MultiPoly.leadingCoeffY i q
        else MultiPoly.add (MultiPoly.leadingCoeffY i p) (MultiPoly.leadingCoeffY i q))
       = MultiPoly.add (MultiPoly.leadingCoeffY i p) (MultiPoly.leadingCoeffY i q)
  rw [if_neg (by omega : ¬ MultiPoly.degreeY i p > MultiPoly.degreeY i q),
      if_neg (by omega : ¬ MultiPoly.degreeY i q > MultiPoly.degreeY i p)]

/-! ### Inductive `add` case of the identity -/

/-- The `add` step of the general chain-2 `leadingCoeffY₁`-under-`cTD` identity: the `degreeY₁`
trichotomy (`cTD` preserves `degreeY₁`, so the leading term comes from the same side after the
derivative), then the IHs. The `=`-branch carries the extra `d·y₀·lcY₁` term through a ring rearrangement
(`d_p = d_q`). -/
theorem leadingCoeffY1_cTD_eval_IterExp2_add (p q : MultiPoly 2) (x : Real) (env : Fin 2 → Real)
    (ihp :
      MultiPoly.eval (MultiPoly.leadingCoeffY (⟨1, by omega⟩ : Fin 2)
          (chainTotalDeriv (IterExpChain 2) p)) x env
      = MultiPoly.eval (chainTotalDeriv (IterExpChain 2)
          (MultiPoly.leadingCoeffY (⟨1, by omega⟩ : Fin 2) p)) x env
        + MachLib.Real.natCast (MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) p)
          * MultiPoly.eval (MultiPoly.mul (MultiPoly.varY (⟨0, by omega⟩ : Fin 2))
              (MultiPoly.leadingCoeffY (⟨1, by omega⟩ : Fin 2) p)) x env)
    (ihq :
      MultiPoly.eval (MultiPoly.leadingCoeffY (⟨1, by omega⟩ : Fin 2)
          (chainTotalDeriv (IterExpChain 2) q)) x env
      = MultiPoly.eval (chainTotalDeriv (IterExpChain 2)
          (MultiPoly.leadingCoeffY (⟨1, by omega⟩ : Fin 2) q)) x env
        + MachLib.Real.natCast (MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) q)
          * MultiPoly.eval (MultiPoly.mul (MultiPoly.varY (⟨0, by omega⟩ : Fin 2))
              (MultiPoly.leadingCoeffY (⟨1, by omega⟩ : Fin 2) q)) x env) :
    MultiPoly.eval (MultiPoly.leadingCoeffY (⟨1, by omega⟩ : Fin 2)
        (chainTotalDeriv (IterExpChain 2) (MultiPoly.add p q))) x env
    = MultiPoly.eval (chainTotalDeriv (IterExpChain 2)
        (MultiPoly.leadingCoeffY (⟨1, by omega⟩ : Fin 2) (MultiPoly.add p q))) x env
      + MachLib.Real.natCast (MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) (MultiPoly.add p q))
        * MultiPoly.eval (MultiPoly.mul (MultiPoly.varY (⟨0, by omega⟩ : Fin 2))
            (MultiPoly.leadingCoeffY (⟨1, by omega⟩ : Fin 2) (MultiPoly.add p q))) x env := by
  have hp_eq := degreeY1_chainTotalDeriv_eq_IterExp2 p
  have hq_eq := degreeY1_chainTotalDeriv_eq_IterExp2 q
  -- cTD distributes over `add` (definitional).
  rw [show chainTotalDeriv (IterExpChain 2) (MultiPoly.add p q)
        = MultiPoly.add (chainTotalDeriv (IterExpChain 2) p)
            (chainTotalDeriv (IterExpChain 2) q) from rfl]
  rcases Nat.lt_trichotomy (MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) p)
                           (MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) q) with hlt | heq | hgt
  · -- d_p < d_q: leading from q.
    have hd : MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) (MultiPoly.add p q)
            = MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) q := Nat.max_eq_right (Nat.le_of_lt hlt)
    rw [lcY_add_of_lt (⟨1, by omega⟩ : Fin 2) (chainTotalDeriv (IterExpChain 2) p)
          (chainTotalDeriv (IterExpChain 2) q) (by rw [hp_eq, hq_eq]; exact hlt),
        lcY_add_of_lt (⟨1, by omega⟩ : Fin 2) p q hlt, hd]
    exact ihq
  · -- d_p = d_q: both sides contribute; ring with the extra term.
    have hd : MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) (MultiPoly.add p q)
            = MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) q := by
      show Nat.max _ _ = _; rw [heq]; exact Nat.max_self _
    rw [lcY_add_of_eq (⟨1, by omega⟩ : Fin 2) (chainTotalDeriv (IterExpChain 2) p)
          (chainTotalDeriv (IterExpChain 2) q) (by rw [hp_eq, hq_eq]; exact heq),
        lcY_add_of_eq (⟨1, by omega⟩ : Fin 2) p q heq, hd,
        show chainTotalDeriv (IterExpChain 2)
               (MultiPoly.add (MultiPoly.leadingCoeffY (⟨1, by omega⟩ : Fin 2) p)
                              (MultiPoly.leadingCoeffY (⟨1, by omega⟩ : Fin 2) q))
           = MultiPoly.add
               (chainTotalDeriv (IterExpChain 2) (MultiPoly.leadingCoeffY (⟨1, by omega⟩ : Fin 2) p))
               (chainTotalDeriv (IterExpChain 2) (MultiPoly.leadingCoeffY (⟨1, by omega⟩ : Fin 2) q))
           from rfl]
    simp only [MultiPoly.eval_add, MultiPoly.eval_mul] at ihp ihq ⊢
    rw [heq] at ihp
    rw [ihp, ihq]; mach_ring
  · -- d_p > d_q: leading from p.
    have hd : MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) (MultiPoly.add p q)
            = MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) p := Nat.max_eq_left (Nat.le_of_lt hgt)
    rw [lcY_add_of_gt (⟨1, by omega⟩ : Fin 2) (chainTotalDeriv (IterExpChain 2) p)
          (chainTotalDeriv (IterExpChain 2) q) (by rw [hp_eq, hq_eq]; exact hgt),
        lcY_add_of_gt (⟨1, by omega⟩ : Fin 2) p q hgt, hd]
    exact ihp

/-! ### `leadingCoeffY`-of-`sub` `gt` helper (the `_of_lt`/`_of_eq` ones already exist in `MultiPoly`) -/

private theorem lcY_sub_of_gt {n : Nat} (i : Fin n) (p q : MultiPoly n)
    (h : MultiPoly.degreeY i q < MultiPoly.degreeY i p) :
    MultiPoly.leadingCoeffY i (MultiPoly.sub p q) = MultiPoly.leadingCoeffY i p := by
  show (if MultiPoly.degreeY i p > MultiPoly.degreeY i q then MultiPoly.leadingCoeffY i p
        else if MultiPoly.degreeY i q > MultiPoly.degreeY i p
             then MultiPoly.sub (MultiPoly.const 0) (MultiPoly.leadingCoeffY i q)
             else MultiPoly.sub (MultiPoly.leadingCoeffY i p) (MultiPoly.leadingCoeffY i q))
       = MultiPoly.leadingCoeffY i p
  rw [if_pos h]

/-! ### Inductive `sub` case of the identity -/

/-- The `sub` step. Parallel to `add`, but the `d_p < d_q` branch carries the negation
(`lcY₁(sub p q) = sub (const 0) (lcY₁ q)`), so the IH enters with a sign — the `mach_ring` step absorbs
it (and the extra `d·y₀·lcY₁` term). -/
theorem leadingCoeffY1_cTD_eval_IterExp2_sub (p q : MultiPoly 2) (x : Real) (env : Fin 2 → Real)
    (ihp :
      MultiPoly.eval (MultiPoly.leadingCoeffY (⟨1, by omega⟩ : Fin 2)
          (chainTotalDeriv (IterExpChain 2) p)) x env
      = MultiPoly.eval (chainTotalDeriv (IterExpChain 2)
          (MultiPoly.leadingCoeffY (⟨1, by omega⟩ : Fin 2) p)) x env
        + MachLib.Real.natCast (MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) p)
          * MultiPoly.eval (MultiPoly.mul (MultiPoly.varY (⟨0, by omega⟩ : Fin 2))
              (MultiPoly.leadingCoeffY (⟨1, by omega⟩ : Fin 2) p)) x env)
    (ihq :
      MultiPoly.eval (MultiPoly.leadingCoeffY (⟨1, by omega⟩ : Fin 2)
          (chainTotalDeriv (IterExpChain 2) q)) x env
      = MultiPoly.eval (chainTotalDeriv (IterExpChain 2)
          (MultiPoly.leadingCoeffY (⟨1, by omega⟩ : Fin 2) q)) x env
        + MachLib.Real.natCast (MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) q)
          * MultiPoly.eval (MultiPoly.mul (MultiPoly.varY (⟨0, by omega⟩ : Fin 2))
              (MultiPoly.leadingCoeffY (⟨1, by omega⟩ : Fin 2) q)) x env) :
    MultiPoly.eval (MultiPoly.leadingCoeffY (⟨1, by omega⟩ : Fin 2)
        (chainTotalDeriv (IterExpChain 2) (MultiPoly.sub p q))) x env
    = MultiPoly.eval (chainTotalDeriv (IterExpChain 2)
        (MultiPoly.leadingCoeffY (⟨1, by omega⟩ : Fin 2) (MultiPoly.sub p q))) x env
      + MachLib.Real.natCast (MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) (MultiPoly.sub p q))
        * MultiPoly.eval (MultiPoly.mul (MultiPoly.varY (⟨0, by omega⟩ : Fin 2))
            (MultiPoly.leadingCoeffY (⟨1, by omega⟩ : Fin 2) (MultiPoly.sub p q))) x env := by
  have hp_eq := degreeY1_chainTotalDeriv_eq_IterExp2 p
  have hq_eq := degreeY1_chainTotalDeriv_eq_IterExp2 q
  rw [show chainTotalDeriv (IterExpChain 2) (MultiPoly.sub p q)
        = MultiPoly.sub (chainTotalDeriv (IterExpChain 2) p)
            (chainTotalDeriv (IterExpChain 2) q) from rfl]
  rcases Nat.lt_trichotomy (MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) p)
                           (MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) q) with hlt | heq | hgt
  · -- d_p < d_q: leading is `-lcY₁ q` (negation).
    have hd : MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) (MultiPoly.sub p q)
            = MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) q := Nat.max_eq_right (Nat.le_of_lt hlt)
    rw [MultiPoly.leadingCoeffY_sub_of_lt (⟨1, by omega⟩ : Fin 2)
          (chainTotalDeriv (IterExpChain 2) p) (chainTotalDeriv (IterExpChain 2) q)
          (by rw [hp_eq, hq_eq]; exact hlt),
        MultiPoly.leadingCoeffY_sub_of_lt (⟨1, by omega⟩ : Fin 2) p q hlt, hd,
        show chainTotalDeriv (IterExpChain 2)
               (MultiPoly.sub (MultiPoly.const 0) (MultiPoly.leadingCoeffY (⟨1, by omega⟩ : Fin 2) q))
           = MultiPoly.sub (MultiPoly.const 0)
               (chainTotalDeriv (IterExpChain 2) (MultiPoly.leadingCoeffY (⟨1, by omega⟩ : Fin 2) q))
           from rfl]
    simp only [MultiPoly.eval_sub, MultiPoly.eval_mul, MultiPoly.eval_add, MultiPoly.eval_const]
      at ihp ihq ⊢
    rw [ihq]; mach_ring
  · -- d_p = d_q: both contribute (no negation in this branch); ring with the extra term.
    have hd : MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) (MultiPoly.sub p q)
            = MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) q := by
      show Nat.max _ _ = _; rw [heq]; exact Nat.max_self _
    rw [MultiPoly.leadingCoeffY_sub_of_eq (⟨1, by omega⟩ : Fin 2)
          (chainTotalDeriv (IterExpChain 2) p) (chainTotalDeriv (IterExpChain 2) q)
          (by rw [hp_eq, hq_eq]; exact heq),
        MultiPoly.leadingCoeffY_sub_of_eq (⟨1, by omega⟩ : Fin 2) p q heq, hd,
        show chainTotalDeriv (IterExpChain 2)
               (MultiPoly.sub (MultiPoly.leadingCoeffY (⟨1, by omega⟩ : Fin 2) p)
                              (MultiPoly.leadingCoeffY (⟨1, by omega⟩ : Fin 2) q))
           = MultiPoly.sub
               (chainTotalDeriv (IterExpChain 2) (MultiPoly.leadingCoeffY (⟨1, by omega⟩ : Fin 2) p))
               (chainTotalDeriv (IterExpChain 2) (MultiPoly.leadingCoeffY (⟨1, by omega⟩ : Fin 2) q))
           from rfl]
    simp only [MultiPoly.eval_sub, MultiPoly.eval_mul, MultiPoly.eval_add] at ihp ihq ⊢
    rw [heq] at ihp
    rw [ihp, ihq]
    -- abstract the (large) eval atoms so the ring step is on plain variables (mach_ring is fast then;
    -- left as evals it times out on the subtraction-heavy normal form).
    generalize MultiPoly.eval (chainTotalDeriv (IterExpChain 2)
        (MultiPoly.leadingCoeffY (⟨1, by omega⟩ : Fin 2) p)) x env = A
    generalize MultiPoly.eval (chainTotalDeriv (IterExpChain 2)
        (MultiPoly.leadingCoeffY (⟨1, by omega⟩ : Fin 2) q)) x env = B
    generalize MultiPoly.eval (MultiPoly.varY (⟨0, by omega⟩ : Fin 2)) x env = Y
    generalize MultiPoly.eval (MultiPoly.leadingCoeffY (⟨1, by omega⟩ : Fin 2) p) x env = LP
    generalize MultiPoly.eval (MultiPoly.leadingCoeffY (⟨1, by omega⟩ : Fin 2) q) x env = LQ
    generalize MachLib.Real.natCast (MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) q) = N
    mach_ring
  · -- d_p > d_q: leading from p.
    have hd : MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) (MultiPoly.sub p q)
            = MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) p := Nat.max_eq_left (Nat.le_of_lt hgt)
    rw [lcY_sub_of_gt (⟨1, by omega⟩ : Fin 2) (chainTotalDeriv (IterExpChain 2) p)
          (chainTotalDeriv (IterExpChain 2) q) (by rw [hp_eq, hq_eq]; exact hgt),
        lcY_sub_of_gt (⟨1, by omega⟩ : Fin 2) p q hgt, hd]
    exact ihp

end MachLib.ChainExp2LcY1CTD
