import MachLib.IterExpTopIdentity
import MachLib.ChainExp2NoZeros

/-!
# Frontier-1 lemma (1), for EVERY depth `N = M+2` — the `∀M` closure

This file finishes the generic-`M` version of `IterExpTopIdentity.leadingCoeffY2_cTD_eval_IterExp3`
(depth-3) so that the top-`leadingCoeffY`-under-`chainTotalDeriv` product-injection identity holds at
**every** depth, machine-checked:

  `eval(lcY_top(cTD p)) = eval(cTD(lcY_top p)) + (degreeY_top p) · eval(F · lcY_top p)`,

with `top = ⟨M+1⟩ : Fin (M+2)` and injection factor `F = Ffac M = y₀·y₁·…·y_M`.
`M = 0` is chain-2 (`F = y₀`); `M = 1` is depth-3 (`F = y₀·y₁`); this covers every higher tower.

## Why this was the documented blocker — and what the fix actually is

The depth-3 concrete proof compiles in ~5 s; the earlier fully-generic `∀M` attempt diverged
(>7 min at 4M heartbeats). The prior diagnosis blamed `whnf` of the `Nat.rec`-defined
`prodVarYUpTo M`. That is **not** the operative cause: marking the factor `Ffac` `irreducible`
(so `prodVarYUpTo M` can never be unfolded) does **not** fix it — the divergence persists, and at 6M
heartbeats `isDefEq` still times out (63 s, no convergence).

The real cause is `rw`'s `kabstract`: to locate a rewrite it runs `isDefEq` against subterms of the
goal, and with the **literal symbolic index `⟨M+1, by omega⟩`** sprinkled through a large goal, every
comparison re-`whnf`s the *stuck* `leadingCoeffY`/`degreeY` recursors at that index — an unbounded
search. The concrete depth-3 case is fast only because `⟨2⟩ : Fin 3` is a *closed* index whose
recursors reduce.

The fix, therefore, is to **keep the top index an abstract variable** `i : Fin (M+2)` carrying only
`hi : i.val = M+1`, and to confine the one place the literal is unavoidable (invoking the upstream
`…top…` lemmas, which are stated at `⟨M+1⟩`) inside three tiny wrapper lemmas whose goals are a single
equation — so that one `kabstract` is trivially cheap. The big induction then runs over the *opaque*
`i`, where `leadingCoeffY i`/`degreeY i` stay atomic and `kabstract` matches by variable identity.
Result: the worst step (`idN_mul`) drops from divergent-at-6M-heartbeats to **0.5 s**.

Path B: `ChainExp2SDR` and the single-exp framework are untouched. No `sorry`.
-/

namespace MachLib.IterExpDepthN

open MachLib.Real
open MachLib.MultiPolyMod
open MachLib.PfaffianChainMod
open MachLib.PfaffianChainMod.PfaffianFn
open MachLib.IterExpChainMod
open MachLib.IterExpTopIdentity
open MachLib.ChainExp2NoZeros

/-! ## Abstract-index wrappers — the literal `⟨M+1⟩` (and its one cheap `kabstract`) is confined here

Each restates an upstream `…top…` lemma (proven at the literal `⟨M+1⟩`) for an *abstract* index `i`
with `hi : i.val = M+1`. The rewrite `i → ⟨M+1,_⟩` runs on a one-equation goal, so it is trivially
cheap — and every caller downstream sees only the atomic `i`. -/

theorem degreeYtop_cTD_eq' (M : Nat) (i : Fin (M + 2)) (hi : i.val = M + 1)
    (p : MultiPoly (M + 2)) :
    MultiPoly.degreeY i (chainTotalDeriv (IterExpChain (M + 2)) p) = MultiPoly.degreeY i p := by
  have h : i = (⟨M + 1, by omega⟩ : Fin (M + 2)) := Fin.ext hi
  rw [h]; exact degreeYtop_cTD_eq M p

theorem cTD_varYtop' (M : Nat) (i : Fin (M + 2)) (hi : i.val = M + 1) :
    chainTotalDeriv (IterExpChain (M + 2)) (MultiPoly.varY i)
      = MultiPoly.mul (Ffac M) (MultiPoly.varY i) := by
  have h : i = (⟨M + 1, by omega⟩ : Fin (M + 2)) := Fin.ext hi
  rw [h]; exact cTD_varYtop M

theorem Ffac_degreeYtop_zero' (M : Nat) (i : Fin (M + 2)) (hi : i.val = M + 1) :
    MultiPoly.degreeY i (Ffac M) = 0 := by
  have h : i = (⟨M + 1, by omega⟩ : Fin (M + 2)) := Fin.ext hi
  rw [h]; exact Ffac_degreeYtop_zero M

/-! ## Make the injection factor opaque

A belt-and-braces measure: even with an abstract index, keep `prodVarYUpTo M` out of `whnf` by
treating `Ffac M` as an atom in this file. (`local`: `Ffac` is imported, so plain `attribute`
cannot set its reducibility here; downstream it reverts to reducible, and the proven theorem's
statement is unaffected.) -/
attribute [local irreducible] MachLib.IterExpTopIdentity.Ffac

/-! ## Small `leadingCoeffY`/`degreeY` helpers (generic in `i`; local copies of the
`IterExpTopIdentity` privates so this file is self-contained). -/

private theorem lcY_varY_self {n : Nat} (i : Fin n) :
    MultiPoly.leadingCoeffY i (MultiPoly.varY i) = MultiPoly.const 1 := by
  show (if i = i then MultiPoly.const 1 else MultiPoly.varY i) = MultiPoly.const 1
  rw [if_pos rfl]

private theorem degreeY_varY_self {n : Nat} (i : Fin n) :
    MultiPoly.degreeY i (MultiPoly.varY i) = 1 := by
  show (if i = i then 1 else 0) = 1
  rw [if_pos rfl]

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

private theorem lcY_sub_of_gt {n : Nat} (i : Fin n) (p q : MultiPoly n)
    (h : MultiPoly.degreeY i q < MultiPoly.degreeY i p) :
    MultiPoly.leadingCoeffY i (MultiPoly.sub p q) = MultiPoly.leadingCoeffY i p := by
  show (if MultiPoly.degreeY i p > MultiPoly.degreeY i q then MultiPoly.leadingCoeffY i p
        else if MultiPoly.degreeY i q > MultiPoly.degreeY i p
             then MultiPoly.sub (MultiPoly.const 0) (MultiPoly.leadingCoeffY i q)
             else MultiPoly.sub (MultiPoly.leadingCoeffY i p) (MultiPoly.leadingCoeffY i q))
       = MultiPoly.leadingCoeffY i p
  rw [if_pos h]

private theorem natCast_add' (a b : Nat) :
    MachLib.Real.natCast (a + b) = MachLib.Real.natCast a + MachLib.Real.natCast b := by
  induction b with
  | zero => rw [Nat.add_zero, MachLib.Real.natCast_zero, MachLib.Real.add_zero]
  | succ n ih =>
    rw [show a + (n + 1) = (a + n) + 1 from rfl, MachLib.Real.natCast_succ,
        MachLib.Real.natCast_succ, ih, MachLib.Real.add_assoc]

/-! ## The generic identity (predicate form), over an abstract top index `i` -/

/-- Frontier-1 lemma (1) at depth `N = M+2`, over an abstract index `i` (the caller supplies
`hi : i.val = M+1`). `F = Ffac M = y₀·…·y_M`. -/
def IdN (M : Nat) (i : Fin (M + 2)) (p : MultiPoly (M + 2)) (x : Real)
    (env : Fin (M + 2) → Real) : Prop :=
    MultiPoly.eval (MultiPoly.leadingCoeffY i (chainTotalDeriv (IterExpChain (M + 2)) p)) x env
    = MultiPoly.eval (chainTotalDeriv (IterExpChain (M + 2)) (MultiPoly.leadingCoeffY i p)) x env
      + MachLib.Real.natCast (MultiPoly.degreeY i p)
        * MultiPoly.eval (MultiPoly.mul (Ffac M) (MultiPoly.leadingCoeffY i p)) x env

/-! ## `add` / `sub` / `mul` inductive steps (abstract `i`; the concrete depth-3 proofs, index-free) -/

set_option maxHeartbeats 1200000 in
theorem idN_add (M : Nat) (i : Fin (M + 2)) (hi : i.val = M + 1)
    (p q : MultiPoly (M + 2)) (x : Real) (env : Fin (M + 2) → Real)
    (ihp : IdN M i p x env) (ihq : IdN M i q x env) : IdN M i (MultiPoly.add p q) x env := by
    unfold IdN at ihp ihq ⊢
    have hp_eq := degreeYtop_cTD_eq' M i hi p
    have hq_eq := degreeYtop_cTD_eq' M i hi q
    rw [cTD_add (IterExpChain (M + 2)) p q]
    rcases Nat.lt_trichotomy (MultiPoly.degreeY i p) (MultiPoly.degreeY i q) with hlt | heq | hgt
    · have hd : MultiPoly.degreeY i (MultiPoly.add p q) = MultiPoly.degreeY i q :=
        Nat.max_eq_right (Nat.le_of_lt hlt)
      rw [lcY_add_of_lt i (chainTotalDeriv (IterExpChain (M + 2)) p)
            (chainTotalDeriv (IterExpChain (M + 2)) q) (by rw [hp_eq, hq_eq]; exact hlt),
          lcY_add_of_lt i p q hlt, hd]
      exact ihq
    · have hd : MultiPoly.degreeY i (MultiPoly.add p q) = MultiPoly.degreeY i q := by
        show Nat.max _ _ = _; rw [heq]; exact Nat.max_self _
      rw [lcY_add_of_eq i (chainTotalDeriv (IterExpChain (M + 2)) p)
            (chainTotalDeriv (IterExpChain (M + 2)) q) (by rw [hp_eq, hq_eq]; exact heq),
          lcY_add_of_eq i p q heq, hd,
          cTD_add (IterExpChain (M + 2))
            (MultiPoly.leadingCoeffY i p) (MultiPoly.leadingCoeffY i q)]
      simp only [MultiPoly.eval_add, MultiPoly.eval_mul] at ihp ihq ⊢
      rw [heq] at ihp
      rw [ihp, ihq]; mach_ring
    · have hd : MultiPoly.degreeY i (MultiPoly.add p q) = MultiPoly.degreeY i p :=
        Nat.max_eq_left (Nat.le_of_lt hgt)
      rw [lcY_add_of_gt i (chainTotalDeriv (IterExpChain (M + 2)) p)
            (chainTotalDeriv (IterExpChain (M + 2)) q) (by rw [hp_eq, hq_eq]; exact hgt),
          lcY_add_of_gt i p q hgt, hd]
      exact ihp

set_option maxHeartbeats 1200000 in
theorem idN_sub (M : Nat) (i : Fin (M + 2)) (hi : i.val = M + 1)
    (p q : MultiPoly (M + 2)) (x : Real) (env : Fin (M + 2) → Real)
    (ihp : IdN M i p x env) (ihq : IdN M i q x env) : IdN M i (MultiPoly.sub p q) x env := by
    unfold IdN at ihp ihq ⊢
    have hp_eq := degreeYtop_cTD_eq' M i hi p
    have hq_eq := degreeYtop_cTD_eq' M i hi q
    rw [cTD_sub (IterExpChain (M + 2)) p q]
    rcases Nat.lt_trichotomy (MultiPoly.degreeY i p) (MultiPoly.degreeY i q) with hlt | heq | hgt
    · have hd : MultiPoly.degreeY i (MultiPoly.sub p q) = MultiPoly.degreeY i q :=
        Nat.max_eq_right (Nat.le_of_lt hlt)
      rw [MultiPoly.leadingCoeffY_sub_of_lt i (chainTotalDeriv (IterExpChain (M + 2)) p)
            (chainTotalDeriv (IterExpChain (M + 2)) q) (by rw [hp_eq, hq_eq]; exact hlt),
          MultiPoly.leadingCoeffY_sub_of_lt i p q hlt, hd,
          cTD_sub_const0 (IterExpChain (M + 2)) (MultiPoly.leadingCoeffY i q)]
      simp only [MultiPoly.eval_sub, MultiPoly.eval_mul, MultiPoly.eval_add, MultiPoly.eval_const]
        at ihp ihq ⊢
      rw [ihq]; mach_ring
    · have hd : MultiPoly.degreeY i (MultiPoly.sub p q) = MultiPoly.degreeY i q := by
        show Nat.max _ _ = _; rw [heq]; exact Nat.max_self _
      rw [MultiPoly.leadingCoeffY_sub_of_eq i (chainTotalDeriv (IterExpChain (M + 2)) p)
            (chainTotalDeriv (IterExpChain (M + 2)) q) (by rw [hp_eq, hq_eq]; exact heq),
          MultiPoly.leadingCoeffY_sub_of_eq i p q heq, hd,
          cTD_sub (IterExpChain (M + 2))
            (MultiPoly.leadingCoeffY i p) (MultiPoly.leadingCoeffY i q)]
      simp only [MultiPoly.eval_sub, MultiPoly.eval_mul, MultiPoly.eval_add] at ihp ihq ⊢
      rw [heq] at ihp
      rw [ihp, ihq]
      generalize MultiPoly.eval (chainTotalDeriv (IterExpChain (M + 2))
          (MultiPoly.leadingCoeffY i p)) x env = A
      generalize MultiPoly.eval (chainTotalDeriv (IterExpChain (M + 2))
          (MultiPoly.leadingCoeffY i q)) x env = B
      generalize MultiPoly.eval (Ffac M) x env = Y
      generalize MultiPoly.eval (MultiPoly.leadingCoeffY i p) x env = LP
      generalize MultiPoly.eval (MultiPoly.leadingCoeffY i q) x env = LQ
      generalize MachLib.Real.natCast (MultiPoly.degreeY i q) = N
      mach_ring
    · have hd : MultiPoly.degreeY i (MultiPoly.sub p q) = MultiPoly.degreeY i p :=
        Nat.max_eq_left (Nat.le_of_lt hgt)
      rw [lcY_sub_of_gt i (chainTotalDeriv (IterExpChain (M + 2)) p)
            (chainTotalDeriv (IterExpChain (M + 2)) q) (by rw [hp_eq, hq_eq]; exact hgt),
          lcY_sub_of_gt i p q hgt, hd]
      exact ihp

set_option maxHeartbeats 1200000 in
theorem idN_mul (M : Nat) (i : Fin (M + 2)) (hi : i.val = M + 1)
    (p q : MultiPoly (M + 2)) (x : Real) (env : Fin (M + 2) → Real)
    (ihp : IdN M i p x env) (ihq : IdN M i q x env) : IdN M i (MultiPoly.mul p q) x env := by
    unfold IdN at ihp ihq ⊢
    have ha_eq := degreeYtop_cTD_eq' M i hi p
    have hb_eq := degreeYtop_cTD_eq' M i hi q
    rw [cTD_mul (IterExpChain (M + 2)) p q]
    have hcond : MultiPoly.degreeY i (MultiPoly.mul (chainTotalDeriv (IterExpChain (M + 2)) p) q)
               = MultiPoly.degreeY i (MultiPoly.mul p (chainTotalDeriv (IterExpChain (M + 2)) q)) := by
      rw [degreeY_mul' i (chainTotalDeriv (IterExpChain (M + 2)) p) q,
          degreeY_mul' i p (chainTotalDeriv (IterExpChain (M + 2)) q), ha_eq, hb_eq]
    rw [lcY_add_of_eq i
          (MultiPoly.mul (chainTotalDeriv (IterExpChain (M + 2)) p) q)
          (MultiPoly.mul p (chainTotalDeriv (IterExpChain (M + 2)) q)) hcond,
        lcY_mul i (chainTotalDeriv (IterExpChain (M + 2)) p) q,
        lcY_mul i p (chainTotalDeriv (IterExpChain (M + 2)) q),
        lcY_mul i p q,
        degreeY_mul' i p q,
        natCast_add',
        cTD_mul (IterExpChain (M + 2)) (MultiPoly.leadingCoeffY i p) (MultiPoly.leadingCoeffY i q)]
    simp only [MultiPoly.eval_add, MultiPoly.eval_mul] at ihp ihq ⊢
    rw [ihp, ihq]
    generalize MultiPoly.eval (chainTotalDeriv (IterExpChain (M + 2))
        (MultiPoly.leadingCoeffY i p)) x env = A
    generalize MultiPoly.eval (chainTotalDeriv (IterExpChain (M + 2))
        (MultiPoly.leadingCoeffY i q)) x env = B
    generalize MultiPoly.eval (Ffac M) x env = Y
    generalize MultiPoly.eval (MultiPoly.leadingCoeffY i p) x env = LA
    generalize MultiPoly.eval (MultiPoly.leadingCoeffY i q) x env = LB
    generalize MachLib.Real.natCast (MultiPoly.degreeY i p) = Na
    generalize MachLib.Real.natCast (MultiPoly.degreeY i q) = Nb
    mach_ring

/-! ## The induction (abstract `i`) -/

/-- The identity for every `p`, over an abstract top index `i` with `hi : i.val = M+1`. The base
cases (`const`/`varX`/`varY`) run cheaply because `i` is atomic; the steps delegate to `idN_add/sub/mul`. -/
theorem idN_general (M : Nat) (i : Fin (M + 2)) (hi : i.val = M + 1)
    (p : MultiPoly (M + 2)) (x : Real) (env : Fin (M + 2) → Real) : IdN M i p x env := by
  induction p with
  | const c =>
    unfold IdN
    rw [cTD_const (IterExpChain (M + 2)) c]
    show MultiPoly.eval (MultiPoly.const 0) x env
        = MultiPoly.eval (chainTotalDeriv (IterExpChain (M + 2)) (MultiPoly.const c)) x env
          + MachLib.Real.natCast 0
            * MultiPoly.eval (MultiPoly.mul (Ffac M) (MultiPoly.const c)) x env
    rw [cTD_const (IterExpChain (M + 2)) c, MachLib.Real.natCast_zero, MultiPoly.eval_const]
    mach_ring
  | varX =>
    unfold IdN
    show MultiPoly.eval (MultiPoly.const 1) x env
        = MultiPoly.eval (chainTotalDeriv (IterExpChain (M + 2)) MultiPoly.varX) x env
          + MachLib.Real.natCast 0
            * MultiPoly.eval (MultiPoly.mul (Ffac M) MultiPoly.varX) x env
    rw [MachLib.Real.natCast_zero, MultiPoly.eval_const]
    show (1 : Real)
        = MultiPoly.eval (MultiPoly.const 1) x env
          + 0 * MultiPoly.eval (MultiPoly.mul (Ffac M) MultiPoly.varX) x env
    rw [MultiPoly.eval_const]; mach_ring
  | varY j =>
    rcases j with ⟨v, hv⟩
    by_cases hji : (⟨v, hv⟩ : Fin (M + 2)) = i
    · -- top variable: cTD(y_i) = Ffac M · y_i; the product-injection base case.
      rw [hji]
      unfold IdN
      rw [cTD_varYtop' M i hi,
          lcY_mul i (Ffac M) (MultiPoly.varY i),
          leadingCoeffY_eq_self_of_degreeY_zero i (Ffac M) (Ffac_degreeYtop_zero' M i hi),
          lcY_varY_self i, degreeY_varY_self i, cTD_const (IterExpChain (M + 2)) 1,
          MachLib.Real.natCast_succ, MachLib.Real.natCast_zero]
      simp only [MultiPoly.eval_mul, MultiPoly.eval_const]
      generalize MultiPoly.eval (Ffac M) x env = Y
      mach_ring
    · -- non-top variable: cTD(y_j) = prodVarYUpTo v (no y_i factor); degreeY i (y_j) = 0.
      unfold IdN
      have hcTD : chainTotalDeriv (IterExpChain (M + 2)) (MultiPoly.varY (⟨v, hv⟩ : Fin (M + 2)))
                = prodVarYUpTo v hv := IterExpChain_relations (M + 2) (⟨v, hv⟩ : Fin (M + 2))
      have hvlt : v < M + 1 := by
        rcases Nat.lt_or_ge v (M + 1) with h | h
        · exact h
        · exact absurd (Fin.ext (show v = i.val by omega) : (⟨v, hv⟩ : Fin (M + 2)) = i) hji
      have hz : MultiPoly.degreeY i (prodVarYUpTo v hv) = 0 :=
        degreeY_prodVarYUpTo_zero_of_lt v hv i (by rw [hi]; omega)
      have hdj : MultiPoly.degreeY i (MultiPoly.varY (⟨v, hv⟩ : Fin (M + 2))) = 0 := by
        show (if i = (⟨v, hv⟩ : Fin (M + 2)) then 1 else 0) = 0
        rw [if_neg (fun h => hji h.symm)]
      rw [hcTD, leadingCoeffY_eq_self_of_degreeY_zero i (prodVarYUpTo v hv) hz, hdj,
          MachLib.Real.natCast_zero,
          leadingCoeffY_eq_self_of_degreeY_zero i (MultiPoly.varY (⟨v, hv⟩ : Fin (M + 2))) hdj,
          hcTD]
      generalize MultiPoly.eval (prodVarYUpTo v hv) x env = P
      mach_ring
  | add p q ihp ihq => exact idN_add M i hi p q x env ihp ihq
  | sub p q ihp ihq => exact idN_sub M i hi p q x env ihp ihq
  | mul p q ihp ihq => exact idN_mul M i hi p q x env ihp ihq

/-! ## The generic identity at the literal top — `∀M`, machine-checked -/

/-- **Frontier-1 lemma (1), for every depth `N = M+2` — PROVEN, `∀M`.**

`eval(lcY_top(cTD p)) = eval(cTD(lcY_top p)) + (degreeY_top p) · eval(Ffac M · lcY_top p)`,
`top = ⟨M+1⟩ : Fin (M+2)`, `Ffac M = y₀·…·y_M`.

`M = 0` is chain-2 (`F = y₀`); `M = 1` is depth-3 (`F = y₀·y₁`); this covers all higher towers. The
product-injection Leibniz step closes exactly as at chain-2 because the identity is *linear* in the
factor `F`. Proven by instantiating the abstract-index `idN_general` at `i := ⟨M+1⟩`, `hi := rfl`. -/
theorem leadingCoeffYtop_cTD_eval_IterExpN (M : Nat) (p : MultiPoly (M + 2)) (x : Real)
    (env : Fin (M + 2) → Real) :
    MultiPoly.eval (MultiPoly.leadingCoeffY (⟨M + 1, by omega⟩ : Fin (M + 2))
        (chainTotalDeriv (IterExpChain (M + 2)) p)) x env
    = MultiPoly.eval (chainTotalDeriv (IterExpChain (M + 2))
        (MultiPoly.leadingCoeffY (⟨M + 1, by omega⟩ : Fin (M + 2)) p)) x env
      + MachLib.Real.natCast (MultiPoly.degreeY (⟨M + 1, by omega⟩ : Fin (M + 2)) p)
        * MultiPoly.eval (MultiPoly.mul (Ffac M)
            (MultiPoly.leadingCoeffY (⟨M + 1, by omega⟩ : Fin (M + 2)) p)) x env := by
  exact idN_general M (⟨M + 1, by omega⟩ : Fin (M + 2)) rfl p x env

end MachLib.IterExpDepthN
