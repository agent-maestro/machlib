import MachLib.ChainExp2SDR
import MachLib.IterExpChain

/-!
# The general `leadingCoeffY`-under-`chainTotalDeriv` identity at the chain TOP, for every depth

This is **Frontier-1 lemma (1)** — the depth-`N` generalization of chain-2's
`ChainExp2LcY1CTD.leadingCoeffY1_cTD_eval_IterExp2`. Parameterized as `MultiPoly (M+2)` over
`IterExpChain (M+2)`, with top index `top = ⟨M+1⟩` and injection factor `F = prodVarYUpTo M`
(= `y₀·y₁·…·y_M`, the top relation `y_{M+1}' = y₀·…·y_{M+1}` with the top variable stripped):

  `eval(lcY_top(cTD p)) = eval(cTD(lcY_top p)) + (degreeY_top p) · eval(F · lcY_top p)`.

`M = 0` recovers chain-2 exactly (`F = y₀`); `M = 1` is the depth-3 double-exponential case
(`F = y₀·y₁`). The key structural fact — confirmed by the depth-3 scope witness — is that in the
Leibniz (`mul`) step the injection factor enters only as a single generalized `eval` atom, so the
"product injection is harder" worry dissolves: the ring closes exactly as at chain-2.

Path B: `ChainExp2SDR` and the single-exp framework are untouched; this is a fresh file. No `sorry`.
-/

namespace MachLib.IterExpTopIdentity

open MachLib.Real
open MachLib.MultiPolyMod
open MachLib.PfaffianChainMod
open MachLib.PfaffianChainMod.PfaffianFn
open MachLib.IterExpChainMod

/-! ## `leadingCoeffY i` of a `degreeY i`-zero poly is the poly itself (local; re-proved for a clean
dependency — the same statement lives in `ChainExp2NoZeros`). -/

private theorem lcY_self_of_degreeY_zero {n : Nat} (i : Fin n) (p : MultiPoly n)
    (hd : MultiPoly.degreeY i p = 0) : MultiPoly.leadingCoeffY i p = p := by
  induction p with
  | const c => rfl
  | varX => rfl
  | varY j =>
    show (if j = i then MultiPoly.const 1 else MultiPoly.varY j) = MultiPoly.varY j
    have hji : j ≠ i := by
      intro h; subst h
      simp [MultiPoly.degreeY] at hd
    rw [if_neg hji]
  | add p q ihp ihq =>
    have hle : MultiPoly.degreeY i p ≤ Nat.max (MultiPoly.degreeY i p) (MultiPoly.degreeY i q) :=
      Nat.le_max_left _ _
    have hp : MultiPoly.degreeY i p = 0 := by
      have : MultiPoly.degreeY i (MultiPoly.add p q) = Nat.max (MultiPoly.degreeY i p) (MultiPoly.degreeY i q) := rfl
      omega
    have hq : MultiPoly.degreeY i q = 0 := by
      have hle2 : MultiPoly.degreeY i q ≤ Nat.max (MultiPoly.degreeY i p) (MultiPoly.degreeY i q) :=
        Nat.le_max_right _ _
      have : MultiPoly.degreeY i (MultiPoly.add p q) = Nat.max (MultiPoly.degreeY i p) (MultiPoly.degreeY i q) := rfl
      omega
    show (if MultiPoly.degreeY i p > MultiPoly.degreeY i q then MultiPoly.leadingCoeffY i p
          else if MultiPoly.degreeY i q > MultiPoly.degreeY i p then MultiPoly.leadingCoeffY i q
          else MultiPoly.add (MultiPoly.leadingCoeffY i p) (MultiPoly.leadingCoeffY i q))
         = MultiPoly.add p q
    rw [if_neg (by rw [hp, hq]; exact Nat.lt_irrefl 0),
        if_neg (by rw [hp, hq]; exact Nat.lt_irrefl 0), ihp hp, ihq hq]
  | sub p q ihp ihq =>
    have hp : MultiPoly.degreeY i p = 0 := by
      have hle : MultiPoly.degreeY i p ≤ Nat.max (MultiPoly.degreeY i p) (MultiPoly.degreeY i q) :=
        Nat.le_max_left _ _
      have : MultiPoly.degreeY i (MultiPoly.sub p q) = Nat.max (MultiPoly.degreeY i p) (MultiPoly.degreeY i q) := rfl
      omega
    have hq : MultiPoly.degreeY i q = 0 := by
      have hle : MultiPoly.degreeY i q ≤ Nat.max (MultiPoly.degreeY i p) (MultiPoly.degreeY i q) :=
        Nat.le_max_right _ _
      have : MultiPoly.degreeY i (MultiPoly.sub p q) = Nat.max (MultiPoly.degreeY i p) (MultiPoly.degreeY i q) := rfl
      omega
    show (if MultiPoly.degreeY i p > MultiPoly.degreeY i q then MultiPoly.leadingCoeffY i p
          else if MultiPoly.degreeY i q > MultiPoly.degreeY i p
               then MultiPoly.sub (MultiPoly.const 0) (MultiPoly.leadingCoeffY i q)
               else MultiPoly.sub (MultiPoly.leadingCoeffY i p) (MultiPoly.leadingCoeffY i q))
         = MultiPoly.sub p q
    rw [if_neg (by rw [hp, hq]; exact Nat.lt_irrefl 0),
        if_neg (by rw [hp, hq]; exact Nat.lt_irrefl 0), ihp hp, ihq hq]
  | mul p q ihp ihq =>
    have hp : MultiPoly.degreeY i p = 0 := by
      have : MultiPoly.degreeY i (MultiPoly.mul p q)
           = MultiPoly.degreeY i p + MultiPoly.degreeY i q := rfl
      omega
    have hq : MultiPoly.degreeY i q = 0 := by
      have : MultiPoly.degreeY i (MultiPoly.mul p q)
           = MultiPoly.degreeY i p + MultiPoly.degreeY i q := rfl
      omega
    show MultiPoly.mul (MultiPoly.leadingCoeffY i p) (MultiPoly.leadingCoeffY i q)
       = MultiPoly.mul p q
    rw [ihp hp, ihq hq]

/-! ## Top chain-variable degree is preserved by `chainTotalDeriv` (any depth) -/

/-- The top y-degree `⟨M+1⟩` is unchanged by `chainTotalDeriv (IterExpChain (M+2))`. Generic-`M`
analog of `degreeY1_chainTotalDeriv_eq_IterExp2`. Only the `varY` case differs from chain-2: for a
generic index `j` we split on `j = top` (both degrees 1, via `prodVarYUpTo (M+1) = F · y_top`) vs
`j ≠ top` (both 0, via triangularity `degreeY_prodVarYUpTo_zero_of_lt`). -/
theorem degreeYtop_cTD_eq (M : Nat) (p : MultiPoly (M + 2)) :
    MultiPoly.degreeY (⟨M + 1, by omega⟩ : Fin (M + 2)) (chainTotalDeriv (IterExpChain (M + 2)) p)
      = MultiPoly.degreeY (⟨M + 1, by omega⟩ : Fin (M + 2)) p := by
  induction p with
  | const c => rfl
  | varX => rfl
  | varY j =>
    rcases j with ⟨jv, jlt⟩
    show MultiPoly.degreeY (⟨M + 1, by omega⟩ : Fin (M + 2))
           (prodVarYUpTo jv jlt : MultiPoly (M + 2))
       = MultiPoly.degreeY (⟨M + 1, by omega⟩ : Fin (M + 2))
           (MultiPoly.varY (⟨jv, jlt⟩ : Fin (M + 2)))
    by_cases hj : jv = M + 1
    · -- j = top: LHS degreeY_top(prodVarYUpTo (M+1)) = 1, RHS degreeY_top(varY top) = 1.
      subst hj
      rw [prodVarYUpTo_succ M jlt]
      show MultiPoly.degreeY (⟨M + 1, by omega⟩ : Fin (M + 2))
             (prodVarYUpTo M (Nat.lt_of_succ_lt jlt))
           + MultiPoly.degreeY (⟨M + 1, by omega⟩ : Fin (M + 2))
               (MultiPoly.varY (⟨M + 1, jlt⟩ : Fin (M + 2)))
         = MultiPoly.degreeY (⟨M + 1, by omega⟩ : Fin (M + 2))
             (MultiPoly.varY (⟨M + 1, jlt⟩ : Fin (M + 2)))
      rw [degreeY_prodVarYUpTo_zero_of_lt M (Nat.lt_of_succ_lt jlt)
            (⟨M + 1, by omega⟩ : Fin (M + 2)) (by show M + 1 > M; omega), Nat.zero_add]
    · -- j ≠ top: LHS 0 (triangularity), RHS 0 (degreeY_top(varY j) = 0, j ≠ top).
      have hjlt : jv < M + 1 := by omega
      rw [degreeY_prodVarYUpTo_zero_of_lt jv jlt (⟨M + 1, by omega⟩ : Fin (M + 2))
            (by show M + 1 > jv; omega)]
      show 0 = (if (⟨M + 1, by omega⟩ : Fin (M + 2)) = (⟨jv, jlt⟩ : Fin (M + 2)) then 1 else 0)
      rw [if_neg (by intro h; rw [Fin.mk.injEq] at h; omega)]
  | add p q ihp ihq =>
    show Nat.max (MultiPoly.degreeY (⟨M + 1, by omega⟩ : Fin (M + 2))
                   (chainTotalDeriv (IterExpChain (M + 2)) p))
                 (MultiPoly.degreeY (⟨M + 1, by omega⟩ : Fin (M + 2))
                   (chainTotalDeriv (IterExpChain (M + 2)) q))
       = Nat.max (MultiPoly.degreeY (⟨M + 1, by omega⟩ : Fin (M + 2)) p)
                 (MultiPoly.degreeY (⟨M + 1, by omega⟩ : Fin (M + 2)) q)
    rw [ihp, ihq]
  | sub p q ihp ihq =>
    show Nat.max (MultiPoly.degreeY (⟨M + 1, by omega⟩ : Fin (M + 2))
                   (chainTotalDeriv (IterExpChain (M + 2)) p))
                 (MultiPoly.degreeY (⟨M + 1, by omega⟩ : Fin (M + 2))
                   (chainTotalDeriv (IterExpChain (M + 2)) q))
       = Nat.max (MultiPoly.degreeY (⟨M + 1, by omega⟩ : Fin (M + 2)) p)
                 (MultiPoly.degreeY (⟨M + 1, by omega⟩ : Fin (M + 2)) q)
    rw [ihp, ihq]
  | mul p q ihp ihq =>
    show Nat.max (MultiPoly.degreeY (⟨M + 1, by omega⟩ : Fin (M + 2))
                   (chainTotalDeriv (IterExpChain (M + 2)) p)
                  + MultiPoly.degreeY (⟨M + 1, by omega⟩ : Fin (M + 2)) q)
                 (MultiPoly.degreeY (⟨M + 1, by omega⟩ : Fin (M + 2)) p
                  + MultiPoly.degreeY (⟨M + 1, by omega⟩ : Fin (M + 2))
                      (chainTotalDeriv (IterExpChain (M + 2)) q))
       = MultiPoly.degreeY (⟨M + 1, by omega⟩ : Fin (M + 2)) p
           + MultiPoly.degreeY (⟨M + 1, by omega⟩ : Fin (M + 2)) q
    rw [ihp, ihq]; exact Nat.max_self _

/-! ## The injection factor `F = prodVarYUpTo M` (as a `def` so `mach_ring` sees one atom) -/

/-- The injection factor `F = y₀·y₁·…·y_M : MultiPoly (M+2)` — the top relation with the top
variable stripped (`y_{M+1}' = F · y_{M+1}`). -/
noncomputable def Ffac (M : Nat) : MultiPoly (M + 2) := prodVarYUpTo M (by omega)

theorem Ffac_degreeYtop_zero (M : Nat) :
    MultiPoly.degreeY (⟨M + 1, by omega⟩ : Fin (M + 2)) (Ffac M) = 0 := by
  show MultiPoly.degreeY (⟨M + 1, by omega⟩ : Fin (M + 2)) (prodVarYUpTo M (by omega)) = 0
  exact degreeY_prodVarYUpTo_zero_of_lt M (by omega) (⟨M + 1, by omega⟩ : Fin (M + 2))
    (by show M + 1 > M; omega)

/-- `cTD(y_top) = F · y_top` (the top relation), stated with `Ffac`. -/
theorem cTD_varYtop (M : Nat) :
    chainTotalDeriv (IterExpChain (M + 2)) (MultiPoly.varY (⟨M + 1, by omega⟩ : Fin (M + 2)))
      = MultiPoly.mul (Ffac M) (MultiPoly.varY (⟨M + 1, by omega⟩ : Fin (M + 2))) := by
  show (prodVarYUpTo (M + 1) (by omega) : MultiPoly (M + 2))
     = MultiPoly.mul (Ffac M) (MultiPoly.varY (⟨M + 1, by omega⟩ : Fin (M + 2)))
  rw [prodVarYUpTo_succ M (by omega)]
  rfl

/-! ## `leadingCoeffY`/`degreeY` at the self-index (needs `if_pos rfl`; doesn't reduce for variable `M`) -/

private theorem lcY_varY_self {n : Nat} (i : Fin n) :
    MultiPoly.leadingCoeffY i (MultiPoly.varY i) = MultiPoly.const 1 := by
  show (if i = i then MultiPoly.const 1 else MultiPoly.varY i) = MultiPoly.const 1
  rw [if_pos rfl]

private theorem degreeY_varY_self {n : Nat} (i : Fin n) :
    MultiPoly.degreeY i (MultiPoly.varY i) = 1 := by
  show (if i = i then 1 else 0) = 1
  rw [if_pos rfl]

/-! ## `leadingCoeffY`-of-`add`/`sub` helpers (generic; copies of the chain-2 privates) -/

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

/-! ## Structural `rfl` lemmas (proven once, on small terms, so the case proofs use cheap keyed `rw`
instead of expensive `show … from rfl` defeq — which blows up / OOMs at variable `M`). -/

theorem cTD_const {n : Nat} (chain : PfaffianChain n) (c : Real) :
    chainTotalDeriv chain (MultiPoly.const c) = MultiPoly.const 0 := rfl
theorem cTD_add {n : Nat} (chain : PfaffianChain n) (p q : MultiPoly n) :
    chainTotalDeriv chain (MultiPoly.add p q)
      = MultiPoly.add (chainTotalDeriv chain p) (chainTotalDeriv chain q) := rfl
theorem cTD_sub {n : Nat} (chain : PfaffianChain n) (p q : MultiPoly n) :
    chainTotalDeriv chain (MultiPoly.sub p q)
      = MultiPoly.sub (chainTotalDeriv chain p) (chainTotalDeriv chain q) := rfl
theorem cTD_sub_const0 {n : Nat} (chain : PfaffianChain n) (q : MultiPoly n) :
    chainTotalDeriv chain (MultiPoly.sub (MultiPoly.const 0) q)
      = MultiPoly.sub (MultiPoly.const 0) (chainTotalDeriv chain q) := rfl
theorem cTD_mul {n : Nat} (chain : PfaffianChain n) (p q : MultiPoly n) :
    chainTotalDeriv chain (MultiPoly.mul p q)
      = MultiPoly.add (MultiPoly.mul (chainTotalDeriv chain p) q)
                      (MultiPoly.mul p (chainTotalDeriv chain q)) := rfl
theorem lcY_mul {n : Nat} (i : Fin n) (a b : MultiPoly n) :
    MultiPoly.leadingCoeffY i (MultiPoly.mul a b)
      = MultiPoly.mul (MultiPoly.leadingCoeffY i a) (MultiPoly.leadingCoeffY i b) := rfl
theorem degreeY_mul' {n : Nat} (i : Fin n) (a b : MultiPoly n) :
    MultiPoly.degreeY i (MultiPoly.mul a b)
      = MultiPoly.degreeY i a + MultiPoly.degreeY i b := rfl

/-! ## Depth-3 concrete instance (M = 1): lemma (1) for the double-exponential chain

The generic `∀M` proof is logically identical but hits a Lean `rw`/`whnf` performance wall at *variable*
`M` (kabstract defeq over the non-reducing `prodVarYUpTo M` diverges). At the concrete depth-3
(`MultiPoly 3`, `IterExpChain 3`, top `⟨2⟩`, factor `F₃ = y₀·y₁`) every term reduces, so the proof
compiles like the chain-2 original. This is the go/no-go instance for the depth-N frontier: it proves
the product-injection Leibniz step closes exactly as at chain-2. -/

/-- Top `y₂`-degree preserved by `cTD` at depth 3. -/
theorem degreeY2_cTD_eq_IterExp3 (p : MultiPoly 3) :
    MultiPoly.degreeY (⟨2, by omega⟩ : Fin 3) (chainTotalDeriv (IterExpChain 3) p)
      = MultiPoly.degreeY (⟨2, by omega⟩ : Fin 3) p := by
  induction p with
  | const c => rfl
  | varX => rfl
  | varY j =>
    rcases j with ⟨v, hv⟩
    match v, hv with
    | 0, _ => rfl
    | 1, _ => rfl
    | 2, _ => rfl
  | add p q ihp ihq =>
    show Nat.max (MultiPoly.degreeY (⟨2, by omega⟩ : Fin 3) (chainTotalDeriv (IterExpChain 3) p))
                 (MultiPoly.degreeY (⟨2, by omega⟩ : Fin 3) (chainTotalDeriv (IterExpChain 3) q))
       = Nat.max (MultiPoly.degreeY (⟨2, by omega⟩ : Fin 3) p)
                 (MultiPoly.degreeY (⟨2, by omega⟩ : Fin 3) q)
    rw [ihp, ihq]
  | sub p q ihp ihq =>
    show Nat.max (MultiPoly.degreeY (⟨2, by omega⟩ : Fin 3) (chainTotalDeriv (IterExpChain 3) p))
                 (MultiPoly.degreeY (⟨2, by omega⟩ : Fin 3) (chainTotalDeriv (IterExpChain 3) q))
       = Nat.max (MultiPoly.degreeY (⟨2, by omega⟩ : Fin 3) p)
                 (MultiPoly.degreeY (⟨2, by omega⟩ : Fin 3) q)
    rw [ihp, ihq]
  | mul p q ihp ihq =>
    show Nat.max (MultiPoly.degreeY (⟨2, by omega⟩ : Fin 3) (chainTotalDeriv (IterExpChain 3) p)
                  + MultiPoly.degreeY (⟨2, by omega⟩ : Fin 3) q)
                 (MultiPoly.degreeY (⟨2, by omega⟩ : Fin 3) p
                  + MultiPoly.degreeY (⟨2, by omega⟩ : Fin 3) (chainTotalDeriv (IterExpChain 3) q))
       = MultiPoly.degreeY (⟨2, by omega⟩ : Fin 3) p + MultiPoly.degreeY (⟨2, by omega⟩ : Fin 3) q
    rw [ihp, ihq]; exact Nat.max_self _

/-- The depth-3 identity statement (predicate form): `F₃ = y₀·y₁`. -/
def Id3 (p : MultiPoly 3) (x : Real) (env : Fin 3 → Real) : Prop :=
    MultiPoly.eval (MultiPoly.leadingCoeffY (⟨2, by omega⟩ : Fin 3)
        (chainTotalDeriv (IterExpChain 3) p)) x env
    = MultiPoly.eval (chainTotalDeriv (IterExpChain 3)
        (MultiPoly.leadingCoeffY (⟨2, by omega⟩ : Fin 3) p)) x env
      + MachLib.Real.natCast (MultiPoly.degreeY (⟨2, by omega⟩ : Fin 3) p)
        * MultiPoly.eval (MultiPoly.mul
            (MultiPoly.mul (MultiPoly.varY (⟨0, by omega⟩ : Fin 3))
                           (MultiPoly.varY (⟨1, by omega⟩ : Fin 3)))
            (MultiPoly.leadingCoeffY (⟨2, by omega⟩ : Fin 3) p)) x env

set_option maxHeartbeats 800000 in
theorem id3_add (p q : MultiPoly 3) (x : Real) (env : Fin 3 → Real)
    (ihp : Id3 p x env) (ihq : Id3 q x env) : Id3 (MultiPoly.add p q) x env := by
    unfold Id3 at ihp ihq ⊢
    have hp_eq := degreeY2_cTD_eq_IterExp3 p
    have hq_eq := degreeY2_cTD_eq_IterExp3 q
    rw [cTD_add (IterExpChain 3) p q]
    rcases Nat.lt_trichotomy (MultiPoly.degreeY (⟨2, by omega⟩ : Fin 3) p)
                             (MultiPoly.degreeY (⟨2, by omega⟩ : Fin 3) q) with hlt | heq | hgt
    · have hd : MultiPoly.degreeY (⟨2, by omega⟩ : Fin 3) (MultiPoly.add p q)
              = MultiPoly.degreeY (⟨2, by omega⟩ : Fin 3) q := Nat.max_eq_right (Nat.le_of_lt hlt)
      rw [lcY_add_of_lt (⟨2, by omega⟩ : Fin 3) (chainTotalDeriv (IterExpChain 3) p)
            (chainTotalDeriv (IterExpChain 3) q) (by rw [hp_eq, hq_eq]; exact hlt),
          lcY_add_of_lt (⟨2, by omega⟩ : Fin 3) p q hlt, hd]
      exact ihq
    · have hd : MultiPoly.degreeY (⟨2, by omega⟩ : Fin 3) (MultiPoly.add p q)
              = MultiPoly.degreeY (⟨2, by omega⟩ : Fin 3) q := by
        show Nat.max _ _ = _; rw [heq]; exact Nat.max_self _
      rw [lcY_add_of_eq (⟨2, by omega⟩ : Fin 3) (chainTotalDeriv (IterExpChain 3) p)
            (chainTotalDeriv (IterExpChain 3) q) (by rw [hp_eq, hq_eq]; exact heq),
          lcY_add_of_eq (⟨2, by omega⟩ : Fin 3) p q heq, hd,
          cTD_add (IterExpChain 3)
            (MultiPoly.leadingCoeffY (⟨2, by omega⟩ : Fin 3) p)
            (MultiPoly.leadingCoeffY (⟨2, by omega⟩ : Fin 3) q)]
      simp only [MultiPoly.eval_add, MultiPoly.eval_mul] at ihp ihq ⊢
      rw [heq] at ihp
      rw [ihp, ihq]; mach_ring
    · have hd : MultiPoly.degreeY (⟨2, by omega⟩ : Fin 3) (MultiPoly.add p q)
              = MultiPoly.degreeY (⟨2, by omega⟩ : Fin 3) p := Nat.max_eq_left (Nat.le_of_lt hgt)
      rw [lcY_add_of_gt (⟨2, by omega⟩ : Fin 3) (chainTotalDeriv (IterExpChain 3) p)
            (chainTotalDeriv (IterExpChain 3) q) (by rw [hp_eq, hq_eq]; exact hgt),
          lcY_add_of_gt (⟨2, by omega⟩ : Fin 3) p q hgt, hd]
      exact ihp

set_option maxHeartbeats 800000 in
theorem id3_sub (p q : MultiPoly 3) (x : Real) (env : Fin 3 → Real)
    (ihp : Id3 p x env) (ihq : Id3 q x env) : Id3 (MultiPoly.sub p q) x env := by
    unfold Id3 at ihp ihq ⊢
    have hp_eq := degreeY2_cTD_eq_IterExp3 p
    have hq_eq := degreeY2_cTD_eq_IterExp3 q
    rw [cTD_sub (IterExpChain 3) p q]
    rcases Nat.lt_trichotomy (MultiPoly.degreeY (⟨2, by omega⟩ : Fin 3) p)
                             (MultiPoly.degreeY (⟨2, by omega⟩ : Fin 3) q) with hlt | heq | hgt
    · have hd : MultiPoly.degreeY (⟨2, by omega⟩ : Fin 3) (MultiPoly.sub p q)
              = MultiPoly.degreeY (⟨2, by omega⟩ : Fin 3) q := Nat.max_eq_right (Nat.le_of_lt hlt)
      rw [MultiPoly.leadingCoeffY_sub_of_lt (⟨2, by omega⟩ : Fin 3)
            (chainTotalDeriv (IterExpChain 3) p) (chainTotalDeriv (IterExpChain 3) q)
            (by rw [hp_eq, hq_eq]; exact hlt),
          MultiPoly.leadingCoeffY_sub_of_lt (⟨2, by omega⟩ : Fin 3) p q hlt, hd,
          cTD_sub_const0 (IterExpChain 3)
            (MultiPoly.leadingCoeffY (⟨2, by omega⟩ : Fin 3) q)]
      simp only [MultiPoly.eval_sub, MultiPoly.eval_mul, MultiPoly.eval_add, MultiPoly.eval_const]
        at ihp ihq ⊢
      rw [ihq]; mach_ring
    · have hd : MultiPoly.degreeY (⟨2, by omega⟩ : Fin 3) (MultiPoly.sub p q)
              = MultiPoly.degreeY (⟨2, by omega⟩ : Fin 3) q := by
        show Nat.max _ _ = _; rw [heq]; exact Nat.max_self _
      rw [MultiPoly.leadingCoeffY_sub_of_eq (⟨2, by omega⟩ : Fin 3)
            (chainTotalDeriv (IterExpChain 3) p) (chainTotalDeriv (IterExpChain 3) q)
            (by rw [hp_eq, hq_eq]; exact heq),
          MultiPoly.leadingCoeffY_sub_of_eq (⟨2, by omega⟩ : Fin 3) p q heq, hd,
          cTD_sub (IterExpChain 3)
            (MultiPoly.leadingCoeffY (⟨2, by omega⟩ : Fin 3) p)
            (MultiPoly.leadingCoeffY (⟨2, by omega⟩ : Fin 3) q)]
      simp only [MultiPoly.eval_sub, MultiPoly.eval_mul, MultiPoly.eval_add] at ihp ihq ⊢
      rw [heq] at ihp
      rw [ihp, ihq]
      generalize MultiPoly.eval (chainTotalDeriv (IterExpChain 3)
          (MultiPoly.leadingCoeffY (⟨2, by omega⟩ : Fin 3) p)) x env = A
      generalize MultiPoly.eval (chainTotalDeriv (IterExpChain 3)
          (MultiPoly.leadingCoeffY (⟨2, by omega⟩ : Fin 3) q)) x env = B
      generalize MultiPoly.eval (MultiPoly.mul (MultiPoly.varY (⟨0, by omega⟩ : Fin 3))
          (MultiPoly.varY (⟨1, by omega⟩ : Fin 3))) x env = Y
      generalize MultiPoly.eval (MultiPoly.leadingCoeffY (⟨2, by omega⟩ : Fin 3) p) x env = LP
      generalize MultiPoly.eval (MultiPoly.leadingCoeffY (⟨2, by omega⟩ : Fin 3) q) x env = LQ
      generalize MachLib.Real.natCast (MultiPoly.degreeY (⟨2, by omega⟩ : Fin 3) q) = N
      mach_ring
    · have hd : MultiPoly.degreeY (⟨2, by omega⟩ : Fin 3) (MultiPoly.sub p q)
              = MultiPoly.degreeY (⟨2, by omega⟩ : Fin 3) p := Nat.max_eq_left (Nat.le_of_lt hgt)
      rw [lcY_sub_of_gt (⟨2, by omega⟩ : Fin 3) (chainTotalDeriv (IterExpChain 3) p)
            (chainTotalDeriv (IterExpChain 3) q) (by rw [hp_eq, hq_eq]; exact hgt),
          lcY_sub_of_gt (⟨2, by omega⟩ : Fin 3) p q hgt, hd]
      exact ihp

set_option maxHeartbeats 800000 in
theorem id3_mul (p q : MultiPoly 3) (x : Real) (env : Fin 3 → Real)
    (ihp : Id3 p x env) (ihq : Id3 q x env) : Id3 (MultiPoly.mul p q) x env := by
    unfold Id3 at ihp ihq ⊢
    have ha_eq := degreeY2_cTD_eq_IterExp3 p
    have hb_eq := degreeY2_cTD_eq_IterExp3 q
    rw [cTD_mul (IterExpChain 3) p q]
    have hcond : MultiPoly.degreeY (⟨2, by omega⟩ : Fin 3)
                   (MultiPoly.mul (chainTotalDeriv (IterExpChain 3) p) q)
               = MultiPoly.degreeY (⟨2, by omega⟩ : Fin 3)
                   (MultiPoly.mul p (chainTotalDeriv (IterExpChain 3) q)) := by
      show MultiPoly.degreeY (⟨2, by omega⟩ : Fin 3) (chainTotalDeriv (IterExpChain 3) p)
             + MultiPoly.degreeY (⟨2, by omega⟩ : Fin 3) q
         = MultiPoly.degreeY (⟨2, by omega⟩ : Fin 3) p
             + MultiPoly.degreeY (⟨2, by omega⟩ : Fin 3) (chainTotalDeriv (IterExpChain 3) q)
      rw [ha_eq, hb_eq]
    rw [lcY_add_of_eq (⟨2, by omega⟩ : Fin 3)
          (MultiPoly.mul (chainTotalDeriv (IterExpChain 3) p) q)
          (MultiPoly.mul p (chainTotalDeriv (IterExpChain 3) q)) hcond,
        lcY_mul (⟨2, by omega⟩ : Fin 3) (chainTotalDeriv (IterExpChain 3) p) q,
        lcY_mul (⟨2, by omega⟩ : Fin 3) p (chainTotalDeriv (IterExpChain 3) q),
        lcY_mul (⟨2, by omega⟩ : Fin 3) p q,
        degreeY_mul' (⟨2, by omega⟩ : Fin 3) p q,
        natCast_add',
        cTD_mul (IterExpChain 3)
          (MultiPoly.leadingCoeffY (⟨2, by omega⟩ : Fin 3) p)
          (MultiPoly.leadingCoeffY (⟨2, by omega⟩ : Fin 3) q)]
    simp only [MultiPoly.eval_add, MultiPoly.eval_mul] at ihp ihq ⊢
    rw [ihp, ihq]
    generalize MultiPoly.eval (chainTotalDeriv (IterExpChain 3)
        (MultiPoly.leadingCoeffY (⟨2, by omega⟩ : Fin 3) p)) x env = A
    generalize MultiPoly.eval (chainTotalDeriv (IterExpChain 3)
        (MultiPoly.leadingCoeffY (⟨2, by omega⟩ : Fin 3) q)) x env = B
    generalize MultiPoly.eval (MultiPoly.mul (MultiPoly.varY (⟨0, by omega⟩ : Fin 3))
        (MultiPoly.varY (⟨1, by omega⟩ : Fin 3))) x env = Y
    generalize MultiPoly.eval (MultiPoly.leadingCoeffY (⟨2, by omega⟩ : Fin 3) p) x env = LA
    generalize MultiPoly.eval (MultiPoly.leadingCoeffY (⟨2, by omega⟩ : Fin 3) q) x env = LB
    generalize MachLib.Real.natCast (MultiPoly.degreeY (⟨2, by omega⟩ : Fin 3) p) = Na
    generalize MachLib.Real.natCast (MultiPoly.degreeY (⟨2, by omega⟩ : Fin 3) q) = Nb
    mach_ring

/-- **Frontier-1 lemma (1), depth-3 (M=1) — PROVEN.** `eval(lcY₂(cTD p)) = eval(cTD(lcY₂ p)) +
(degreeY₂ p)·eval(y₀·y₁·lcY₂ p)`. The product injection `y₀·y₁` (vs chain-2's single `y₀`) closes the
Leibniz step identically — the depth-N recursion's one genuinely uncertain algebraic step, now verified. -/
theorem leadingCoeffY2_cTD_eval_IterExp3 (p : MultiPoly 3) (x : Real) (env : Fin 3 → Real) :
    MultiPoly.eval (MultiPoly.leadingCoeffY (⟨2, by omega⟩ : Fin 3)
        (chainTotalDeriv (IterExpChain 3) p)) x env
    = MultiPoly.eval (chainTotalDeriv (IterExpChain 3)
        (MultiPoly.leadingCoeffY (⟨2, by omega⟩ : Fin 3) p)) x env
      + MachLib.Real.natCast (MultiPoly.degreeY (⟨2, by omega⟩ : Fin 3) p)
        * MultiPoly.eval (MultiPoly.mul
            (MultiPoly.mul (MultiPoly.varY (⟨0, by omega⟩ : Fin 3))
                           (MultiPoly.varY (⟨1, by omega⟩ : Fin 3)))
            (MultiPoly.leadingCoeffY (⟨2, by omega⟩ : Fin 3) p)) x env := by
  show Id3 p x env
  induction p with
  | const c =>
    show (0 : Real) = 0 + MachLib.Real.natCast 0
        * MultiPoly.eval (MultiPoly.mul (MultiPoly.mul (MultiPoly.varY (⟨0, by omega⟩ : Fin 3))
            (MultiPoly.varY (⟨1, by omega⟩ : Fin 3))) (MultiPoly.const c)) x env
    rw [MachLib.Real.natCast_zero]; mach_ring
  | varX =>
    show (1 : Real) = 1 + MachLib.Real.natCast 0
        * MultiPoly.eval (MultiPoly.mul (MultiPoly.mul (MultiPoly.varY (⟨0, by omega⟩ : Fin 3))
            (MultiPoly.varY (⟨1, by omega⟩ : Fin 3))) MultiPoly.varX) x env
    rw [MachLib.Real.natCast_zero]; mach_ring
  | varY j =>
    rcases j with ⟨v, hv⟩
    match v, hv with
    | 0, _ =>
      show env (⟨0, by omega⟩ : Fin 3)
          = env (⟨0, by omega⟩ : Fin 3) + MachLib.Real.natCast 0
            * ((env (⟨0, by omega⟩ : Fin 3) * env (⟨1, by omega⟩ : Fin 3))
               * env (⟨0, by omega⟩ : Fin 3))
      rw [MachLib.Real.natCast_zero]; mach_ring
    | 1, _ =>
      show env (⟨0, by omega⟩ : Fin 3) * env (⟨1, by omega⟩ : Fin 3)
          = env (⟨0, by omega⟩ : Fin 3) * env (⟨1, by omega⟩ : Fin 3) + MachLib.Real.natCast 0
            * ((env (⟨0, by omega⟩ : Fin 3) * env (⟨1, by omega⟩ : Fin 3))
               * env (⟨1, by omega⟩ : Fin 3))
      rw [MachLib.Real.natCast_zero]; mach_ring
    | 2, _ =>
      show (env (⟨0, by omega⟩ : Fin 3) * env (⟨1, by omega⟩ : Fin 3)) * (1 : Real)
          = 0 + MachLib.Real.natCast 1
            * ((env (⟨0, by omega⟩ : Fin 3) * env (⟨1, by omega⟩ : Fin 3)) * (1 : Real))
      rw [MachLib.Real.natCast_succ, MachLib.Real.natCast_zero]; mach_ring
  | add p q ihp ihq => exact id3_add p q x env ihp ihq
  | sub p q ihp ihq => exact id3_sub p q x env ihp ihq
  | mul p q ihp ihq => exact id3_mul p q x env ihp ihq

end MachLib.IterExpTopIdentity
