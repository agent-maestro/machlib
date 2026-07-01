import MachLib.ChainExp2LcY1CTD

/-!
# The `leadingCoeffY₀`-under-`cTD` identity for `y₁`-free `MultiPoly 2` (the descent's algebraic core)

The single-exp canonical descent needs to compute the `y₀`-leading coefficient of the reduce
`reduceSE c q = cTD₂ q − c·q` for `q = lcY₁ p` (a `y₁`-free object). That rests on the `y₀`-analog of the
`y₁`-identity:

  `eval(lcY₀(cTD₂ q)) x env = eval(cTD₂(lcY₀ q)) x env + (degreeY₀ q) · eval(lcY₀ q) x env`   (`y₁`-free `q`).

The injection is `d·lcY₀` — NO `y₀` factor (unlike `y₁`'s `d·y₀·lcY₁`), because `y₀' = y₀` contributes a
factor of `1`, not `y₀`. It holds only for `y₁`-free `q` (it FAILS on `varY 1`: `cTD₂(y₁) = y₀·y₁` injects
`y₀`), so every case carries `degreeY₁ q = 0`.

Built case by case, mirroring `ChainExp2LcY1CTD`. Foundations untouched (Path B).
-/

namespace MachLib.ChainExp2LcY0CTD

open MachLib.Real
open MachLib.MultiPolyMod
open MachLib.PfaffianChainMod
open MachLib.PfaffianChainMod.PfaffianFn
open MachLib.IterExpChainMod
open MachLib.ChainExp2SDR

/-- Extract `degreeY₁ a = 0` from `degreeY₁ (add a b) = 0` (`Nat.max`). -/
private theorem degY1_add_left {a b : MultiPoly 2}
    (h : MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) (MultiPoly.add a b) = 0) :
    MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) a = 0 := by
  have h' : Nat.max (MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) a)
                    (MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) b) = 0 := h
  have hle : MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) a
           ≤ Nat.max (MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) a)
                     (MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) b) := Nat.le_max_left _ _
  omega

private theorem degY1_add_right {a b : MultiPoly 2}
    (h : MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) (MultiPoly.add a b) = 0) :
    MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) b = 0 := by
  have h' : Nat.max (MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) a)
                    (MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) b) = 0 := h
  have hle : MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) b
           ≤ Nat.max (MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) a)
                     (MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) b) := Nat.le_max_right _ _
  omega

/-- **`degreeY₀` preserved by `cTD₂` on `y₁`-free polys** (the `y₀`-analog of
`degreeY1_chainTotalDeriv_eq_IterExp2`, conditional on `degreeY₁ q = 0` since it fails on `varY 1`). -/
theorem degreeY0_cTD_eq_of_y1free (q : MultiPoly 2) :
    MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) q = 0 →
    MultiPoly.degreeY (⟨0, by omega⟩ : Fin 2) (chainTotalDeriv (IterExpChain 2) q)
      = MultiPoly.degreeY (⟨0, by omega⟩ : Fin 2) q := by
  induction q with
  | const c => intro _; rfl
  | varX => intro _; rfl
  | varY j =>
    intro hy1
    rcases j with ⟨v, hv⟩
    match v, hv with
    | 0, _ => rfl
    | 1, _ => simp [MultiPoly.degreeY] at hy1
  | add p q ihp ihq =>
    intro hy1
    show Nat.max (MultiPoly.degreeY (⟨0, by omega⟩ : Fin 2) (chainTotalDeriv (IterExpChain 2) p))
                 (MultiPoly.degreeY (⟨0, by omega⟩ : Fin 2) (chainTotalDeriv (IterExpChain 2) q))
       = Nat.max (MultiPoly.degreeY (⟨0, by omega⟩ : Fin 2) p)
                 (MultiPoly.degreeY (⟨0, by omega⟩ : Fin 2) q)
    rw [ihp (degY1_add_left hy1), ihq (degY1_add_right hy1)]
  | sub p q ihp ihq =>
    intro hy1
    show Nat.max (MultiPoly.degreeY (⟨0, by omega⟩ : Fin 2) (chainTotalDeriv (IterExpChain 2) p))
                 (MultiPoly.degreeY (⟨0, by omega⟩ : Fin 2) (chainTotalDeriv (IterExpChain 2) q))
       = Nat.max (MultiPoly.degreeY (⟨0, by omega⟩ : Fin 2) p)
                 (MultiPoly.degreeY (⟨0, by omega⟩ : Fin 2) q)
    rw [ihp (degY1_add_left hy1), ihq (degY1_add_right hy1)]
  | mul p q ihp ihq =>
    intro hy1
    have hp1 : MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) p = 0 := by
      have h' : MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) p
              + MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) q = 0 := hy1
      omega
    have hq1 : MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) q = 0 := by
      have h' : MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) p
              + MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) q = 0 := hy1
      omega
    show Nat.max (MultiPoly.degreeY (⟨0, by omega⟩ : Fin 2) (chainTotalDeriv (IterExpChain 2) p)
                  + MultiPoly.degreeY (⟨0, by omega⟩ : Fin 2) q)
                 (MultiPoly.degreeY (⟨0, by omega⟩ : Fin 2) p
                  + MultiPoly.degreeY (⟨0, by omega⟩ : Fin 2) (chainTotalDeriv (IterExpChain 2) q))
       = MultiPoly.degreeY (⟨0, by omega⟩ : Fin 2) p + MultiPoly.degreeY (⟨0, by omega⟩ : Fin 2) q
    rw [ihp hp1, ihq hq1]; exact Nat.max_self _

/-! ### Helpers (re-declared; the `y₁`-file's are `private`) -/

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

/-! ### The `y₀`-identity (inline induction, `y₁`-free threaded) -/

set_option maxHeartbeats 1600000 in
/-- **The `y₀`-analog `leadingCoeffY`-under-`cTD` identity**, for `y₁`-free `q`:
`eval(lcY₀(cTD₂ q)) = eval(cTD₂(lcY₀ q)) + (degreeY₀ q)·eval(lcY₀ q)`. Injection `d·lcY₀` (no `y₀`
factor). Budget raised: the single `induction` shares one heartbeat budget across all six cases
(the `y₁`-file splits into per-case lemmas instead; raising the limit is equally sound). -/
theorem leadingCoeffY0_cTD_eval_IterExp2 (q : MultiPoly 2) (x : Real) (env : Fin 2 → Real) :
    MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) q = 0 →
    MultiPoly.eval (MultiPoly.leadingCoeffY (⟨0, by omega⟩ : Fin 2)
        (chainTotalDeriv (IterExpChain 2) q)) x env
    = MultiPoly.eval (chainTotalDeriv (IterExpChain 2)
        (MultiPoly.leadingCoeffY (⟨0, by omega⟩ : Fin 2) q)) x env
      + MachLib.Real.natCast (MultiPoly.degreeY (⟨0, by omega⟩ : Fin 2) q)
        * MultiPoly.eval (MultiPoly.leadingCoeffY (⟨0, by omega⟩ : Fin 2) q) x env := by
  induction q with
  | const c =>
    intro _
    show (0 : Real) = 0 + MachLib.Real.natCast 0 * c
    rw [MachLib.Real.natCast_zero]; mach_ring
  | varX =>
    intro _
    show (1 : Real) = 1 + MachLib.Real.natCast 0 * x
    rw [MachLib.Real.natCast_zero]; mach_ring
  | varY j =>
    intro hy1
    rcases j with ⟨v, hv⟩
    match v, hv with
    | 0, _ =>
      show (1 : Real) = 0 + MachLib.Real.natCast 1 * 1
      rw [MachLib.Real.natCast_succ, MachLib.Real.natCast_zero]; mach_ring
    | 1, _ => simp [MultiPoly.degreeY] at hy1
  | add p q ihp ihq =>
    intro hy1
    have hp1 := degY1_add_left hy1
    have hq1 := degY1_add_right hy1
    have hp_eq := degreeY0_cTD_eq_of_y1free p hp1
    have hq_eq := degreeY0_cTD_eq_of_y1free q hq1
    rw [show chainTotalDeriv (IterExpChain 2) (MultiPoly.add p q)
          = MultiPoly.add (chainTotalDeriv (IterExpChain 2) p)
              (chainTotalDeriv (IterExpChain 2) q) from rfl]
    rcases Nat.lt_trichotomy (MultiPoly.degreeY (⟨0, by omega⟩ : Fin 2) p)
                             (MultiPoly.degreeY (⟨0, by omega⟩ : Fin 2) q) with hlt | heq | hgt
    · have hd : MultiPoly.degreeY (⟨0, by omega⟩ : Fin 2) (MultiPoly.add p q)
              = MultiPoly.degreeY (⟨0, by omega⟩ : Fin 2) q := Nat.max_eq_right (Nat.le_of_lt hlt)
      rw [lcY_add_of_lt (⟨0, by omega⟩ : Fin 2) (chainTotalDeriv (IterExpChain 2) p)
            (chainTotalDeriv (IterExpChain 2) q) (by rw [hp_eq, hq_eq]; exact hlt),
          lcY_add_of_lt (⟨0, by omega⟩ : Fin 2) p q hlt, hd]
      exact ihq hq1
    · have hd : MultiPoly.degreeY (⟨0, by omega⟩ : Fin 2) (MultiPoly.add p q)
              = MultiPoly.degreeY (⟨0, by omega⟩ : Fin 2) q := by
        show Nat.max _ _ = _; rw [heq]; exact Nat.max_self _
      rw [lcY_add_of_eq (⟨0, by omega⟩ : Fin 2) (chainTotalDeriv (IterExpChain 2) p)
            (chainTotalDeriv (IterExpChain 2) q) (by rw [hp_eq, hq_eq]; exact heq),
          lcY_add_of_eq (⟨0, by omega⟩ : Fin 2) p q heq, hd,
          show chainTotalDeriv (IterExpChain 2)
                 (MultiPoly.add (MultiPoly.leadingCoeffY (⟨0, by omega⟩ : Fin 2) p)
                                (MultiPoly.leadingCoeffY (⟨0, by omega⟩ : Fin 2) q))
             = MultiPoly.add
                 (chainTotalDeriv (IterExpChain 2) (MultiPoly.leadingCoeffY (⟨0, by omega⟩ : Fin 2) p))
                 (chainTotalDeriv (IterExpChain 2) (MultiPoly.leadingCoeffY (⟨0, by omega⟩ : Fin 2) q))
             from rfl]
      simp only [MultiPoly.eval_add] at ihp ihq ⊢
      rw [heq] at ihp
      rw [ihp hp1, ihq hq1]; mach_ring
    · have hd : MultiPoly.degreeY (⟨0, by omega⟩ : Fin 2) (MultiPoly.add p q)
              = MultiPoly.degreeY (⟨0, by omega⟩ : Fin 2) p := Nat.max_eq_left (Nat.le_of_lt hgt)
      rw [lcY_add_of_gt (⟨0, by omega⟩ : Fin 2) (chainTotalDeriv (IterExpChain 2) p)
            (chainTotalDeriv (IterExpChain 2) q) (by rw [hp_eq, hq_eq]; exact hgt),
          lcY_add_of_gt (⟨0, by omega⟩ : Fin 2) p q hgt, hd]
      exact ihp hp1
  | sub p q ihp ihq =>
    intro hy1
    have hp1 := degY1_add_left hy1
    have hq1 := degY1_add_right hy1
    have hp_eq := degreeY0_cTD_eq_of_y1free p hp1
    have hq_eq := degreeY0_cTD_eq_of_y1free q hq1
    rw [show chainTotalDeriv (IterExpChain 2) (MultiPoly.sub p q)
          = MultiPoly.sub (chainTotalDeriv (IterExpChain 2) p)
              (chainTotalDeriv (IterExpChain 2) q) from rfl]
    rcases Nat.lt_trichotomy (MultiPoly.degreeY (⟨0, by omega⟩ : Fin 2) p)
                             (MultiPoly.degreeY (⟨0, by omega⟩ : Fin 2) q) with hlt | heq | hgt
    · have hd : MultiPoly.degreeY (⟨0, by omega⟩ : Fin 2) (MultiPoly.sub p q)
              = MultiPoly.degreeY (⟨0, by omega⟩ : Fin 2) q := Nat.max_eq_right (Nat.le_of_lt hlt)
      rw [MultiPoly.leadingCoeffY_sub_of_lt (⟨0, by omega⟩ : Fin 2)
            (chainTotalDeriv (IterExpChain 2) p) (chainTotalDeriv (IterExpChain 2) q)
            (by rw [hp_eq, hq_eq]; exact hlt),
          MultiPoly.leadingCoeffY_sub_of_lt (⟨0, by omega⟩ : Fin 2) p q hlt, hd,
          show chainTotalDeriv (IterExpChain 2)
                 (MultiPoly.sub (MultiPoly.const 0) (MultiPoly.leadingCoeffY (⟨0, by omega⟩ : Fin 2) q))
             = MultiPoly.sub (MultiPoly.const 0)
                 (chainTotalDeriv (IterExpChain 2) (MultiPoly.leadingCoeffY (⟨0, by omega⟩ : Fin 2) q))
             from rfl]
      simp only [MultiPoly.eval_sub, MultiPoly.eval_const] at ihp ihq ⊢
      rw [ihq hq1]; mach_ring
    · have hd : MultiPoly.degreeY (⟨0, by omega⟩ : Fin 2) (MultiPoly.sub p q)
              = MultiPoly.degreeY (⟨0, by omega⟩ : Fin 2) q := by
        show Nat.max _ _ = _; rw [heq]; exact Nat.max_self _
      rw [MultiPoly.leadingCoeffY_sub_of_eq (⟨0, by omega⟩ : Fin 2)
            (chainTotalDeriv (IterExpChain 2) p) (chainTotalDeriv (IterExpChain 2) q)
            (by rw [hp_eq, hq_eq]; exact heq),
          MultiPoly.leadingCoeffY_sub_of_eq (⟨0, by omega⟩ : Fin 2) p q heq, hd,
          show chainTotalDeriv (IterExpChain 2)
                 (MultiPoly.sub (MultiPoly.leadingCoeffY (⟨0, by omega⟩ : Fin 2) p)
                                (MultiPoly.leadingCoeffY (⟨0, by omega⟩ : Fin 2) q))
             = MultiPoly.sub
                 (chainTotalDeriv (IterExpChain 2) (MultiPoly.leadingCoeffY (⟨0, by omega⟩ : Fin 2) p))
                 (chainTotalDeriv (IterExpChain 2) (MultiPoly.leadingCoeffY (⟨0, by omega⟩ : Fin 2) q))
             from rfl]
      simp only [MultiPoly.eval_sub] at ihp ihq ⊢
      rw [heq] at ihp
      rw [ihp hp1, ihq hq1]
      generalize MultiPoly.eval (chainTotalDeriv (IterExpChain 2)
          (MultiPoly.leadingCoeffY (⟨0, by omega⟩ : Fin 2) p)) x env = A
      generalize MultiPoly.eval (chainTotalDeriv (IterExpChain 2)
          (MultiPoly.leadingCoeffY (⟨0, by omega⟩ : Fin 2) q)) x env = B
      generalize MultiPoly.eval (MultiPoly.leadingCoeffY (⟨0, by omega⟩ : Fin 2) p) x env = LP
      generalize MultiPoly.eval (MultiPoly.leadingCoeffY (⟨0, by omega⟩ : Fin 2) q) x env = LQ
      generalize MachLib.Real.natCast (MultiPoly.degreeY (⟨0, by omega⟩ : Fin 2) q) = N
      mach_ring
    · have hd : MultiPoly.degreeY (⟨0, by omega⟩ : Fin 2) (MultiPoly.sub p q)
              = MultiPoly.degreeY (⟨0, by omega⟩ : Fin 2) p := Nat.max_eq_left (Nat.le_of_lt hgt)
      rw [lcY_sub_of_gt (⟨0, by omega⟩ : Fin 2) (chainTotalDeriv (IterExpChain 2) p)
            (chainTotalDeriv (IterExpChain 2) q) (by rw [hp_eq, hq_eq]; exact hgt),
          lcY_sub_of_gt (⟨0, by omega⟩ : Fin 2) p q hgt, hd]
      exact ihp hp1
  | mul p q ihp ihq =>
    intro hy1
    have hp1 : MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) p = 0 := by
      have h' : MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) p
              + MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) q = 0 := hy1
      omega
    have hq1 : MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) q = 0 := by
      have h' : MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) p
              + MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) q = 0 := hy1
      omega
    have hp_eq := degreeY0_cTD_eq_of_y1free p hp1
    have hq_eq := degreeY0_cTD_eq_of_y1free q hq1
    rw [show chainTotalDeriv (IterExpChain 2) (MultiPoly.mul p q)
          = MultiPoly.add (MultiPoly.mul (chainTotalDeriv (IterExpChain 2) p) q)
                          (MultiPoly.mul p (chainTotalDeriv (IterExpChain 2) q)) from rfl]
    have hcond : MultiPoly.degreeY (⟨0, by omega⟩ : Fin 2)
                   (MultiPoly.mul (chainTotalDeriv (IterExpChain 2) p) q)
               = MultiPoly.degreeY (⟨0, by omega⟩ : Fin 2)
                   (MultiPoly.mul p (chainTotalDeriv (IterExpChain 2) q)) := by
      show MultiPoly.degreeY (⟨0, by omega⟩ : Fin 2) (chainTotalDeriv (IterExpChain 2) p)
             + MultiPoly.degreeY (⟨0, by omega⟩ : Fin 2) q
         = MultiPoly.degreeY (⟨0, by omega⟩ : Fin 2) p
             + MultiPoly.degreeY (⟨0, by omega⟩ : Fin 2) (chainTotalDeriv (IterExpChain 2) q)
      rw [hp_eq, hq_eq]
    rw [lcY_add_of_eq (⟨0, by omega⟩ : Fin 2)
          (MultiPoly.mul (chainTotalDeriv (IterExpChain 2) p) q)
          (MultiPoly.mul p (chainTotalDeriv (IterExpChain 2) q)) hcond,
        show MultiPoly.leadingCoeffY (⟨0, by omega⟩ : Fin 2)
               (MultiPoly.mul (chainTotalDeriv (IterExpChain 2) p) q)
           = MultiPoly.mul (MultiPoly.leadingCoeffY (⟨0, by omega⟩ : Fin 2)
                             (chainTotalDeriv (IterExpChain 2) p))
                           (MultiPoly.leadingCoeffY (⟨0, by omega⟩ : Fin 2) q) from rfl,
        show MultiPoly.leadingCoeffY (⟨0, by omega⟩ : Fin 2)
               (MultiPoly.mul p (chainTotalDeriv (IterExpChain 2) q))
           = MultiPoly.mul (MultiPoly.leadingCoeffY (⟨0, by omega⟩ : Fin 2) p)
                           (MultiPoly.leadingCoeffY (⟨0, by omega⟩ : Fin 2)
                             (chainTotalDeriv (IterExpChain 2) q)) from rfl,
        show MultiPoly.leadingCoeffY (⟨0, by omega⟩ : Fin 2) (MultiPoly.mul p q)
           = MultiPoly.mul (MultiPoly.leadingCoeffY (⟨0, by omega⟩ : Fin 2) p)
                           (MultiPoly.leadingCoeffY (⟨0, by omega⟩ : Fin 2) q) from rfl,
        show MultiPoly.degreeY (⟨0, by omega⟩ : Fin 2) (MultiPoly.mul p q)
           = MultiPoly.degreeY (⟨0, by omega⟩ : Fin 2) p
               + MultiPoly.degreeY (⟨0, by omega⟩ : Fin 2) q from rfl,
        natCast_add',
        show chainTotalDeriv (IterExpChain 2)
               (MultiPoly.mul (MultiPoly.leadingCoeffY (⟨0, by omega⟩ : Fin 2) p)
                              (MultiPoly.leadingCoeffY (⟨0, by omega⟩ : Fin 2) q))
           = MultiPoly.add
               (MultiPoly.mul (chainTotalDeriv (IterExpChain 2)
                                (MultiPoly.leadingCoeffY (⟨0, by omega⟩ : Fin 2) p))
                              (MultiPoly.leadingCoeffY (⟨0, by omega⟩ : Fin 2) q))
               (MultiPoly.mul (MultiPoly.leadingCoeffY (⟨0, by omega⟩ : Fin 2) p)
                              (chainTotalDeriv (IterExpChain 2)
                                (MultiPoly.leadingCoeffY (⟨0, by omega⟩ : Fin 2) q))) from rfl]
    simp only [MultiPoly.eval_add, MultiPoly.eval_mul] at ihp ihq ⊢
    rw [ihp hp1, ihq hq1]
    generalize MultiPoly.eval (chainTotalDeriv (IterExpChain 2)
        (MultiPoly.leadingCoeffY (⟨0, by omega⟩ : Fin 2) p)) x env = A
    generalize MultiPoly.eval (chainTotalDeriv (IterExpChain 2)
        (MultiPoly.leadingCoeffY (⟨0, by omega⟩ : Fin 2) q)) x env = B
    generalize MultiPoly.eval (MultiPoly.leadingCoeffY (⟨0, by omega⟩ : Fin 2) p) x env = LP
    generalize MultiPoly.eval (MultiPoly.leadingCoeffY (⟨0, by omega⟩ : Fin 2) q) x env = LQ
    generalize MachLib.Real.natCast (MultiPoly.degreeY (⟨0, by omega⟩ : Fin 2) p) = Na
    generalize MachLib.Real.natCast (MultiPoly.degreeY (⟨0, by omega⟩ : Fin 2) q) = Nb
    mach_ring

end MachLib.ChainExp2LcY0CTD
