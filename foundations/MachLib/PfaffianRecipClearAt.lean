import MachLib.PfaffianRecipStep
import MachLib.MultiPolyDropAt

/-!
# `clearAt` — clear an INTERIOR reciprocal variable (Stage A of the mixed-chain port)

The interior analog of `clearTop`: `clearAt i v` clears the reciprocal variable `y_i = 1/v`
sitting at an ARBITRARY index `i` of a `MultiPoly (N+1)`, producing a `MultiPoly N` over the chain
with slot `i` removed. Lower/higher survivors reindex (the `dropAt` pattern via `embedSkip`); the
target `y_i` clears to `const 1` (`y_i·v = 1`); the clearing power is `degreeY i`, shared across
`add`/`sub` by `v^(max−dᵢ)` padding exactly as `clearTop`.

`clearAt_eval` is the load-bearing correctness bridge — the interior analog of `clearTop_eval`:
on an `envFull` agreeing with `env` on the surviving slots (via `embedSkip i`) and with
`envFull i = 1/eval v`, `clearAt i v p = v^(degreeY i p) · p`. The non-`varY` cases are the
`clearTop` proof verbatim (index `i` for the top); only the `varY` case gains the interior 3-way
split. No new axioms — reuses `mpolyPow` / `mpad_combine`.
-/

namespace MachLib
namespace PfaffianExpRecip

open MachLib.Real
open MachLib.MultiPolyMod MachLib.MultiPolyMod.MultiPoly
open MachLib.PfaffianChainMod MachLib.PfaffianChainMod.PfaffianFn MachLib.PfaffianGeneralReduce

variable {N : Nat}

/-- Clear the interior reciprocal variable `y_i = 1/v`. -/
noncomputable def clearAt (i : Fin (N + 1)) (v : MultiPoly N) : MultiPoly (N + 1) → MultiPoly N
  | MultiPoly.const c => MultiPoly.const c
  | MultiPoly.varX => MultiPoly.varX
  | MultiPoly.varY j =>
      if hj : j.val < i.val then MultiPoly.varY ⟨j.val, by omega⟩
      else if hj2 : i.val < j.val then MultiPoly.varY ⟨j.val - 1, by omega⟩
      else MultiPoly.const 1
  | MultiPoly.add p q =>
      MultiPoly.add
        (MultiPoly.mul (mpolyPow v (Nat.max (MultiPoly.degreeY i p) (MultiPoly.degreeY i q)
              - MultiPoly.degreeY i p)) (clearAt i v p))
        (MultiPoly.mul (mpolyPow v (Nat.max (MultiPoly.degreeY i p) (MultiPoly.degreeY i q)
              - MultiPoly.degreeY i q)) (clearAt i v q))
  | MultiPoly.sub p q =>
      MultiPoly.sub
        (MultiPoly.mul (mpolyPow v (Nat.max (MultiPoly.degreeY i p) (MultiPoly.degreeY i q)
              - MultiPoly.degreeY i p)) (clearAt i v p))
        (MultiPoly.mul (mpolyPow v (Nat.max (MultiPoly.degreeY i p) (MultiPoly.degreeY i q)
              - MultiPoly.degreeY i q)) (clearAt i v q))
  | MultiPoly.mul p q => MultiPoly.mul (clearAt i v p) (clearAt i v q)

/-- **Eval bridge for `clearAt`.** With `envFull` agreeing with `env` on the surviving slots
(`envFull ∘ embedSkip i = env`) and `envFull i = 1/eval v x env` (`eval v ≠ 0`),
`clearAt i v p` evaluates to `v^(degreeY i p) · p`. Interior analog of `clearTop_eval`. -/
theorem clearAt_eval (i : Fin (N + 1)) (v : MultiPoly N) (x : Real) (env : Fin N → Real)
    (envFull : Fin (N + 1) → Real)
    (hlow : ∀ (k : Fin N), envFull (embedSkip i k) = env k)
    (htop : envFull i = 1 / MultiPoly.eval v x env)
    (hvne : MultiPoly.eval v x env ≠ 0)
    (p : MultiPoly (N + 1)) :
    MultiPoly.eval (clearAt i v p) x env
      = MultiPoly.eval (mpolyPow v (MultiPoly.degreeY i p)) x env * MultiPoly.eval p x envFull := by
  induction p with
  | const c =>
    show MultiPoly.eval (MultiPoly.const c) x env = MultiPoly.eval (mpolyPow v 0) x env * c
    rw [mpolyPow_eval_zero]; show c = 1 * c; mach_ring
  | varX =>
    show MultiPoly.eval MultiPoly.varX x env = MultiPoly.eval (mpolyPow v 0) x env * x
    rw [mpolyPow_eval_zero]; show x = 1 * x; mach_ring
  | varY j =>
    by_cases hj : j.val < i.val
    · have hne : i ≠ j := by intro heq; rw [heq] at hj; omega
      have hdeg : MultiPoly.degreeY i (MultiPoly.varY j) = 0 := by
        show (if i = j then (1 : Nat) else 0) = 0; rw [if_neg hne]
      have hclear : clearAt i v (MultiPoly.varY j) = MultiPoly.varY ⟨j.val, by omega⟩ := by
        show (if _ : j.val < i.val then MultiPoly.varY ⟨j.val, by omega⟩
              else if _ : i.val < j.val then MultiPoly.varY ⟨j.val - 1, by omega⟩
              else MultiPoly.const 1) = MultiPoly.varY ⟨j.val, by omega⟩
        rw [dif_pos hj]
      rw [hclear, hdeg, mpolyPow_eval_zero]
      show env ⟨j.val, by omega⟩ = 1 * MultiPoly.eval (MultiPoly.varY j) x envFull
      rw [show MultiPoly.eval (MultiPoly.varY j) x envFull = envFull j from rfl]
      have hkey : envFull j = env ⟨j.val, by omega⟩ := by
        have h1 := hlow (⟨j.val, by omega⟩ : Fin N)
        rw [embedSkip_lt i j hj] at h1; exact h1
      rw [hkey]; mach_ring
    · by_cases hj2 : i.val < j.val
      · have hne : i ≠ j := by intro heq; rw [heq] at hj2; omega
        have hdeg : MultiPoly.degreeY i (MultiPoly.varY j) = 0 := by
          show (if i = j then (1 : Nat) else 0) = 0; rw [if_neg hne]
        have hclear : clearAt i v (MultiPoly.varY j) = MultiPoly.varY ⟨j.val - 1, by omega⟩ := by
          show (if _ : j.val < i.val then MultiPoly.varY ⟨j.val, by omega⟩
                else if _ : i.val < j.val then MultiPoly.varY ⟨j.val - 1, by omega⟩
                else MultiPoly.const 1) = MultiPoly.varY ⟨j.val - 1, by omega⟩
          rw [dif_neg hj, dif_pos hj2]
        rw [hclear, hdeg, mpolyPow_eval_zero]
        show env ⟨j.val - 1, by omega⟩ = 1 * MultiPoly.eval (MultiPoly.varY j) x envFull
        rw [show MultiPoly.eval (MultiPoly.varY j) x envFull = envFull j from rfl]
        have hkey : envFull j = env ⟨j.val - 1, by omega⟩ := by
          have h1 := hlow (⟨j.val - 1, by omega⟩ : Fin N)
          rw [embedSkip_gt i j hj2] at h1; exact h1
        rw [hkey]; mach_ring
      · have hji : i = j := Fin.eq_of_val_eq (by omega)
        have hdeg : MultiPoly.degreeY i (MultiPoly.varY j) = 1 := by
          show (if i = j then (1 : Nat) else 0) = 1; rw [if_pos hji]
        have hclear : clearAt i v (MultiPoly.varY j) = MultiPoly.const 1 := by
          show (if _ : j.val < i.val then MultiPoly.varY ⟨j.val, by omega⟩
                else if _ : i.val < j.val then MultiPoly.varY ⟨j.val - 1, by omega⟩
                else MultiPoly.const 1) = MultiPoly.const 1
          rw [dif_neg hj, dif_neg hj2]
        rw [hclear, hdeg, mpolyPow_eval_succ, mpolyPow_eval_zero]
        show (1 : Real) = MultiPoly.eval v x env * 1 * MultiPoly.eval (MultiPoly.varY j) x envFull
        rw [show MultiPoly.eval (MultiPoly.varY j) x envFull = envFull j from rfl, ← hji, htop,
            mul_one_ax]
        exact (mul_div_cancel_left hvne).symm
  | add p q ihp ihq =>
    show MultiPoly.eval (MultiPoly.add
        (MultiPoly.mul (mpolyPow v (Nat.max (MultiPoly.degreeY i p) (MultiPoly.degreeY i q)
              - MultiPoly.degreeY i p)) (clearAt i v p))
        (MultiPoly.mul (mpolyPow v (Nat.max (MultiPoly.degreeY i p) (MultiPoly.degreeY i q)
              - MultiPoly.degreeY i q)) (clearAt i v q))) x env
        = MultiPoly.eval (mpolyPow v (Nat.max (MultiPoly.degreeY i p) (MultiPoly.degreeY i q))) x env
          * MultiPoly.eval (MultiPoly.add p q) x envFull
    simp only [MultiPoly.eval]
    rw [ihp, ihq]
    exact mpad_combine_add v x env _ _ _ _ _ (Nat.le_max_left _ _) (Nat.le_max_right _ _)
  | sub p q ihp ihq =>
    show MultiPoly.eval (MultiPoly.sub
        (MultiPoly.mul (mpolyPow v (Nat.max (MultiPoly.degreeY i p) (MultiPoly.degreeY i q)
              - MultiPoly.degreeY i p)) (clearAt i v p))
        (MultiPoly.mul (mpolyPow v (Nat.max (MultiPoly.degreeY i p) (MultiPoly.degreeY i q)
              - MultiPoly.degreeY i q)) (clearAt i v q))) x env
        = MultiPoly.eval (mpolyPow v (Nat.max (MultiPoly.degreeY i p) (MultiPoly.degreeY i q))) x env
          * MultiPoly.eval (MultiPoly.sub p q) x envFull
    simp only [MultiPoly.eval]
    rw [ihp, ihq]
    exact mpad_combine_sub v x env _ _ _ _ _ (Nat.le_max_left _ _) (Nat.le_max_right _ _)
  | mul p q ihp ihq =>
    show MultiPoly.eval (MultiPoly.mul (clearAt i v p) (clearAt i v q)) x env
        = MultiPoly.eval (mpolyPow v (MultiPoly.degreeY i p + MultiPoly.degreeY i q)) x env
          * MultiPoly.eval (MultiPoly.mul p q) x envFull
    simp only [MultiPoly.eval]
    rw [ihp, ihq, mpolyPow_eval_add]; mach_ring

/-! ## Chain-level bridge + the interior reciprocal descent step -/

/-- The chain with interior slot `i` removed: its evals are `c`'s at the surviving slots
(`embedSkip i`). Relations are placeholder (the zero-count bridge uses only the evals). -/
noncomputable def chainDropAt (i : Fin (N + 1)) (c : PfaffianChain (N + 1)) : PfaffianChain N :=
  { evals := fun k => c.evals (embedSkip i k),
    relations := fun _ => MultiPoly.const 0 }

/-- **Chain-level eval bridge.** Instantiate `clearAt_eval` at the actual chain: `envFull =
c.chainValues`, `env = (chainDropAt i c).chainValues` (agree on survivors by construction), with
the interior reciprocal witness `c.chainValues x i = 1/eval v`. Interior analog of
`clearTop_chain_bridge`. -/
theorem clearAt_chain_bridge (i : Fin (N + 1)) (c : PfaffianChain (N + 1)) (v : MultiPoly N) (x : Real)
    (hwitness : c.chainValues x i = 1 / MultiPoly.eval v x ((chainDropAt i c).chainValues x))
    (hvne : MultiPoly.eval v x ((chainDropAt i c).chainValues x) ≠ 0)
    (p : MultiPoly (N + 1)) :
    MultiPoly.eval (clearAt i v p) x ((chainDropAt i c).chainValues x)
      = MultiPoly.eval (mpolyPow v (MultiPoly.degreeY i p)) x ((chainDropAt i c).chainValues x)
        * MultiPoly.eval p x (c.chainValues x) := by
  refine clearAt_eval i v x ((chainDropAt i c).chainValues x) (c.chainValues x) ?_ hwitness hvne p
  intro k; rfl

/-- **Interior reciprocal descent step.** Bound the zeros of `pfaffianChainFn c p` (with an
interior reciprocal `y_i = 1/v`) by those of `pfaffianChainFn (chainDropAt i c) (clearAt i v p)`
over the slot-`i`-removed chain, supplied by the IH. No integrating factor — the clearing bridge
`fp·v^d = fP` does it (`v^d > 0` not even needed: `fp z = 0 ⇒ fP z = 0`). Interior analog of
`recip_top_step`. -/
theorem clearAt_recip_step (i : Fin (N + 1)) (c : PfaffianChain (N + 1)) (v : MultiPoly N)
    (a b : Real) (M : Nat)
    (hwitness : ∀ x : Real, a < x → x < b →
        c.chainValues x i = 1 / MultiPoly.eval v x ((chainDropAt i c).chainValues x))
    (hvne : ∀ x : Real, a < x → x < b →
        MultiPoly.eval v x ((chainDropAt i c).chainValues x) ≠ 0)
    (p : MultiPoly (N + 1))
    (hIH : ∀ zeros : List Real, zeros.Nodup →
        (∀ z ∈ zeros, a < z ∧ z < b
            ∧ (pfaffianChainFn (chainDropAt i c) (clearAt i v p)).eval z = 0) →
        zeros.length ≤ M) :
    ∀ zeros : List Real, zeros.Nodup →
      (∀ z ∈ zeros, a < z ∧ z < b ∧ (pfaffianChainFn c p).eval z = 0) →
      zeros.length ≤ M := by
  apply recip_top_zero_reduction
    (pfaffianChainFn c p).eval
    (pfaffianChainFn (chainDropAt i c) (clearAt i v p)).eval
    (fun x => MultiPoly.eval (mpolyPow v (MultiPoly.degreeY i p)) x ((chainDropAt i c).chainValues x))
    a b M ?_ hIH
  intro z ha hb
  show MultiPoly.eval p z (c.chainValues z)
      * MultiPoly.eval (mpolyPow v (MultiPoly.degreeY i p)) z ((chainDropAt i c).chainValues z)
      = MultiPoly.eval (clearAt i v p) z ((chainDropAt i c).chainValues z)
  rw [clearAt_chain_bridge i c v z (hwitness z ha hb) (hvne z ha hb) p]
  mach_ring

end PfaffianExpRecip
end MachLib
