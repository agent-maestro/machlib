import MachLib.IterExpDepthNCapstone

/-!
# Phase D (D3, WF assembly bridging) — the ∀N dispatch bridges (`Fin (m+2)` inner ↔ `Fin (m+3)` `lcY_top p`)

The final WF assembly dispatches on the inner `q := dropLastY(lcY_top p)` (a `MultiPoly (m+2)`), but the
inner-trim eval-preservation is phrased in terms of `lcY_top p` (a `MultiPoly (m+3)`). These lemmas cross
the two arities. ∀N ports of `IterExpDepth3Assembly`'s `dropLastY_eval_zero_of_yfree` /
`degreeY2_leadingCoeffY1_zero`.

**Mechanical note.** The structural-induction lemma is stated with the two `y`-indices ABSTRACT (`it`, `ip`
with `it.val = m+2`, `ip.val = m+1`), NOT as literals `⟨m+2, by omega⟩` — the omega-proof-carrying literal
index makes `whnf`/`isDefEq` diverge inside the `show` unifications at variable depth (the same literal-index
hazard the reduce files avoid). Callers instantiate with `rfl` for the `.val` hypotheses. No `sorry`.
-/

namespace MachLib.IterExpDepthN

open MachLib.Real
open MachLib.MultiPolyMod
open MachLib.MultiPolyMod.MultiPoly

/-- **A top-free `X` that vanishes after `dropLastY` vanishes on every full environment.** `dropLastY`
preserves eval, and top-freeness makes the dropped coordinate irrelevant. Generic in `n` (the depth-3
`dropLastY_eval_zero_of_yfree` is the `n = 2` instance). -/
theorem dropLastY_eval_zero_of_yfree {n : Nat} (X : MultiPoly (n + 1))
    (hX : MultiPoly.degreeY (⟨n, Nat.lt_succ_self n⟩ : Fin (n + 1)) X = 0)
    (h : ∀ (x : Real) (env : Fin n → Real), MultiPoly.eval (MultiPoly.dropLastY X) x env = 0) :
    ∀ (x : Real) (env : Fin (n + 1) → Real), MultiPoly.eval X x env = 0 := by
  intro x env
  rw [← MultiPoly.eval_dropLastY X hX x env]
  exact h x _

set_option maxHeartbeats 1200000 in
/-- **`leadingCoeffY ip` preserves `y_it`-freeness** (abstract indices; `it` = top, `ip` = top−1). ∀N port
of `degreeY2_leadingCoeffY1_zero` (structural induction; the leading-`y_ip` extraction never introduces the
top variable `y_it`). -/
theorem degreeYtop_leadingCoeffYprev_zero (n : Nat) (it ip : Fin n) : ∀ (X : MultiPoly n),
    MultiPoly.degreeY it X = 0 →
    MultiPoly.degreeY it (MultiPoly.leadingCoeffY ip X) = 0 := by
  intro X
  induction X with
  | const c => intro _; rfl
  | varX => intro _; rfl
  | varY i =>
    intro hj
    show MultiPoly.degreeY it
      (if i = ip then MultiPoly.const 1 else MultiPoly.varY i) = 0
    by_cases hi : i = ip
    · rw [if_pos hi]; rfl
    · rw [if_neg hi]; exact hj
  | add p q ihp ihq =>
    intro hj
    have hmax : Nat.max (MultiPoly.degreeY it p) (MultiPoly.degreeY it q) = 0 := hj
    have hp : MultiPoly.degreeY it p = 0 := by
      have hle : MultiPoly.degreeY it p
          ≤ Nat.max (MultiPoly.degreeY it p) (MultiPoly.degreeY it q) := Nat.le_max_left _ _
      omega
    have hq : MultiPoly.degreeY it q = 0 := by
      have hle : MultiPoly.degreeY it q
          ≤ Nat.max (MultiPoly.degreeY it p) (MultiPoly.degreeY it q) := Nat.le_max_right _ _
      omega
    show MultiPoly.degreeY it
      (if MultiPoly.degreeY ip p > MultiPoly.degreeY ip q
        then MultiPoly.leadingCoeffY ip p
        else if MultiPoly.degreeY ip q > MultiPoly.degreeY ip p
          then MultiPoly.leadingCoeffY ip q
          else MultiPoly.add (MultiPoly.leadingCoeffY ip p) (MultiPoly.leadingCoeffY ip q)) = 0
    by_cases h1 : MultiPoly.degreeY ip p > MultiPoly.degreeY ip q
    · rw [if_pos h1]; exact ihp hp
    · rw [if_neg h1]
      by_cases h2 : MultiPoly.degreeY ip q > MultiPoly.degreeY ip p
      · rw [if_pos h2]; exact ihq hq
      · rw [if_neg h2]
        show Nat.max (MultiPoly.degreeY it (MultiPoly.leadingCoeffY ip p))
            (MultiPoly.degreeY it (MultiPoly.leadingCoeffY ip q)) = 0
        rw [ihp hp, ihq hq]; exact Nat.max_self 0
  | sub p q ihp ihq =>
    intro hj
    have hmax : Nat.max (MultiPoly.degreeY it p) (MultiPoly.degreeY it q) = 0 := hj
    have hp : MultiPoly.degreeY it p = 0 := by
      have hle : MultiPoly.degreeY it p
          ≤ Nat.max (MultiPoly.degreeY it p) (MultiPoly.degreeY it q) := Nat.le_max_left _ _
      omega
    have hq : MultiPoly.degreeY it q = 0 := by
      have hle : MultiPoly.degreeY it q
          ≤ Nat.max (MultiPoly.degreeY it p) (MultiPoly.degreeY it q) := Nat.le_max_right _ _
      omega
    show MultiPoly.degreeY it
      (if MultiPoly.degreeY ip p > MultiPoly.degreeY ip q
        then MultiPoly.leadingCoeffY ip p
        else if MultiPoly.degreeY ip q > MultiPoly.degreeY ip p
          then MultiPoly.sub (MultiPoly.const 0) (MultiPoly.leadingCoeffY ip q)
          else MultiPoly.sub (MultiPoly.leadingCoeffY ip p) (MultiPoly.leadingCoeffY ip q)) = 0
    by_cases h1 : MultiPoly.degreeY ip p > MultiPoly.degreeY ip q
    · rw [if_pos h1]; exact ihp hp
    · rw [if_neg h1]
      by_cases h2 : MultiPoly.degreeY ip q > MultiPoly.degreeY ip p
      · rw [if_pos h2]
        show Nat.max (MultiPoly.degreeY it (MultiPoly.const 0))
            (MultiPoly.degreeY it (MultiPoly.leadingCoeffY ip q)) = 0
        rw [ihq hq]; exact Nat.max_self 0
      · rw [if_neg h2]
        show Nat.max (MultiPoly.degreeY it (MultiPoly.leadingCoeffY ip p))
            (MultiPoly.degreeY it (MultiPoly.leadingCoeffY ip q)) = 0
        rw [ihp hp, ihq hq]; exact Nat.max_self 0
  | mul p q ihp ihq =>
    intro hj
    have hadd : MultiPoly.degreeY it p + MultiPoly.degreeY it q = 0 := hj
    have hp : MultiPoly.degreeY it p = 0 := by omega
    have hq : MultiPoly.degreeY it q = 0 := by omega
    show MultiPoly.degreeY it
      (MultiPoly.mul (MultiPoly.leadingCoeffY ip p) (MultiPoly.leadingCoeffY ip q)) = 0
    show MultiPoly.degreeY it (MultiPoly.leadingCoeffY ip p)
      + MultiPoly.degreeY it (MultiPoly.leadingCoeffY ip q) = 0
    rw [ihp hp, ihq hq]

end MachLib.IterExpDepthN
