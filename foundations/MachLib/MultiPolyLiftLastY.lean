import MachLib.MultiPoly

/-!
# `liftLastY` — a right inverse of `dropLastY` (embed as a top-variable-free polynomial)

`dropLastY : MultiPoly (n+1) → MultiPoly n` drops the top chain variable. The ∀N Khovanskii descent's
multiplier-threading needs the other direction: embed a `MultiPoly n` into `MultiPoly (n+1)` as a
polynomial that does not use the new top variable, so the recursive graded multiplier can be built and
recovered via `dropLastY`. This file supplies it and its two load-bearing facts:

* `dropLastY_liftLastY` — `dropLastY (liftLastY x) = x` (right inverse);
* `degreeY_top_liftLastY` — `liftLastY x` is free of the top variable.

Pure structural recursion on `MultiPoly`; no `sorry`.
-/

namespace MachLib.MultiPolyMod.MultiPoly

/-- Embed a `MultiPoly n` into `MultiPoly (n+1)`, mapping each `y_i` to the same `y_i` (a lower index in
`Fin (n+1)`) and never introducing the top variable `y_n`. -/
noncomputable def liftLastY {n : Nat} : MultiPoly n → MultiPoly (n + 1)
  | .const c => .const c
  | .varX => .varX
  | .varY i => .varY ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩
  | .add p q => .add (liftLastY p) (liftLastY q)
  | .sub p q => .sub (liftLastY p) (liftLastY q)
  | .mul p q => .mul (liftLastY p) (liftLastY q)

/-- **`liftLastY` is a right inverse of `dropLastY`.** -/
theorem dropLastY_liftLastY {n : Nat} (x : MultiPoly n) : dropLastY (liftLastY x) = x := by
  induction x with
  | const c => rfl
  | varX => rfl
  | varY i =>
      show (if h : (⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ : Fin (n + 1)).val < n
              then MultiPoly.varY (⟨i.val, h⟩ : Fin n) else MultiPoly.const 0) = MultiPoly.varY i
      rw [dif_pos i.isLt]
  | add p q ihp ihq =>
      show MultiPoly.add (dropLastY (liftLastY p)) (dropLastY (liftLastY q)) = MultiPoly.add p q
      rw [ihp, ihq]
  | sub p q ihp ihq =>
      show MultiPoly.sub (dropLastY (liftLastY p)) (dropLastY (liftLastY q)) = MultiPoly.sub p q
      rw [ihp, ihq]
  | mul p q ihp ihq =>
      show MultiPoly.mul (dropLastY (liftLastY p)) (dropLastY (liftLastY q)) = MultiPoly.mul p q
      rw [ihp, ihq]

/-- **`liftLastY x` is free of the top variable.** -/
theorem degreeY_top_liftLastY {n : Nat} (x : MultiPoly n) :
    degreeY (⟨n, Nat.lt_succ_self n⟩ : Fin (n + 1)) (liftLastY x) = 0 := by
  induction x with
  | const c => rfl
  | varX => rfl
  | varY i =>
      show (if (⟨n, Nat.lt_succ_self n⟩ : Fin (n + 1)) = (⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ : Fin (n + 1))
              then 1 else 0) = 0
      rw [if_neg (by intro h; have := (Fin.mk.injEq ..).mp h; omega)]
  | add p q ihp ihq =>
      show Nat.max (degreeY _ (liftLastY p)) (degreeY _ (liftLastY q)) = 0
      rw [ihp, ihq]; decide
  | sub p q ihp ihq =>
      show Nat.max (degreeY _ (liftLastY p)) (degreeY _ (liftLastY q)) = 0
      rw [ihp, ihq]; decide
  | mul p q ihp ihq =>
      show degreeY _ (liftLastY p) + degreeY _ (liftLastY q) = 0
      rw [ihp, ihq]

/-- **Eval ignores the new top variable.** `eval (liftLastY x)` at any `Fin (n+1)` environment equals
`eval x` at the environment restricted to the first `n` slots. -/
theorem eval_liftLastY {n : Nat} (x : MultiPoly n) (xval : Real) (env : Fin (n + 1) → Real) :
    MultiPoly.eval (liftLastY x) xval env
      = MultiPoly.eval x xval (fun i : Fin n => env ⟨i.val, by omega⟩) := by
  induction x with
  | const c => rfl
  | varX => rfl
  | varY i => rfl
  | add p q ihp ihq =>
      show MultiPoly.eval (liftLastY p) xval env + MultiPoly.eval (liftLastY q) xval env
        = MultiPoly.eval p xval _ + MultiPoly.eval q xval _
      rw [ihp, ihq]
  | sub p q ihp ihq =>
      show MultiPoly.eval (liftLastY p) xval env - MultiPoly.eval (liftLastY q) xval env
        = MultiPoly.eval p xval _ - MultiPoly.eval q xval _
      rw [ihp, ihq]
  | mul p q ihp ihq =>
      show MultiPoly.eval (liftLastY p) xval env * MultiPoly.eval (liftLastY q) xval env
        = MultiPoly.eval p xval _ * MultiPoly.eval q xval _
      rw [ihp, ihq]

end MachLib.MultiPolyMod.MultiPoly
