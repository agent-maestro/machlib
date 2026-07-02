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

/-- **`dropLastY` preserves `degreeY` at a non-top index.** For `ip'.val = ip.val` (so `ip` is not the top
variable, since `ip'.val < n`), `degreeY ip' (dropLastY X) = degreeY ip X`. The `= ` sharpening of
`MultiPoly.degreeY_dropLastY_le`; the generic bridge behind the depth-3 `degreeY1_dropLastY`. Abstract
indices (whnf hazard). -/
theorem degreeY_dropLastY_eq_prev (n : Nat) (ip : Fin (n + 1)) (ip' : Fin n)
    (hcast : ip'.val = ip.val) : ∀ (X : MultiPoly (n + 1)),
    MultiPoly.degreeY ip' (MultiPoly.dropLastY X) = MultiPoly.degreeY ip X := by
  intro X
  induction X with
  | const c => rfl
  | varX => rfl
  | varY i =>
    show MultiPoly.degreeY ip'
        (if h : i.val < n then MultiPoly.varY ⟨i.val, h⟩ else MultiPoly.const 0)
      = (if ip = i then 1 else 0)
    by_cases hlt : i.val < n
    · rw [dif_pos hlt]
      show (if ip' = ⟨i.val, hlt⟩ then 1 else 0) = (if ip = i then 1 else 0)
      by_cases hie : ip = i
      · rw [if_pos hie, if_pos (Fin.ext (by rw [hcast]; exact congrArg Fin.val hie))]
      · rw [if_neg hie, if_neg (fun h => hie (Fin.ext (by rw [← hcast]; exact congrArg Fin.val h)))]
    · rw [dif_neg hlt]
      show (0 : Nat) = (if ip = i then 1 else 0)
      rw [if_neg (fun h => hlt (by
        have hii : ip.val = i.val := congrArg Fin.val h
        rw [← hii, ← hcast]; exact ip'.isLt))]
  | add p q ihp ihq =>
    show Nat.max (MultiPoly.degreeY ip' (MultiPoly.dropLastY p))
        (MultiPoly.degreeY ip' (MultiPoly.dropLastY q))
      = Nat.max (MultiPoly.degreeY ip p) (MultiPoly.degreeY ip q)
    rw [ihp, ihq]
  | sub p q ihp ihq =>
    show Nat.max (MultiPoly.degreeY ip' (MultiPoly.dropLastY p))
        (MultiPoly.degreeY ip' (MultiPoly.dropLastY q))
      = Nat.max (MultiPoly.degreeY ip p) (MultiPoly.degreeY ip q)
    rw [ihp, ihq]
  | mul p q ihp ihq =>
    show MultiPoly.degreeY ip' (MultiPoly.dropLastY p) + MultiPoly.degreeY ip' (MultiPoly.dropLastY q)
      = MultiPoly.degreeY ip p + MultiPoly.degreeY ip q
    rw [ihp, ihq]

set_option maxHeartbeats 1600000 in
/-- **`dropLastY` commutes with `leadingCoeffY ip`** (non-top index `ip`, cast to `ip'` one variable down).
`leadingCoeffY` reads only `degreeY ip`, which `dropLastY` preserves (`degreeY_dropLastY_eq_prev`), so the
leading-`y_ip`-coefficient extraction is unaffected by dropping the top variable. ∀N port of
`dropLastY_leadingCoeffY1_commute` (abstract indices; whnf hazard). -/
theorem dropLastY_leadingCoeffYprev_commute (n : Nat) (ip : Fin (n + 1)) (ip' : Fin n)
    (hcast : ip'.val = ip.val) : ∀ (X : MultiPoly (n + 1)),
    MultiPoly.dropLastY (MultiPoly.leadingCoeffY ip X)
      = MultiPoly.leadingCoeffY ip' (MultiPoly.dropLastY X) := by
  intro X
  induction X with
  | const c => rfl
  | varX => rfl
  | varY i =>
    have hd : MultiPoly.dropLastY (MultiPoly.varY i)
        = (if h : i.val < n then MultiPoly.varY ⟨i.val, h⟩ else MultiPoly.const 0) := rfl
    show MultiPoly.dropLastY (if i = ip then MultiPoly.const 1 else MultiPoly.varY i)
      = MultiPoly.leadingCoeffY ip' (MultiPoly.dropLastY (MultiPoly.varY i))
    by_cases hi : i = ip
    · have hlt : i.val < n := by rw [congrArg Fin.val hi, ← hcast]; exact ip'.isLt
      rw [if_pos hi, hd, dif_pos hlt]
      show MultiPoly.const 1
        = (if (⟨i.val, hlt⟩ : Fin n) = ip' then MultiPoly.const 1 else MultiPoly.varY ⟨i.val, hlt⟩)
      rw [if_pos (Fin.ext (by rw [hcast]; exact congrArg Fin.val hi))]
    · rw [if_neg hi, hd]
      by_cases hlt : i.val < n
      · rw [dif_pos hlt]
        show MultiPoly.varY ⟨i.val, hlt⟩
          = (if (⟨i.val, hlt⟩ : Fin n) = ip' then MultiPoly.const 1 else MultiPoly.varY ⟨i.val, hlt⟩)
        rw [if_neg (fun h => hi (Fin.ext (by rw [← hcast]; exact (congrArg Fin.val h))))]
      · rw [dif_neg hlt]
        show MultiPoly.const 0 = MultiPoly.leadingCoeffY ip' (MultiPoly.const 0)
        rfl
  | add p q ihp ihq =>
    show MultiPoly.dropLastY
        (if MultiPoly.degreeY ip p > MultiPoly.degreeY ip q then MultiPoly.leadingCoeffY ip p
          else if MultiPoly.degreeY ip q > MultiPoly.degreeY ip p then MultiPoly.leadingCoeffY ip q
            else MultiPoly.add (MultiPoly.leadingCoeffY ip p) (MultiPoly.leadingCoeffY ip q))
      = MultiPoly.leadingCoeffY ip' (MultiPoly.add (MultiPoly.dropLastY p) (MultiPoly.dropLastY q))
    rw [show MultiPoly.leadingCoeffY ip' (MultiPoly.add (MultiPoly.dropLastY p) (MultiPoly.dropLastY q))
        = (if MultiPoly.degreeY ip' (MultiPoly.dropLastY p) > MultiPoly.degreeY ip' (MultiPoly.dropLastY q)
            then MultiPoly.leadingCoeffY ip' (MultiPoly.dropLastY p)
            else if MultiPoly.degreeY ip' (MultiPoly.dropLastY q) > MultiPoly.degreeY ip' (MultiPoly.dropLastY p)
              then MultiPoly.leadingCoeffY ip' (MultiPoly.dropLastY q)
              else MultiPoly.add (MultiPoly.leadingCoeffY ip' (MultiPoly.dropLastY p))
                (MultiPoly.leadingCoeffY ip' (MultiPoly.dropLastY q))) from rfl,
        degreeY_dropLastY_eq_prev n ip ip' hcast p, degreeY_dropLastY_eq_prev n ip ip' hcast q]
    by_cases h1 : MultiPoly.degreeY ip p > MultiPoly.degreeY ip q
    · rw [if_pos h1, if_pos h1]; exact ihp
    · rw [if_neg h1, if_neg h1]
      by_cases h2 : MultiPoly.degreeY ip q > MultiPoly.degreeY ip p
      · rw [if_pos h2, if_pos h2]; exact ihq
      · rw [if_neg h2, if_neg h2]
        show MultiPoly.add (MultiPoly.dropLastY (MultiPoly.leadingCoeffY ip p))
            (MultiPoly.dropLastY (MultiPoly.leadingCoeffY ip q)) = _
        rw [ihp, ihq]
  | sub p q ihp ihq =>
    show MultiPoly.dropLastY
        (if MultiPoly.degreeY ip p > MultiPoly.degreeY ip q then MultiPoly.leadingCoeffY ip p
          else if MultiPoly.degreeY ip q > MultiPoly.degreeY ip p
            then MultiPoly.sub (MultiPoly.const 0) (MultiPoly.leadingCoeffY ip q)
            else MultiPoly.sub (MultiPoly.leadingCoeffY ip p) (MultiPoly.leadingCoeffY ip q))
      = MultiPoly.leadingCoeffY ip' (MultiPoly.sub (MultiPoly.dropLastY p) (MultiPoly.dropLastY q))
    rw [show MultiPoly.leadingCoeffY ip' (MultiPoly.sub (MultiPoly.dropLastY p) (MultiPoly.dropLastY q))
        = (if MultiPoly.degreeY ip' (MultiPoly.dropLastY p) > MultiPoly.degreeY ip' (MultiPoly.dropLastY q)
            then MultiPoly.leadingCoeffY ip' (MultiPoly.dropLastY p)
            else if MultiPoly.degreeY ip' (MultiPoly.dropLastY q) > MultiPoly.degreeY ip' (MultiPoly.dropLastY p)
              then MultiPoly.sub (MultiPoly.const 0) (MultiPoly.leadingCoeffY ip' (MultiPoly.dropLastY q))
              else MultiPoly.sub (MultiPoly.leadingCoeffY ip' (MultiPoly.dropLastY p))
                (MultiPoly.leadingCoeffY ip' (MultiPoly.dropLastY q))) from rfl,
        degreeY_dropLastY_eq_prev n ip ip' hcast p, degreeY_dropLastY_eq_prev n ip ip' hcast q]
    by_cases h1 : MultiPoly.degreeY ip p > MultiPoly.degreeY ip q
    · rw [if_pos h1, if_pos h1]; exact ihp
    · rw [if_neg h1, if_neg h1]
      by_cases h2 : MultiPoly.degreeY ip q > MultiPoly.degreeY ip p
      · rw [if_pos h2, if_pos h2]
        show MultiPoly.sub (MultiPoly.dropLastY (MultiPoly.const 0))
            (MultiPoly.dropLastY (MultiPoly.leadingCoeffY ip q)) = _
        rw [ihq]; rfl
      · rw [if_neg h2, if_neg h2]
        show MultiPoly.sub (MultiPoly.dropLastY (MultiPoly.leadingCoeffY ip p))
            (MultiPoly.dropLastY (MultiPoly.leadingCoeffY ip q)) = _
        rw [ihp, ihq]
  | mul p q ihp ihq =>
    show MultiPoly.dropLastY
        (MultiPoly.mul (MultiPoly.leadingCoeffY ip p) (MultiPoly.leadingCoeffY ip q))
      = MultiPoly.leadingCoeffY ip' (MultiPoly.mul (MultiPoly.dropLastY p) (MultiPoly.dropLastY q))
    show MultiPoly.mul (MultiPoly.dropLastY (MultiPoly.leadingCoeffY ip p))
        (MultiPoly.dropLastY (MultiPoly.leadingCoeffY ip q))
      = MultiPoly.mul (MultiPoly.leadingCoeffY ip' (MultiPoly.dropLastY p))
          (MultiPoly.leadingCoeffY ip' (MultiPoly.dropLastY q))
    rw [ihp, ihq]

end MachLib.IterExpDepthN
