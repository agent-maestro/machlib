import MachLib.IterExpDepth3Bridge
import MachLib.ChainExp2NoZeros

/-!
# Depth-3 assembly — dispatch bridging (`Fin 2` inner ↔ `Fin 3` `lcY₂ p`)

The final WF assembly dispatches on the inner `q := dropLastY(lcY₂ p)` (a `MultiPoly 2`), but the
inner-trim and degreeY₂-trim eval-preservations are phrased in terms of `lcY₂ p` (a `MultiPoly 3`). This
file bridges the two arities:

* `dropLastY_eval_zero_of_yfree` — a `y₂`-free `X` that vanishes after `dropLastY` vanishes everywhere.
* `degreeY2_leadingCoeffY1_zero` — `leadingCoeffY ⟨1⟩` preserves `y₂`-freeness.
* `dropLastY_leadingCoeffY1_commute` — `dropLastY` commutes with `leadingCoeffY ⟨1⟩` (the latter only
  reads `degreeY₁`, which `dropLastY` preserves — `degreeY1_dropLastY`).

Path B; no `sorry`.
-/

namespace MachLib.IterExpDepth3Assembly

open MachLib.Real
open MachLib.MultiPolyMod
open MachLib.MultiPolyMod.MultiPoly
open MachLib.IterExpDepth3Bridge

/-- A `y₂`-free `X` whose `dropLastY` vanishes on every `Fin 2` environment vanishes on every `Fin 3`
environment (`dropLastY` preserves eval, and `y₂`-freeness makes the last coordinate irrelevant). -/
theorem dropLastY_eval_zero_of_yfree (X : MultiPoly 3)
    (hX : MultiPoly.degreeY (⟨2, by omega⟩ : Fin 3) X = 0)
    (h : ∀ (x : Real) (env2 : Fin 2 → Real), MultiPoly.eval (MultiPoly.dropLastY X) x env2 = 0) :
    ∀ (x : Real) (env3 : Fin 3 → Real), MultiPoly.eval X x env3 = 0 := by
  intro x env3
  rw [← MultiPoly.eval_dropLastY X hX x env3]
  exact h x _

set_option maxHeartbeats 1200000 in
/-- `leadingCoeffY ⟨1⟩` preserves `y₂`-freeness. -/
theorem degreeY2_leadingCoeffY1_zero : ∀ (X : MultiPoly 3),
    MultiPoly.degreeY (⟨2, by omega⟩ : Fin 3) X = 0 →
    MultiPoly.degreeY (⟨2, by omega⟩ : Fin 3)
      (MultiPoly.leadingCoeffY (⟨1, by omega⟩ : Fin 3) X) = 0 := by
  intro X
  induction X with
  | const c => intro _; rfl
  | varX => intro _; rfl
  | varY i =>
    intro hj
    show MultiPoly.degreeY (⟨2, by omega⟩ : Fin 3)
      (if i = (⟨1, by omega⟩ : Fin 3) then MultiPoly.const 1 else MultiPoly.varY i) = 0
    by_cases hi : i = (⟨1, by omega⟩ : Fin 3)
    · rw [if_pos hi]; rfl
    · rw [if_neg hi]; exact hj
  | add p q ihp ihq =>
    intro hj
    have hmax : Nat.max (MultiPoly.degreeY (⟨2, by omega⟩ : Fin 3) p)
        (MultiPoly.degreeY (⟨2, by omega⟩ : Fin 3) q) = 0 := hj
    have hp : MultiPoly.degreeY (⟨2, by omega⟩ : Fin 3) p = 0 := by
      have hle : MultiPoly.degreeY (⟨2, by omega⟩ : Fin 3) p
          ≤ Nat.max (MultiPoly.degreeY (⟨2, by omega⟩ : Fin 3) p)
              (MultiPoly.degreeY (⟨2, by omega⟩ : Fin 3) q) := Nat.le_max_left _ _
      omega
    have hq : MultiPoly.degreeY (⟨2, by omega⟩ : Fin 3) q = 0 := by
      have hle : MultiPoly.degreeY (⟨2, by omega⟩ : Fin 3) q
          ≤ Nat.max (MultiPoly.degreeY (⟨2, by omega⟩ : Fin 3) p)
              (MultiPoly.degreeY (⟨2, by omega⟩ : Fin 3) q) := Nat.le_max_right _ _
      omega
    show MultiPoly.degreeY (⟨2, by omega⟩ : Fin 3)
      (if MultiPoly.degreeY (⟨1, by omega⟩ : Fin 3) p > MultiPoly.degreeY (⟨1, by omega⟩ : Fin 3) q
        then MultiPoly.leadingCoeffY (⟨1, by omega⟩ : Fin 3) p
        else if MultiPoly.degreeY (⟨1, by omega⟩ : Fin 3) q > MultiPoly.degreeY (⟨1, by omega⟩ : Fin 3) p
          then MultiPoly.leadingCoeffY (⟨1, by omega⟩ : Fin 3) q
          else MultiPoly.add (MultiPoly.leadingCoeffY (⟨1, by omega⟩ : Fin 3) p)
            (MultiPoly.leadingCoeffY (⟨1, by omega⟩ : Fin 3) q)) = 0
    by_cases h1 : MultiPoly.degreeY (⟨1, by omega⟩ : Fin 3) p > MultiPoly.degreeY (⟨1, by omega⟩ : Fin 3) q
    · rw [if_pos h1]; exact ihp hp
    · rw [if_neg h1]
      by_cases h2 : MultiPoly.degreeY (⟨1, by omega⟩ : Fin 3) q > MultiPoly.degreeY (⟨1, by omega⟩ : Fin 3) p
      · rw [if_pos h2]; exact ihq hq
      · rw [if_neg h2]
        show Nat.max (MultiPoly.degreeY (⟨2, by omega⟩ : Fin 3)
              (MultiPoly.leadingCoeffY (⟨1, by omega⟩ : Fin 3) p))
            (MultiPoly.degreeY (⟨2, by omega⟩ : Fin 3)
              (MultiPoly.leadingCoeffY (⟨1, by omega⟩ : Fin 3) q)) = 0
        rw [ihp hp, ihq hq]; exact Nat.max_self 0
  | sub p q ihp ihq =>
    intro hj
    have hmax : Nat.max (MultiPoly.degreeY (⟨2, by omega⟩ : Fin 3) p)
        (MultiPoly.degreeY (⟨2, by omega⟩ : Fin 3) q) = 0 := hj
    have hp : MultiPoly.degreeY (⟨2, by omega⟩ : Fin 3) p = 0 := by
      have hle : MultiPoly.degreeY (⟨2, by omega⟩ : Fin 3) p
          ≤ Nat.max (MultiPoly.degreeY (⟨2, by omega⟩ : Fin 3) p)
              (MultiPoly.degreeY (⟨2, by omega⟩ : Fin 3) q) := Nat.le_max_left _ _
      omega
    have hq : MultiPoly.degreeY (⟨2, by omega⟩ : Fin 3) q = 0 := by
      have hle : MultiPoly.degreeY (⟨2, by omega⟩ : Fin 3) q
          ≤ Nat.max (MultiPoly.degreeY (⟨2, by omega⟩ : Fin 3) p)
              (MultiPoly.degreeY (⟨2, by omega⟩ : Fin 3) q) := Nat.le_max_right _ _
      omega
    show MultiPoly.degreeY (⟨2, by omega⟩ : Fin 3)
      (if MultiPoly.degreeY (⟨1, by omega⟩ : Fin 3) p > MultiPoly.degreeY (⟨1, by omega⟩ : Fin 3) q
        then MultiPoly.leadingCoeffY (⟨1, by omega⟩ : Fin 3) p
        else if MultiPoly.degreeY (⟨1, by omega⟩ : Fin 3) q > MultiPoly.degreeY (⟨1, by omega⟩ : Fin 3) p
          then MultiPoly.sub (MultiPoly.const 0) (MultiPoly.leadingCoeffY (⟨1, by omega⟩ : Fin 3) q)
          else MultiPoly.sub (MultiPoly.leadingCoeffY (⟨1, by omega⟩ : Fin 3) p)
            (MultiPoly.leadingCoeffY (⟨1, by omega⟩ : Fin 3) q)) = 0
    by_cases h1 : MultiPoly.degreeY (⟨1, by omega⟩ : Fin 3) p > MultiPoly.degreeY (⟨1, by omega⟩ : Fin 3) q
    · rw [if_pos h1]; exact ihp hp
    · rw [if_neg h1]
      by_cases h2 : MultiPoly.degreeY (⟨1, by omega⟩ : Fin 3) q > MultiPoly.degreeY (⟨1, by omega⟩ : Fin 3) p
      · rw [if_pos h2]
        show Nat.max (MultiPoly.degreeY (⟨2, by omega⟩ : Fin 3) (MultiPoly.const 0))
            (MultiPoly.degreeY (⟨2, by omega⟩ : Fin 3)
              (MultiPoly.leadingCoeffY (⟨1, by omega⟩ : Fin 3) q)) = 0
        rw [ihq hq]; exact Nat.max_self 0
      · rw [if_neg h2]
        show Nat.max (MultiPoly.degreeY (⟨2, by omega⟩ : Fin 3)
              (MultiPoly.leadingCoeffY (⟨1, by omega⟩ : Fin 3) p))
            (MultiPoly.degreeY (⟨2, by omega⟩ : Fin 3)
              (MultiPoly.leadingCoeffY (⟨1, by omega⟩ : Fin 3) q)) = 0
        rw [ihp hp, ihq hq]; exact Nat.max_self 0
  | mul p q ihp ihq =>
    intro hj
    have hadd : MultiPoly.degreeY (⟨2, by omega⟩ : Fin 3) p
        + MultiPoly.degreeY (⟨2, by omega⟩ : Fin 3) q = 0 := hj
    have hp : MultiPoly.degreeY (⟨2, by omega⟩ : Fin 3) p = 0 := by omega
    have hq : MultiPoly.degreeY (⟨2, by omega⟩ : Fin 3) q = 0 := by omega
    show MultiPoly.degreeY (⟨2, by omega⟩ : Fin 3)
      (MultiPoly.mul (MultiPoly.leadingCoeffY (⟨1, by omega⟩ : Fin 3) p)
        (MultiPoly.leadingCoeffY (⟨1, by omega⟩ : Fin 3) q)) = 0
    show MultiPoly.degreeY (⟨2, by omega⟩ : Fin 3) (MultiPoly.leadingCoeffY (⟨1, by omega⟩ : Fin 3) p)
      + MultiPoly.degreeY (⟨2, by omega⟩ : Fin 3) (MultiPoly.leadingCoeffY (⟨1, by omega⟩ : Fin 3) q) = 0
    rw [ihp hp, ihq hq]

set_option maxHeartbeats 1200000 in
/-- **`dropLastY` commutes with `leadingCoeffY ⟨1⟩`.** `leadingCoeffY ⟨1⟩` reads only `degreeY₁`, which
`dropLastY` preserves (`degreeY1_dropLastY`), so the leading-`y₁`-coefficient extraction is unaffected by
dropping the `y₂` variable. -/
theorem dropLastY_leadingCoeffY1_commute : ∀ (X : MultiPoly 3),
    MultiPoly.dropLastY (MultiPoly.leadingCoeffY (⟨1, by omega⟩ : Fin 3) X)
      = MultiPoly.leadingCoeffY (⟨1, by omega⟩ : Fin 2) (MultiPoly.dropLastY X) := by
  intro X
  induction X with
  | const c => rfl
  | varX => rfl
  | varY i =>
    rcases (by omega : i.val = 0 ∨ i.val = 1 ∨ i.val = 2) with h | h | h
    · rw [show i = (⟨0, by omega⟩ : Fin 3) from Fin.ext h]; rfl
    · rw [show i = (⟨1, by omega⟩ : Fin 3) from Fin.ext h]; rfl
    · rw [show i = (⟨2, by omega⟩ : Fin 3) from Fin.ext h]; rfl
  | add p q ihp ihq =>
    show MultiPoly.dropLastY
        (if MultiPoly.degreeY (⟨1, by omega⟩ : Fin 3) p > MultiPoly.degreeY (⟨1, by omega⟩ : Fin 3) q
          then MultiPoly.leadingCoeffY (⟨1, by omega⟩ : Fin 3) p
          else if MultiPoly.degreeY (⟨1, by omega⟩ : Fin 3) q > MultiPoly.degreeY (⟨1, by omega⟩ : Fin 3) p
            then MultiPoly.leadingCoeffY (⟨1, by omega⟩ : Fin 3) q
            else MultiPoly.add (MultiPoly.leadingCoeffY (⟨1, by omega⟩ : Fin 3) p)
              (MultiPoly.leadingCoeffY (⟨1, by omega⟩ : Fin 3) q))
      = MultiPoly.leadingCoeffY (⟨1, by omega⟩ : Fin 2)
          (MultiPoly.add (MultiPoly.dropLastY p) (MultiPoly.dropLastY q))
    rw [show MultiPoly.leadingCoeffY (⟨1, by omega⟩ : Fin 2)
          (MultiPoly.add (MultiPoly.dropLastY p) (MultiPoly.dropLastY q))
        = (if MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) (MultiPoly.dropLastY p)
              > MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) (MultiPoly.dropLastY q)
            then MultiPoly.leadingCoeffY (⟨1, by omega⟩ : Fin 2) (MultiPoly.dropLastY p)
            else if MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) (MultiPoly.dropLastY q)
                > MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) (MultiPoly.dropLastY p)
              then MultiPoly.leadingCoeffY (⟨1, by omega⟩ : Fin 2) (MultiPoly.dropLastY q)
              else MultiPoly.add (MultiPoly.leadingCoeffY (⟨1, by omega⟩ : Fin 2) (MultiPoly.dropLastY p))
                (MultiPoly.leadingCoeffY (⟨1, by omega⟩ : Fin 2) (MultiPoly.dropLastY q))) from rfl,
        degreeY1_dropLastY p, degreeY1_dropLastY q]
    by_cases h1 : MultiPoly.degreeY (⟨1, by omega⟩ : Fin 3) p > MultiPoly.degreeY (⟨1, by omega⟩ : Fin 3) q
    · rw [if_pos h1, if_pos h1]; exact ihp
    · rw [if_neg h1, if_neg h1]
      by_cases h2 : MultiPoly.degreeY (⟨1, by omega⟩ : Fin 3) q > MultiPoly.degreeY (⟨1, by omega⟩ : Fin 3) p
      · rw [if_pos h2, if_pos h2]; exact ihq
      · rw [if_neg h2, if_neg h2]
        show MultiPoly.add (MultiPoly.dropLastY (MultiPoly.leadingCoeffY (⟨1, by omega⟩ : Fin 3) p))
            (MultiPoly.dropLastY (MultiPoly.leadingCoeffY (⟨1, by omega⟩ : Fin 3) q)) = _
        rw [ihp, ihq]
  | sub p q ihp ihq =>
    show MultiPoly.dropLastY
        (if MultiPoly.degreeY (⟨1, by omega⟩ : Fin 3) p > MultiPoly.degreeY (⟨1, by omega⟩ : Fin 3) q
          then MultiPoly.leadingCoeffY (⟨1, by omega⟩ : Fin 3) p
          else if MultiPoly.degreeY (⟨1, by omega⟩ : Fin 3) q > MultiPoly.degreeY (⟨1, by omega⟩ : Fin 3) p
            then MultiPoly.sub (MultiPoly.const 0) (MultiPoly.leadingCoeffY (⟨1, by omega⟩ : Fin 3) q)
            else MultiPoly.sub (MultiPoly.leadingCoeffY (⟨1, by omega⟩ : Fin 3) p)
              (MultiPoly.leadingCoeffY (⟨1, by omega⟩ : Fin 3) q))
      = MultiPoly.leadingCoeffY (⟨1, by omega⟩ : Fin 2)
          (MultiPoly.sub (MultiPoly.dropLastY p) (MultiPoly.dropLastY q))
    rw [show MultiPoly.leadingCoeffY (⟨1, by omega⟩ : Fin 2)
          (MultiPoly.sub (MultiPoly.dropLastY p) (MultiPoly.dropLastY q))
        = (if MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) (MultiPoly.dropLastY p)
              > MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) (MultiPoly.dropLastY q)
            then MultiPoly.leadingCoeffY (⟨1, by omega⟩ : Fin 2) (MultiPoly.dropLastY p)
            else if MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) (MultiPoly.dropLastY q)
                > MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) (MultiPoly.dropLastY p)
              then MultiPoly.sub (MultiPoly.const 0)
                (MultiPoly.leadingCoeffY (⟨1, by omega⟩ : Fin 2) (MultiPoly.dropLastY q))
              else MultiPoly.sub (MultiPoly.leadingCoeffY (⟨1, by omega⟩ : Fin 2) (MultiPoly.dropLastY p))
                (MultiPoly.leadingCoeffY (⟨1, by omega⟩ : Fin 2) (MultiPoly.dropLastY q))) from rfl,
        degreeY1_dropLastY p, degreeY1_dropLastY q]
    by_cases h1 : MultiPoly.degreeY (⟨1, by omega⟩ : Fin 3) p > MultiPoly.degreeY (⟨1, by omega⟩ : Fin 3) q
    · rw [if_pos h1, if_pos h1]; exact ihp
    · rw [if_neg h1, if_neg h1]
      by_cases h2 : MultiPoly.degreeY (⟨1, by omega⟩ : Fin 3) q > MultiPoly.degreeY (⟨1, by omega⟩ : Fin 3) p
      · rw [if_pos h2, if_pos h2]
        show MultiPoly.sub (MultiPoly.dropLastY (MultiPoly.const 0))
            (MultiPoly.dropLastY (MultiPoly.leadingCoeffY (⟨1, by omega⟩ : Fin 3) q)) = _
        rw [ihq]; rfl
      · rw [if_neg h2, if_neg h2]
        show MultiPoly.sub (MultiPoly.dropLastY (MultiPoly.leadingCoeffY (⟨1, by omega⟩ : Fin 3) p))
            (MultiPoly.dropLastY (MultiPoly.leadingCoeffY (⟨1, by omega⟩ : Fin 3) q)) = _
        rw [ihp, ihq]
  | mul p q ihp ihq =>
    show MultiPoly.dropLastY
        (MultiPoly.mul (MultiPoly.leadingCoeffY (⟨1, by omega⟩ : Fin 3) p)
          (MultiPoly.leadingCoeffY (⟨1, by omega⟩ : Fin 3) q))
      = MultiPoly.leadingCoeffY (⟨1, by omega⟩ : Fin 2)
          (MultiPoly.mul (MultiPoly.dropLastY p) (MultiPoly.dropLastY q))
    show MultiPoly.mul (MultiPoly.dropLastY (MultiPoly.leadingCoeffY (⟨1, by omega⟩ : Fin 3) p))
        (MultiPoly.dropLastY (MultiPoly.leadingCoeffY (⟨1, by omega⟩ : Fin 3) q))
      = MultiPoly.mul (MultiPoly.leadingCoeffY (⟨1, by omega⟩ : Fin 2) (MultiPoly.dropLastY p))
          (MultiPoly.leadingCoeffY (⟨1, by omega⟩ : Fin 2) (MultiPoly.dropLastY q))
    rw [ihp, ihq]

end MachLib.IterExpDepth3Assembly
