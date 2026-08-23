import MachLib.BipevTail

/-!
# The descent: a relation shorter than the minimal one is entirely trivial

The gap named at the end of `BipevTail`, and the last structural piece of the differential route.

The eliminated relation has its top coefficient eventually zero, so by `bipev_concat` it agrees with
its own truncation. That truncation is a relation too, and it is *shorter* — so minimality forbids it
from being proper, forcing **its** top coefficient to be eventually zero as well, and the argument
repeats. The conclusion is that every coefficient of the eliminated relation vanishes eventually,
which is the single-coefficient identity `cleared_relation_impossible` consumes.

## Why the induction runs from the right

Every other list induction in this arc runs from the head, because `pev`, `pnorm`, `pmul` and
`bipev` all recurse there. This one cannot: "top coefficient" is the *last* entry, and the descent
is precisely peeling it. So the list is decomposed as `Es₀ ++ [A]` and the recursion is on the
length budget rather than on the constructor — the same `Nat`-budget shape as `exists_minimal_length`,
for the same reason.

## What it does not need

No minimality of the *eliminated* relation, no properness, and nothing about `q`. The only inputs
are that the ambient minimal relation exists and that the shorter one is a relation at all. That is
worth noting because the natural first statement — phrased in terms of the eliminated relation's own
degree — would have needed the elimination's details, and this does not.
-/

namespace MachLib

open Real

/-! ## Dropping a vanishing top coefficient -/

/-- A relation whose final coefficient is eventually zero truncates to a relation. -/
theorem evRel_dropLast {S : Real → Real} {Es₀ : List (List Real)} {A : List Real}
    (hrel : EvRel S (Es₀ ++ [A])) (hA : EvZeroF (pev A)) : EvRel S Es₀ := by
  obtain ⟨X₁, hX₁, h₁⟩ := hrel
  obtain ⟨X₂, hX₂, h₂⟩ := hA
  obtain ⟨X, hX, hle1, hle2⟩ := two_bounds' hX₁ hX₂
  refine ⟨X, hX, fun x hx => ?_⟩
  have hb := h₁ x (le_trans hle1 hx)
  rw [bipev_concat Es₀ A x (exp (S x)), h₂ x (le_trans hle2 hx)] at hb
  have e : bipev Es₀ x (exp (S x)) + powNat (exp (S x)) Es₀.length * 0
      = bipev Es₀ x (exp (S x)) := by mach_ring
  rw [e] at hb
  exact hb

/-! ## The descent -/

/-- **Every coefficient of a too-short relation is eventually zero.** The induction is on a length
budget, decomposing from the right — see the module docstring. -/
theorem all_coeffs_evZero_of_shorter {S : Real → Real} {Ms : List (List Real)}
    (hmin : ∀ Ns : List (List Real), ProperRel S Ns → Ms.length ≤ Ns.length) :
    ∀ (n : Nat) (Es : List (List Real)), Es.length ≤ n → EvRel S Es → Es.length < Ms.length →
      ∀ A : List Real, A ∈ Es → EvZeroF (pev A) := by
  intro n
  induction n with
  | zero =>
      intro Es hlen _ _ A hA
      cases Es with
      | nil => exact absurd hA (by simp)
      | cons _ _ => simp at hlen
  | succ n ih =>
      intro Es hlen hrel hlt A hA
      cases hEs : Es with
      | nil => rw [hEs] at hA; exact absurd hA (by simp)
      | cons E Es' =>
          -- decompose at the leading coefficient
          have hne : Es ≠ [] := by rw [hEs]; simp
          obtain ⟨Es₀, A₀, hsplit⟩ : ∃ Es₀ A₀, Es = Es₀ ++ [A₀] :=
            ⟨Es.dropLast, Es.getLast hne, (List.dropLast_concat_getLast hne).symm⟩
          -- the top coefficient must be eventually zero, or minimality is contradicted
          have hA₀ : EvZeroF (pev A₀) := by
            rcases Classical.em (EvZeroF (pev A₀)) with h | h
            · exact h
            · exfalso
              have hproper : ProperRel S Es := ⟨hrel, Es₀, A₀, hsplit, h⟩
              have := hmin Es hproper
              omega
          -- so the truncation is a shorter relation; recurse
          have hrel₀ : EvRel S Es₀ := by
            rw [hsplit] at hrel
            exact evRel_dropLast hrel hA₀
          have hlen₀ : Es₀.length + 1 = Es.length := by rw [hsplit]; simp
          have hIH := ih Es₀ (by omega) hrel₀ (by omega)
          -- membership splits at the append
          rw [hsplit] at hA
          rcases List.mem_append.mp hA with hm | hm
          · exact hIH A hm
          · have : A = A₀ := by simpa using hm
            rw [this]; exact hA₀

/-- The budget-free form. -/
theorem all_coeffs_evZero_of_shorter' {S : Real → Real} {Ms Es : List (List Real)}
    (hmin : ∀ Ns : List (List Real), ProperRel S Ns → Ms.length ≤ Ns.length)
    (hrel : EvRel S Es) (hlt : Es.length < Ms.length) :
    ∀ A : List Real, A ∈ Es → EvZeroF (pev A) :=
  all_coeffs_evZero_of_shorter hmin Es.length Es (Nat.le_refl _) hrel hlt

end MachLib
