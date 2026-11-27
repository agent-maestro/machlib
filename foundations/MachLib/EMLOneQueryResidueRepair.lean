import MachLib.EMLOneQueryReflect
import MachLib.AnalyticFiniteZerosReal

/-!
# `OneQueryLevelSetResidue` is FALSE as stated, and the repaired residue

## The finding

`OneQueryLevelSetResidue` (`EMLOneQueryReflect`) is `OneQueryTailRigidity ∧ OneQueryBoundedLevelFinite`.
The second conjunct asks, for **every** one-query term `T`, level `c` and window `[-X, X]`, for a
finite list containing the level set inside the window:

    ∀ T, fOcc T = 1 → ∀ c X, 1 ≤ X → ∃ E, ∀ x, -X ≤ x → x ≤ X → T x = c → x ∈ E

That is false whenever `T` is constantly `c`, and a one-query term can be: `0 · F(x) + c` has exactly
one `F` node and evaluates to `c` at every real. Its level set is all of `ℝ`, and no list exhausts
`(0, 1)`. So the open ledger row can never be discharged — it is *refutable*, and the reduction
`oneQueryLevelSet_of_residue` was reducing a (presumably true) statement to a false one.

`OneQueryLevelSet` itself is untouched: at this `T` its first disjunct holds with `E = []`.

## The repair

The reduction only ever calls the bounded half after BOTH tails have been shown to miss the level
(its last branch: "both tails miss the level, so the level set is trapped in `[-X, X]`"). Carrying
those two facts as hypotheses gives `OneQueryBoundedLevelFiniteOffTails`, which the constant term no
longer refutes (its tails hit the level), and `oneQueryLevelSet_of_residue'` is the same proof.

Nothing here proves either half of the repaired residue.
-/

namespace MachLib

open Real

/-- **No finite list exhausts an open interval.** Density plus induction on the list: if the point
the induction hands back is the new head, ask again strictly to its left. -/
theorem exists_between_not_mem : ∀ (E : List Real) (a b : Real), a < b →
    ∃ x : Real, a < x ∧ x < b ∧ x ∉ E := by
  intro E
  induction E with
  | nil =>
      intro a b hab
      obtain ⟨m, h1, h2⟩ := exists_between a b hab
      exact ⟨m, h1, h2, fun h => by cases h⟩
  | cons c cs ih =>
      intro a b hab
      obtain ⟨x, hax, hxb, hx⟩ := ih a b hab
      rcases Classical.em (x = c) with hxc | hxc
      · obtain ⟨y, hay, hyx, hy⟩ := ih a x hax
        refine ⟨y, hay, lt_trans_ax hyx hxb, fun hmem => ?_⟩
        rcases List.mem_cons.mp hmem with he | hm
        · rw [he, ← hxc] at hyx
          exact lt_irrefl_ax x hyx
        · exact hy hm
      · refine ⟨x, hax, hxb, fun hmem => ?_⟩
        rcases List.mem_cons.mp hmem with he | hm
        · exact hxc he
        · exact hx hm

/-- The constant one-query term `0 · F(x) + c`. -/
noncomputable def constOneQuery (c : Real) : FTerm :=
  FTerm.add (FTerm.mul (FTerm.const 0) (FTerm.F FTerm.var)) (FTerm.const c)

/-- It really is a ONE-query term: the `F` node is counted even though its value is discarded. -/
theorem constOneQuery_fOcc (c : Real) : fOcc (constOneQuery c) = 1 := rfl

/-- And it is constant, at every real. -/
theorem constOneQuery_eval (c x : Real) : (constOneQuery c).eval x = c := by
  show (0 : Real) * Fbasis x + c = c
  mach_mpoly [Fbasis x, c]

/-- **The bounded half of the residue is false.** -/
theorem not_oneQueryBoundedLevelFinite : ¬ OneQueryBoundedLevelFinite := by
  intro h
  obtain ⟨E, hE⟩ := h (constOneQuery 0) (constOneQuery_fOcc 0) 0 1 (le_refl 1)
  obtain ⟨x, h0x, hx1, hx⟩ := exists_between_not_mem E 0 1 zero_lt_one_ax
  have hneg : (0 : Real) - 1 < 0 := by
    have v := add_lt_add_left zero_lt_one_ax ((0 : Real) - 1)
    have e1 : (0 : Real) - 1 + 0 = 0 - 1 := by mach_ring
    have e2 : (0 : Real) - 1 + 1 = 0 := by mach_ring
    rw [e1, e2] at v; exact v
  exact hx (hE x (le_of_lt (lt_trans_ax hneg h0x)) (le_of_lt hx1) (constOneQuery_eval 0 x))

/-- **So the open ledger row is refuted as stated.** -/
theorem not_oneQueryLevelSetResidue : ¬ OneQueryLevelSetResidue :=
  fun h => not_oneQueryBoundedLevelFinite h.2

/-! ## The repaired residue -/

/-- **Residue 2, repaired.** Finiteness on the window, *given that both tails miss the level* — which
is the only situation the reduction consults it in. -/
def OneQueryBoundedLevelFiniteOffTails : Prop :=
  ∀ T : FTerm, fOcc T = 1 → ∀ c X : Real, 1 ≤ X →
    (∀ x : Real, X ≤ x → T.eval x ≠ c) →
    (∀ x : Real, X ≤ x → T.eval (0 - x) ≠ c) →
    ∃ E : List Real, ∀ x : Real, 0 - X ≤ x → x ≤ X → T.eval x = c → x ∈ E

/-- The repaired residue, as one proposition. -/
def OneQueryLevelSetResidue' : Prop :=
  OneQueryTailRigidity ∧ OneQueryBoundedLevelFiniteOffTails

/-- The constant term does not refute the repaired form: its tails hit the level, so the two new
hypotheses are false there and the statement is silent. -/
theorem constOneQuery_tail_hits (c X : Real) :
    ¬ (∀ x : Real, X ≤ x → (constOneQuery c).eval x ≠ c) :=
  fun h => h X (le_refl X) (constOneQuery_eval c X)

/-- **The reduction, against the repaired residue.** Same proof as `oneQueryLevelSet_of_residue`;
the two tail facts it had in hand are now passed to the bounded half instead of being dropped. -/
theorem oneQueryLevelSet_of_residue' (hRes : OneQueryLevelSetResidue') : OneQueryLevelSet := by
  obtain ⟨hR, hB⟩ := hRes
  intro T h c
  obtain ⟨X, hX, hpos, hneg⟩ := one_query_level_set_two_sided T h c
  rcases hpos with hall | hposnone
  · obtain ⟨E, hE⟩ := hR T h c X hX (Or.inl hall)
    exact ⟨E, Or.inl hE⟩
  rcases hneg with hall | hnegnone
  · obtain ⟨E, hE⟩ := hR T h c X hX (Or.inr hall)
    exact ⟨E, Or.inl hE⟩
  obtain ⟨E, hE⟩ := hB T h c X hX hposnone hnegnone
  refine ⟨E, Or.inr (fun x hx => ?_)⟩
  rcases lt_total x (0 - X) with hlo | hlo | hlo
  · exfalso
    refine hnegnone (0 - x) ?_ ?_
    · have u := add_lt_add_left hlo (0 - x + X)
      have e1 : 0 - x + X + x = X := by mach_ring
      have e2 : 0 - x + X + (0 - X) = 0 - x := by mach_ring
      rw [e1, e2] at u; exact le_of_lt u
    · have e : 0 - (0 - x) = x := by mach_ring
      rw [e]; exact hx
  · refine hE x (le_of_eq hlo.symm) ?_ hx
    rcases lt_total (0 - X) X with hu | hu | hu
    · exact le_of_lt (hlo ▸ hu)
    · exact le_of_eq (hlo ▸ hu)
    · exfalso
      have hXpos : (0 : Real) < X := lt_of_lt_of_le zero_lt_one_ax hX
      have u := add_lt_add_left hu X
      have e : X + (0 - X) = 0 := by mach_ring
      rw [e] at u
      have v := add_lt_add_left hXpos X
      have e2 : X + 0 = X := by mach_ring
      rw [e2] at v
      exact lt_irrefl_ax X (lt_trans_ax (lt_trans_ax v u) hXpos)
  · rcases lt_total X x with hhi | hhi | hhi
    · exact absurd (hposnone x (le_of_lt hhi) hx) (fun k => k)
    · exact absurd (hposnone x (le_of_eq hhi) hx) (fun k => k)
    · exact hE x (le_of_lt hlo) (le_of_lt hhi) hx

end MachLib
