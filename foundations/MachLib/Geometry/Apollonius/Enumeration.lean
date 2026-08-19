import MachLib.Geometry.Apollonius.SymmetricTriple

/-!
# The count, in list-cardinality form

The exhibit at `monogate.org/proofs/apollonius` carried this disclaimer:

> **NOT PROVED — list-cardinality form.** MachLib is Mathlib-free and has no `Finset` layer; the
> count is a derivation from per-mode theorems plus the antipodal pairing, not a
> `List.length = 8` theorem.

The first clause is true and the inference from it was wrong. Lean's **core** carries `List`,
`List.length`, `List.Nodup` and `Decidable` instances for all of them; `Finset` is a Mathlib
notion and nothing here needs it. `Mode` is a structure of three two-element enumerations with
`DecidableEq`, so the mode half of the count is not merely provable but *decidable* — every
enumeration theorem below closes by `decide`.

What genuinely needed care was the solution half, and only because the roots are supplied by an
existential rather than a formula. That is handled by producing the list inside the statement
(`eight_solutions`) rather than as a `noncomputable def`, which keeps `Classical.choose` out of the
signature while still delivering a `List` whose `length` is `8` by computation.
-/

namespace MachLib
namespace Geometry
namespace Apollonius

open Sign

/-! ## The eight modes -/

/-- All eight tangency modes. Order is the binary counting order on `(sA, sB, sC)`. -/
def allModes : List Mode :=
  [⟨outer, outer, outer⟩, ⟨outer, outer, inner⟩, ⟨outer, inner, outer⟩, ⟨outer, inner, inner⟩,
   ⟨inner, outer, outer⟩, ⟨inner, outer, inner⟩, ⟨inner, inner, outer⟩, ⟨inner, inner, inner⟩]

/-- **Eight. By computation, not by counting in prose.** -/
theorem allModes_length : allModes.length = 8 := rfl

/-- No mode is listed twice. -/
theorem allModes_nodup : allModes.Nodup := by decide

/-- **And nothing is missing.** Length alone would not be a count — a list of eight things is only
"the eight modes" once every mode is known to be in it. -/
theorem allModes_complete (m : Mode) : m ∈ allModes := by
  cases m with
  | mk a b c => cases a <;> cases b <;> cases c <;> decide

/-! ## Four classes, in the same form -/

/-- Every listed representative really is canonical.

`canonicalModes_length`, `canonicalModes_nodup` and `mem_canonicalModes_iff` were already in
`Mode.lean`, so the **four**-class half of the count has been in list-cardinality form all along.
Only the eight-mode list and the solution list were missing, which is worth noting because the
exhibit's disclaimer implied the whole count was informal. -/
theorem canonicalModes_all_canonical : ∀ m ∈ canonicalModes, m.IsCanonical := by decide

/-- **The antipodal pairing, as a list identity.** Appending the four canonical modes to their four
antipodes reproduces the eight — with no repetition, and omitting nothing.

This is `eightModes_reduce_to_four` in cardinality form: `4 + 4 = 8`, with the two halves disjoint.
Stated as three separate facts because each fails differently — a length claim misses duplicates, a
`Nodup` claim misses omissions, and a completeness claim misses over-counting. -/
theorem canonical_plus_anti_length :
    (canonicalModes ++ canonicalModes.map Mode.anti).length = 8 := rfl

theorem canonical_plus_anti_nodup :
    (canonicalModes ++ canonicalModes.map Mode.anti).Nodup := by decide

theorem canonical_plus_anti_complete (m : Mode) :
    m ∈ canonicalModes ++ canonicalModes.map Mode.anti := by
  cases m with
  | mk a b c => cases a <;> cases b <;> cases c <;> decide

/-- **Each mode is canonical or the antipode of a canonical one, never both.** The set-level
statement behind the list identity above. -/
theorem canonical_or_anti (m : Mode) :
    (m ∈ canonicalModes ∧ m.anti ∉ canonicalModes)
    ∨ (m ∉ canonicalModes ∧ m.anti ∈ canonicalModes) := by
  cases m with
  | mk a b c => cases a <;> cases b <;> cases c <;> decide


/-! ## The eight solutions

The mode half above is decidable. This half is not: the roots come from `QM_two_roots_of_gp` as an
existential, so the list is produced *inside* the statement rather than as a `noncomputable def`.
That keeps `Classical.choose` out of every signature while still delivering an actual `List` whose
`length` reduces to `8` by computation.
-/

namespace SymmetricTriple

variable (d ρ : Real)

private theorem neg_ne_neg {a b : Real} (h : a ≠ b) : -a ≠ -b := by
  intro he
  refine h ?_
  have e1 : a = -(-a) := by mach_ring
  have e2 : b = -(-b) := by mach_ring
  rw [e1, e2, he]

/-- A solution, packaged: the mode it belongs to, its centre, and its **positive** radius. -/
abbrev Sol := Mode × Real × Real × Real

/-- What it means for a packaged solution to be genuine. -/
def IsSol (hρ : 0 < ρ) (s : Sol) : Prop :=
  0 < s.2.2.2 ∧ SolvesMode (cA ρ hρ) (cB d ρ hρ) (cC d ρ hρ) s.1 s.2.1 s.2.2.1 s.2.2.2

/-- **One class contributes exactly two positive-radius solutions, and they are distinct.**

The two roots of the class quadratic are distinct and nonzero, so each decodes — by
`decode_of_canonical` — to a positive-radius solution, in the class itself or in its antipode.
Distinctness survives every combination: two roots of the same sign give the same mode and
different radii; roots of opposite sign give different modes, since `anti_ne`. -/
theorem two_solutions_per_class (gp : SymmetricGeneralPosition d ρ) (m : Mode) :
    ∃ s₁ s₂ : Sol, IsSol d ρ (gp_rho_pos d ρ gp) s₁ ∧ IsSol d ρ (gp_rho_pos d ρ gp) s₂
      ∧ s₁ ≠ s₂
      ∧ (s₁.1 = m ∨ s₁.1 = m.anti) ∧ (s₂.1 = m ∨ s₂.1 = m.anti) := by
  have hρ := gp_rho_pos d ρ gp
  have hsep : (1 + 1) * ρ < d := gp.2.1
  obtain ⟨r₁, r₂, hne, hq₁, hq₂⟩ := QM_two_roots_of_gp d ρ gp m
  obtain ⟨x₁, y₁, hs₁⟩ := solution_of_root d ρ gp m r₁ hq₁
  obtain ⟨x₂, y₂, hs₂⟩ := solution_of_root d ρ gp m r₂ hq₂
  have hz₁ : r₁ ≠ 0 := root_ne_zero d ρ hρ hsep m hq₁
  have hz₂ : r₂ ≠ 0 := root_ne_zero d ρ hρ hsep m hq₂
  rcases decode_of_canonical (cA ρ hρ) (cB d ρ hρ) (cC d ρ hρ) m x₁ y₁ r₁ hz₁ hs₁ with
    ⟨hp₁, hd₁⟩ | ⟨hp₁, hd₁⟩ <;>
  rcases decode_of_canonical (cA ρ hρ) (cB d ρ hρ) (cC d ρ hρ) m x₂ y₂ r₂ hz₂ hs₂ with
    ⟨hp₂, hd₂⟩ | ⟨hp₂, hd₂⟩
  · -- both positive: same mode, different radii
    exact ⟨(m, x₁, y₁, r₁), (m, x₂, y₂, r₂), ⟨hp₁, hd₁⟩, ⟨hp₂, hd₂⟩, by
      intro he; exact hne (congrArg (fun t => t.2.2.2) he), Or.inl rfl, Or.inl rfl⟩
  · -- r₁ > 0, r₂ < 0: modes differ
    exact ⟨(m, x₁, y₁, r₁), (m.anti, x₂, y₂, -r₂), ⟨hp₁, hd₁⟩, ⟨hp₂, hd₂⟩, by
      intro he
      exact (Mode.anti_ne m) (congrArg (fun t => t.1) he).symm, Or.inl rfl, Or.inr rfl⟩
  · -- r₁ < 0, r₂ > 0: modes differ
    exact ⟨(m.anti, x₁, y₁, -r₁), (m, x₂, y₂, r₂), ⟨hp₁, hd₁⟩, ⟨hp₂, hd₂⟩, by
      intro he
      exact (Mode.anti_ne m) (congrArg (fun t => t.1) he), Or.inr rfl, Or.inl rfl⟩
  · -- both negative: same mode, different radii
    exact ⟨(m.anti, x₁, y₁, -r₁), (m.anti, x₂, y₂, -r₂), ⟨hp₁, hd₁⟩, ⟨hp₂, hd₂⟩, by
      intro he
      exact (neg_ne_neg hne) (congrArg (fun t => t.2.2.2) he), Or.inr rfl, Or.inr rfl⟩

/-- Two packaged solutions with different modes are different solutions. -/
private theorem sol_ne_of_mode_ne {s t : Sol} (h : s.1 ≠ t.1) : s ≠ t := fun he =>
  h (congrArg (fun z => z.1) he)

/-- **The eight, as a list of length eight.**

`length = 8` holds by computation. `Nodup` is the clause that makes the length mean something: a
list of eight things is a count only once no entry repeats. And every entry is a genuine
positive-radius solution of the mode it is labelled with.

Distinctness has two sources and both are needed. *Within* a class it is the two roots of the class
quadratic being distinct — same mode with different radii, or opposite modes. *Across* classes it is
that the four canonical modes and their four antipodes are eight distinct modes, which is
`canonical_plus_anti_nodup` and is decidable. -/
theorem eight_solutions (gp : SymmetricGeneralPosition d ρ) :
    ∃ L : List Sol, L.length = 8
      ∧ (∀ s ∈ L, IsSol d ρ (gp_rho_pos d ρ gp) s)
      ∧ L.Nodup := by
  obtain ⟨a₁, a₂, ha₁, ha₂, hane, hma₁, hma₂⟩ :=
    two_solutions_per_class d ρ gp ⟨outer, outer, outer⟩
  obtain ⟨b₁, b₂, hb₁, hb₂, hbne, hmb₁, hmb₂⟩ :=
    two_solutions_per_class d ρ gp ⟨outer, outer, inner⟩
  obtain ⟨c₁, c₂, hc₁, hc₂, hcne, hmc₁, hmc₂⟩ :=
    two_solutions_per_class d ρ gp ⟨outer, inner, outer⟩
  obtain ⟨e₁, e₂, he₁, he₂, hene, hme₁, hme₂⟩ :=
    two_solutions_per_class d ρ gp ⟨outer, inner, inner⟩
  refine ⟨[a₁, a₂, b₁, b₂, c₁, c₂, e₁, e₂], rfl, ?_, ?_⟩
  · intro s hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with h|h|h|h|h|h|h|h <;> subst h <;>
      first
        | exact ha₁ | exact ha₂ | exact hb₁ | exact hb₂
        | exact hc₁ | exact hc₂ | exact he₁ | exact he₂
  · -- cross-class disequalities are mode disequalities, and those are decidable
    have cross : ∀ {s t : Sol} {m m' : Mode},
        (s.1 = m ∨ s.1 = m.anti) → (t.1 = m' ∨ t.1 = m'.anti) →
        (m ≠ m' ∧ m ≠ m'.anti ∧ m.anti ≠ m' ∧ m.anti ≠ m'.anti) → s ≠ t := by
      rintro s t m m' (h|h) (h'|h') ⟨d1, d2, d3, d4⟩ <;>
        refine sol_ne_of_mode_ne ?_ <;> rw [h, h']
      · exact d1
      · exact d2
      · exact d3
      · exact d4
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, List.nodup_nil,
      not_or, and_true]
    repeat' apply And.intro
    all_goals
      first
        | trivial
        | exact hane | exact hbne | exact hcne | exact hene
        | exact cross hma₁ hmb₁ (by decide) | exact cross hma₁ hmb₂ (by decide)
        | exact cross hma₁ hmc₁ (by decide) | exact cross hma₁ hmc₂ (by decide)
        | exact cross hma₁ hme₁ (by decide) | exact cross hma₁ hme₂ (by decide)
        | exact cross hma₂ hmb₁ (by decide) | exact cross hma₂ hmb₂ (by decide)
        | exact cross hma₂ hmc₁ (by decide) | exact cross hma₂ hmc₂ (by decide)
        | exact cross hma₂ hme₁ (by decide) | exact cross hma₂ hme₂ (by decide)
        | exact cross hmb₁ hmc₁ (by decide) | exact cross hmb₁ hmc₂ (by decide)
        | exact cross hmb₁ hme₁ (by decide) | exact cross hmb₁ hme₂ (by decide)
        | exact cross hmb₂ hmc₁ (by decide) | exact cross hmb₂ hmc₂ (by decide)
        | exact cross hmb₂ hme₁ (by decide) | exact cross hmb₂ hme₂ (by decide)
        | exact cross hmc₁ hme₁ (by decide) | exact cross hmc₁ hme₂ (by decide)
        | exact cross hmc₂ hme₁ (by decide) | exact cross hmc₂ hme₂ (by decide)

end SymmetricTriple

end Apollonius
end Geometry
end MachLib
