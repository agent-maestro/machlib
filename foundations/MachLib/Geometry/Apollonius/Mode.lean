import MachLib.Geometry.Circle
import MachLib.QuadraticRoots

/-!
# Tangency modes, and the antipodal law

A solution of Apollonius' problem is tangent to each input circle either externally or internally,
so the naive enumeration carries **eight** sign triples. Each triple's algebra reduces to a
quadratic in the radius, which would suggest as many as sixteen algebraic candidates against a
classical generic count of eight.

The discrepancy is not resolved by discarding roots. It is resolved by a symmetry:

    (x, y, r) solves mode σ  ⟺  (x, y, −r) solves mode −σ

Every `σ`-dependent term in the expanded tangency equation carries exactly one factor of `r`, and
`x² + y² − r²` is even in `r`; so negating the radius and the mode together returns the identical
system. The eight modes are therefore **four antipodal classes**, each carrying one quadratic whose
two roots split by sign between the class's two modes. Four classes times two roots is eight — the
factor of two was already spent, and there was never a sixteen.

## What this file is careful about

* The eight-element `Mode` is defined first, because it is the honest mathematical object. The four
  classes are then *derived* (`canonicalModes`, `eightModes_reduce_to_four`), not encoded as a
  four-constructor datatype — a datatype with four constructors would make the conclusion true by
  construction and prove nothing.
* The algebraic layer admits **any** signed `r`, including `0`. A degenerate configuration really
  can produce a zero root, and the solver has to be able to represent that candidate in order to
  reject it. Requiring `r ≠ 0` and passing to `|r|` is the job of the certification layer, not of
  this one; the zero case is rejected here, never made unrepresentable.
* `Mode` and `Sign` carry `DecidableEq` and no `Real` fields, so the mode half of a candidate is
  decidable syntax. Only `Sign.val` crosses into `Real`, and it is `noncomputable` — the same
  syntax/semantics split `EMLCertifiedSynthesis` draws.

Beware the naive invariant this replaces: **"one solution per mode" is false.** For
`A = (0,0,1)`, `B = (4,0,2)`, `C = (1,4,3)` the mode `(−1,+1,+1)` carries two solutions and its
antipode none. What is invariant is two roots per *class*, not one solution per *mode*.
-/

namespace MachLib
namespace Geometry
namespace Apollonius

open Real

/-- A tangency sign: `outer` is external tangency (`σ = +1`), `inner` internal (`σ = −1`). -/
inductive Sign where
  | outer : Sign
  | inner : Sign
  deriving DecidableEq, Repr

namespace Sign

/-- The sign as a real coefficient. The only bridge from this syntax into `Real`. -/
noncomputable def val : Sign → Real
  | outer => 1
  | inner => -1

/-- Sign reversal. -/
def flip : Sign → Sign
  | outer => inner
  | inner => outer

@[simp] theorem flip_flip (s : Sign) : s.flip.flip = s := by cases s <;> rfl

/-- **`σ² = 1`.** Obvious, and load-bearing: `mach_mpoly` treats `Sign.val` as an opaque atom, so
every expansion of a tangency equation needs this supplied explicitly or the `σ²ρ²` term will not
collapse to `ρ²`. Omitting it does not produce a wrong-looking goal — it produces `1 = 0`. -/
@[simp] theorem val_sq (s : Sign) : s.val * s.val = 1 := by
  cases s
  · show (1 : Real) * 1 = 1; mach_ring
  · show (-1 : Real) * -1 = 1; mach_ring

/-- `Sign.val` is injective — `1 ≠ -1`. -/
theorem val_inj {s t : Sign} (h : s.val = t.val) : s = t := by
  have contra : ∀ _ : (1 : Real) = -1, False := by
    intro h1
    have e : (1 : Real) + 1 = -1 + 1 := congrArg (fun z => z + 1) h1
    have z : (-1 : Real) + 1 = 0 := by mach_ring
    rw [z] at e
    have hpos : (0 : Real) < 1 + 1 := add_pos zero_lt_one_ax zero_lt_one_ax
    rw [e] at hpos
    exact lt_irrefl_ax 0 hpos
  cases s <;> cases t
  · rfl
  · exact absurd (h : (1 : Real) = -1) (fun hh => contra hh)
  · exact absurd ((h : (-1 : Real) = 1).symm) (fun hh => contra hh)
  · rfl

theorem val_flip (s : Sign) : s.flip.val = -(s.val) := by
  cases s
  · rfl
  · show (1 : Real) = -(-1)
    have e : -(-(1 : Real)) = 1 := by mach_ring
    rw [e]

end Sign

/-- A tangency mode: one sign per input circle. Eight inhabitants. -/
structure Mode where
  sA : Sign
  sB : Sign
  sC : Sign
  deriving DecidableEq, Repr

namespace Mode

/-- The antipode: reverse all three tangency signs. -/
def anti (m : Mode) : Mode := ⟨m.sA.flip, m.sB.flip, m.sC.flip⟩

/-- **The antipode is an involution.** -/
@[simp] theorem anti_anti (m : Mode) : m.anti.anti = m := by
  cases m with
  | mk a b c => cases a <;> cases b <;> cases c <;> rfl

theorem anti_ne (m : Mode) : m.anti ≠ m := by
  cases m with
  | mk a b c => cases a <;> cases b <;> cases c <;> intro h <;> exact Sign.noConfusion (Mode.mk.inj h).1

end Mode

/-- **The tangency equation at a SIGNED radius.**

`r` ranges over all of `Real`, negative and zero included. This is the algebraic enumeration
object; `Geometry.TangentExt` / `TangentInt` remain the geometric predicates over a genuine
`Circle`, whose radius is strictly positive. Keeping the two apart is what lets a degenerate zero
root be produced and then rejected, rather than being unrepresentable. -/
noncomputable def tangentEq (a₁ a₂ ρ : Real) (s : Sign) (x y r : Real) : Prop :=
  (x - a₁) * (x - a₁) + (y - a₂) * (y - a₂) = (r + s.val * ρ) * (r + s.val * ρ)

/-- **The antipodal law, one equation.** Negating the radius and the sign together is the identity
on the tangency equation. This is the whole content; everything below is bookkeeping over it. -/
theorem tangentEq_antipodal (a₁ a₂ ρ : Real) (s : Sign) (x y r : Real) :
    tangentEq a₁ a₂ ρ s x y r ↔ tangentEq a₁ a₂ ρ s.flip x y (-r) := by
  unfold tangentEq
  rw [Sign.val_flip]
  have e : (-r + -(s.val) * ρ) * (-r + -(s.val) * ρ) = (r + s.val * ρ) * (r + s.val * ρ) := by
    mach_mpoly [r, s.val, ρ]
  rw [e]

/-- **The tangency equation with the sign squared out.** The right-hand side of `tangentEq` hides a
`σ²ρ²`; once `σ² = 1` is applied the equation is a genuine polynomial in `σ` of degree one, which is
the form every elimination step wants. -/
theorem tangentEq_expanded (a₁ a₂ ρ : Real) (s : Sign) (x y r : Real) :
    tangentEq a₁ a₂ ρ s x y r
      ↔ (x - a₁) * (x - a₁) + (y - a₂) * (y - a₂)
          = r * r + (1 + 1) * (s.val * ρ) * r + ρ * ρ := by
  unfold tangentEq
  have e : (r + s.val * ρ) * (r + s.val * ρ)
      = r * r + (1 + 1) * (s.val * ρ) * r + (s.val * s.val) * (ρ * ρ) := by
    mach_mpoly [r, s.val, ρ]
  rw [e, Sign.val_sq]
  have e2 : r * r + (1 + 1) * (s.val * ρ) * r + 1 * (ρ * ρ)
      = r * r + (1 + 1) * (s.val * ρ) * r + ρ * ρ := by mach_mpoly [r, s.val, ρ]
  rw [e2]

/-- The three-equation system for one mode, at a signed radius. -/
def SolvesMode (A B C : Circle) (m : Mode) (x y r : Real) : Prop :=
  tangentEq A.x A.y A.r m.sA x y r
  ∧ tangentEq B.x B.y B.r m.sB x y r
  ∧ tangentEq C.x C.y C.r m.sC x y r

/-- **The antipodal law, lifted to the system.** -/
theorem solvesMode_antipodal (A B C : Circle) (m : Mode) (x y r : Real) :
    SolvesMode A B C m x y r ↔ SolvesMode A B C m.anti x y (-r) :=
  and_congr (tangentEq_antipodal _ _ _ _ _ _ _)
    (and_congr (tangentEq_antipodal _ _ _ _ _ _ _) (tangentEq_antipodal _ _ _ _ _ _ _))


/-- **A solution with nonzero radius determines its mode.**

If one `(x, y, r)` solves two modes then the modes agree, provided `r ≠ 0`. Subtracting the two
tangency equations for the same input circle leaves `2rρ(σ − σ')= 0`, and both `r` and `ρ` are
nonzero, so the signs coincide.

This is the last ingredient of distinctness, and it is what makes the eight solutions eight *distinct
circles* rather than eight labelled ones: a circle cannot be tangent to the same input both
externally and internally unless it has zero radius. Note where the hypothesis `r ≠ 0` bites — it is
the same degenerate candidate the algebraic layer deliberately keeps representable. -/
theorem mode_unique (A B C : Circle) (m m' : Mode) (x y r : Real) (hr : r ≠ 0)
    (h : SolvesMode A B C m x y r) (h' : SolvesMode A B C m' x y r) : m = m' := by
  have key : ∀ (P : Circle) (s t : Sign),
      tangentEq P.x P.y P.r s x y r → tangentEq P.x P.y P.r t x y r → s = t := by
    intro P s t hs ht
    rw [tangentEq_expanded] at hs ht
    refine Sign.val_inj ?_
    -- `2rρ(σ − σ') = 0`, with `r ≠ 0` and `ρ > 0`
    have hd : (1 + 1) * ((r * P.r) * (s.val - t.val)) = 0 := by
      have e : (1 + 1) * ((r * P.r) * (s.val - t.val))
          = (r * r + (1 + 1) * (s.val * P.r) * r + P.r * P.r)
            - (r * r + (1 + 1) * (t.val * P.r) * r + P.r * P.r) := by
        mach_mpoly [r, P.r, s.val, t.val] <;> mach_ring
      rw [e, ← hs, ← ht]
      mach_mpoly [x, y, P.x, P.y] <;> mach_ring
    have h2 : (0 : Real) < 1 + 1 := add_pos zero_lt_one_ax zero_lt_one_ax
    have hrP : r * P.r ≠ 0 := by
      intro hz
      exact hr (QuadraticRoots.right_of_mul_eq_zero (ne_of_gt P.hr)
        (by rw [← hz]; mach_ring : P.r * r = 0))
    have := QuadraticRoots.right_of_mul_eq_zero (ne_of_gt h2) hd
    exact QuadraticRoots.eq_of_sub_eq_zero (QuadraticRoots.right_of_mul_eq_zero hrP this)
  obtain ⟨hA, hB, hC⟩ := h
  obtain ⟨hA', hB', hC'⟩ := h'
  cases m with
  | mk a b c => cases m' with
    | mk a' b' c' =>
      have ea := key A a a' hA hA'
      have eb := key B b b' hB hB'
      have ec := key C c c' hC hC'
      rw [ea, eb, ec]

/-! ## The four classes, derived rather than declared -/

/-- A mode is **canonical** when its first sign is external. Exactly one of each antipodal pair is:
the antipode flips all three signs, so it flips this one. Any single coordinate would do — the
choice of `sA` is arbitrary and carries no content. -/
def Mode.IsCanonical (m : Mode) : Prop := m.sA = Sign.outer

instance (m : Mode) : Decidable m.IsCanonical := by
  unfold Mode.IsCanonical; infer_instance

/-- **Exactly one of `m`, `m.anti` is canonical.** This is what makes "four classes" well defined:
the eight modes are partitioned into four antipodal pairs, each with a unique representative. -/
theorem canonical_xor_anti (m : Mode) :
    (m.IsCanonical ∧ ¬ m.anti.IsCanonical) ∨ (¬ m.IsCanonical ∧ m.anti.IsCanonical) := by
  cases m with
  | mk a b c => cases a <;> cases b <;> cases c <;> decide

/-- The four canonical representatives, listed. -/
def canonicalModes : List Mode :=
  [⟨Sign.outer, Sign.outer, Sign.outer⟩,
   ⟨Sign.outer, Sign.outer, Sign.inner⟩,
   ⟨Sign.outer, Sign.inner, Sign.outer⟩,
   ⟨Sign.outer, Sign.inner, Sign.inner⟩]

theorem canonicalModes_length : canonicalModes.length = 4 := rfl

theorem canonicalModes_nodup : canonicalModes.Nodup := by decide

/-- **The list is exactly the canonical modes** — no representative missing, none spurious. -/
theorem mem_canonicalModes_iff (m : Mode) : m ∈ canonicalModes ↔ m.IsCanonical := by
  cases m with
  | mk a b c => cases a <;> cases b <;> cases c <;> decide

/-- **The milestone: enumerating four classes over a signed radius is equivalent to enumerating
all eight modes.**

Left to right is the reduction the solver relies on — whatever mode a solution belongs to, it is
recovered from a canonical class at a signed radius. Right to left is what stops the reduction from
losing solutions. Both directions are the antipodal law and nothing else. -/
theorem eightModes_reduce_to_four (A B C : Circle) (m : Mode) (x y r : Real) :
    SolvesMode A B C m x y r ↔
      ∃ m₀ : Mode, ∃ r₀ : Real,
        m₀.IsCanonical ∧ SolvesMode A B C m₀ x y r₀ ∧
        ((m₀ = m ∧ r₀ = r) ∨ (m₀ = m.anti ∧ r₀ = -r)) := by
  constructor
  · intro h
    rcases canonical_xor_anti m with ⟨hc, _⟩ | ⟨_, hc⟩
    · exact ⟨m, r, hc, h, Or.inl ⟨rfl, rfl⟩⟩
    · exact ⟨m.anti, -r, hc, (solvesMode_antipodal A B C m x y r).mp h, Or.inr ⟨rfl, rfl⟩⟩
  · rintro ⟨m₀, r₀, _, hsol, (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)⟩
    · exact hsol
    · exact (solvesMode_antipodal A B C m x y r).mpr hsol

/-- **The decode step, with the zero root visible.**

A canonical class hands back a signed `r`. Given `r ≠ 0` it decodes to a genuine mode and a
*positive* radius — the class's own mode when `r > 0`, its antipode when `r < 0`. The hypothesis
`r ≠ 0` is exactly the obligation the certification layer must discharge before a `Circle` (whose
radius is strictly positive) can be built; a zero root is a representable candidate that fails
here, not a case the algebra was prevented from producing. -/
theorem decode_of_canonical (A B C : Circle) (m₀ : Mode) (x y r : Real) (hr : r ≠ 0)
    (h : SolvesMode A B C m₀ x y r) :
    (0 < r ∧ SolvesMode A B C m₀ x y r)
    ∨ (0 < -r ∧ SolvesMode A B C m₀.anti x y (-r)) := by
  rcases lt_total 0 r with hpos | hzero | hneg
  · exact Or.inl ⟨hpos, h⟩
  · exact absurd hzero.symm hr
  · refine Or.inr ⟨?_, (solvesMode_antipodal A B C m₀ x y r).mp h⟩
    have v := add_lt_add_left hneg (-r)
    have l : -r + r = 0 := by mach_ring
    have rr : -r + (0 : Real) = -r := by mach_ring
    rw [l, rr] at v; exact v

end Apollonius
end Geometry
end MachLib
