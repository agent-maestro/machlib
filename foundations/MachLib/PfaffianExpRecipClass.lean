import MachLib.MultiPoly
import MachLib.PfaffianChain
import MachLib.PfaffianGeneralReduce

/-!
# The exp-or-reciprocal Pfaffian chain class — Brick A-1 (extended descent)

Retiring `PfaffianFunction.zero_count_bound_classical` from the *general*
`sin_not_in_eml_any_depth` requires bounding zeros of Pfaffian functions over
chains that are exp-type **except at reciprocal levels** — because a `log(v)` of
a composite argument forces a `1/v` generator whose relation `(1/v)' = −v'·(1/v)²`
is degree 2 in its own variable (see the exploration FINDINGS re-correction,
2026-07-07, and `Pfaffian.lean`'s `log_atom.derivative = inv var`).

This file opens the extended-class track (the user chose the full route,
"eyes open"): the class `IsExpOrRecipChain`, generalising
`MachLib.PfaffianGeneralReduce.IsExpChain` to admit degree-2 reciprocal levels
alongside the linear exp levels, and its two cheap structural facts — every
`IsExpChain` is one, and the class is closed under `chainRestrict` (so the
depth descent stays inside it). The hard content — a descent *step* that strips
a top reciprocal level (reusing `clearNum` / `reciprocalPfaffian_zero_count` as
the base-case tools) — is the subsequent brick.

## Level shapes
- **exp-type** `i`: `relations i = G · yᵢ`, `G` top-free (`degreeY i G = 0`).
  Value `eᵘ`, `(eᵘ)' = u'·eᵘ`; `G` carries `u'`.
- **reciprocal-type** `i`: `relations i = G · (yᵢ · yᵢ)`, `G` top-free.
  Value `1/v`, `(1/v)' = −v'·(1/v)²`; `G` carries `−v'`.
Both are triangular (`relations i` omits `yⱼ` for `j > i`).
-/

namespace MachLib
namespace PfaffianExpRecip

open MachLib.Real
open MachLib.MultiPolyMod
open MachLib.PfaffianChainMod
open MachLib.PfaffianGeneralReduce

/-- **The exp-or-reciprocal chain class.** At every level `i`, the relation is
either exp-type (`G·yᵢ`) or reciprocal-type (`G·yᵢ²`) with `G` top-free, and the
level is triangular. Strictly generalises `IsExpChain` (which forces the exp
disjunct everywhere). -/
def IsExpOrRecipChain {N : Nat} (c : PfaffianChain N) : Prop :=
  ∀ i : Fin N,
    ( (∃ G : MultiPoly N, MultiPoly.degreeY i G = 0
          ∧ c.relations i = MultiPoly.mul G (MultiPoly.varY i))
      ∨ (∃ G : MultiPoly N, MultiPoly.degreeY i G = 0
          ∧ c.relations i
              = MultiPoly.mul G (MultiPoly.mul (MultiPoly.varY i) (MultiPoly.varY i))) )
    ∧ (∀ j : Fin N, i.val < j.val → MultiPoly.degreeY j (c.relations i) = 0)

/-- Every exponential-type chain is exp-or-reciprocal (take the exp disjunct at
every level). So the extended descent subsumes the existing one. -/
theorem IsExpChain_imp_IsExpOrRecip {N : Nat} (c : PfaffianChain N)
    (h : IsExpChain c) : IsExpOrRecipChain c := by
  intro i
  obtain ⟨hrel, htri⟩ := h i
  exact ⟨Or.inl hrel, htri⟩

/-- **`chainRestrict` preserves `IsExpOrRecipChain`.** Dropping the top generator
keeps every lower level exp-type or reciprocal-type (`dropLastY` is a `mul`
homomorphism and sends `yⱼ ↦ yⱼ` for `j < N`), and preserves triangularity — so
the depth descent recurses within the extended class, exactly as it does for
`IsExpChain`. -/
theorem IsExpOrRecipChain_chainRestrict {N : Nat} (c : PfaffianChain (N + 1))
    (h : IsExpOrRecipChain c) : IsExpOrRecipChain (chainRestrict c) := by
  intro i
  have hdrop : MultiPoly.dropLastY
        (MultiPoly.varY (⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ : Fin (N + 1)))
      = MultiPoly.varY i := by
    show (if hlt : i.val < N then MultiPoly.varY ⟨i.val, hlt⟩ else MultiPoly.const 0)
        = MultiPoly.varY i
    rw [dif_pos i.isLt]
  refine ⟨?_, ?_⟩
  · rcases (h ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩).1 with hexp | hrecip
    · -- exp-type level survives (mirrors IsExpChain_chainRestrict)
      obtain ⟨G, hG, hrel⟩ := hexp
      refine Or.inl ⟨MultiPoly.dropLastY G, ?_, ?_⟩
      · have hle := MultiPoly.degreeY_dropLastY_le G i
        rw [hG] at hle
        exact Nat.le_zero.mp hle
      · show MultiPoly.dropLastY (c.relations ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩)
            = MultiPoly.mul (MultiPoly.dropLastY G) (MultiPoly.varY i)
        rw [hrel]
        show MultiPoly.mul (MultiPoly.dropLastY G)
              (MultiPoly.dropLastY (MultiPoly.varY ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩))
            = MultiPoly.mul (MultiPoly.dropLastY G) (MultiPoly.varY i)
        rw [hdrop]
    · -- reciprocal-type level survives (extra yᵢ·yᵢ factor)
      obtain ⟨G, hG, hrel⟩ := hrecip
      refine Or.inr ⟨MultiPoly.dropLastY G, ?_, ?_⟩
      · have hle := MultiPoly.degreeY_dropLastY_le G i
        rw [hG] at hle
        exact Nat.le_zero.mp hle
      · show MultiPoly.dropLastY (c.relations ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩)
            = MultiPoly.mul (MultiPoly.dropLastY G)
                (MultiPoly.mul (MultiPoly.varY i) (MultiPoly.varY i))
        rw [hrel]
        show MultiPoly.mul (MultiPoly.dropLastY G)
              (MultiPoly.mul
                (MultiPoly.dropLastY (MultiPoly.varY ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩))
                (MultiPoly.dropLastY (MultiPoly.varY ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩)))
            = MultiPoly.mul (MultiPoly.dropLastY G)
                (MultiPoly.mul (MultiPoly.varY i) (MultiPoly.varY i))
        rw [hdrop]
  · intro j hij
    show MultiPoly.degreeY j
        (MultiPoly.dropLastY (c.relations ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩)) = 0
    have hle := MultiPoly.degreeY_dropLastY_le
      (c.relations ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩) j
    rw [(h ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩).2
      ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩ hij] at hle
    exact Nat.le_zero.mp hle

end PfaffianExpRecip
end MachLib
