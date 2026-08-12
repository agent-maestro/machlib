import MachLib.EMLSizeNineShape

/-!
# Constant generation is vacuous in EML — and not in the unit-generated fragment

A research direction was proposed on the grammar `S → 1 | eml(S,S)`: *which irrational constants are
EML-representable, and how compactly?* Against **MachLib's actual grammar** that question has no
content, and the reason is one line of the definition:

```
inductive EMLTree | const : Real → EMLTree | var | eml : EMLTree → EMLTree → EMLTree
```

`const` takes an **arbitrary real**. So `π` is `EMLTree.const π` — depth `0`, size `1`
(`const_mem_eml_depth_zero`), and likewise for `e`, `Ω`, or any other constant one might ask about.
There is no representability question and no compactness question. `i` is not even in scope: `eval`
is `Real`-valued.

`const_generation_is_vacuous` states this as a theorem rather than a remark, because the direction
was proposed twice and the refutation is cheap enough that it should be checkable, not argued.

## Where the question does have content

Restrict the constants to `0` and `1` — `EMLTree.unitOnly` — and constant generation becomes real
arithmetic again. Two immediate facts:

* **`e` at depth 1, size 3** (`e_mem_unitOnly`): `eml (const 1) (const 1)` is
  `exp 1 − log 1 = e − 0`.
* **`e − 1` at depth 2, size 5** (`e_sub_one_mem_unitOnly`): `eml (const 1) (eml (const 1) (const 1))`
  is `exp 1 − log (exp 1) = e − 1`.

Both lean on the totalised `log`: `log 0 = 0` and `log 1 = 0` are what make the depth-1 leaves usable
rather than undefined. Whether every algebraic combination of iterated exponentials is reachable, and
at what depth, is open and is a *different language* from the one the rest of this corpus studies —
it should not be confused with it.
-/

namespace MachLib

open Real

/-- **Every real constant sits at depth 0 and size 1.** -/
theorem const_mem_eml_depth_zero (c : Real) :
    ∃ t : EMLTree, t.depth = 0 ∧ t.size = 1 ∧ ∀ x : Real, 0 < x → t.eval x = c :=
  ⟨EMLTree.const c, rfl, rfl, fun _ _ => rfl⟩

/-- **So "which constants are representable, and how compactly?" is vacuous for EML.** Every real is
representable, all at the same minimal cost, so the question orders nothing. -/
theorem const_generation_is_vacuous :
    ∀ c : Real, ∃ t : EMLTree, t.depth = 0 ∧ t.size = 1 ∧ ∀ x : Real, 0 < x → t.eval x = c :=
  const_mem_eml_depth_zero

/-- The **unit-generated** fragment: every `const` leaf is `0` or `1`. This is the language in which
constant generation is a question. -/
def EMLTree.unitOnly : EMLTree → Prop
  | EMLTree.const c => c = 0 ∨ c = 1
  | EMLTree.var => True
  | EMLTree.eml a b => a.unitOnly ∧ b.unitOnly

/-- `log 1 = 0`, used by both witnesses below. -/
private theorem log_one_eq_zero : log (1 : Real) = 0 := by
  have hz : exp (0 : Real) = 1 := exp_zero
  rw [← hz, log_exp]

/-- **`e` is unit-generated at depth 1, size 3.** `exp 1 − log 1 = e − 0`. -/
theorem e_mem_unitOnly :
    ∃ t : EMLTree, t.unitOnly ∧ t.depth = 1 ∧ t.size = 3
      ∧ ∀ x : Real, 0 < x → t.eval x = exp 1 := by
  refine ⟨EMLTree.eml (EMLTree.const 1) (EMLTree.const 1), ⟨Or.inr rfl, Or.inr rfl⟩, rfl, rfl,
    fun x _ => ?_⟩
  show exp 1 - log (1 : Real) = exp 1
  rw [log_one_eq_zero]
  mach_mpoly [exp 1]

/-- **`e − 1` is unit-generated at depth 2, size 5.** `exp 1 − log (exp 1) = e − 1`, so the second
level is spent turning `e` into the `1` that gets subtracted. -/
theorem e_sub_one_mem_unitOnly :
    ∃ t : EMLTree, t.unitOnly ∧ t.depth = 2 ∧ t.size = 5
      ∧ ∀ x : Real, 0 < x → t.eval x = exp 1 - 1 := by
  refine ⟨EMLTree.eml (EMLTree.const 1)
            (EMLTree.eml (EMLTree.const 1) (EMLTree.const 1)),
          ⟨Or.inr rfl, ⟨Or.inr rfl, Or.inr rfl⟩⟩, rfl, rfl, fun x _ => ?_⟩
  show exp 1 - log (exp 1 - log (1 : Real)) = exp 1 - 1
  rw [log_one_eq_zero]
  have e : exp 1 - (0 : Real) = exp 1 := by mach_mpoly [exp 1]
  rw [e, log_exp]

end MachLib
