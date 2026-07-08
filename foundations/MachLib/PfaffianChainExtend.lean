import MachLib.PfaffianGeneralReduce
import MachLib.MultiPolyLiftLastY

/-!
# `chainExtend` — add one top variable to a Pfaffian chain

The descent has `chainRestrict` (drop the top variable) but no way to
*build* a chain up. The EMLTree→chain encoder needs the reverse: process an
EML expression innermost-first, adding each new (outer) sub-expression as a
fresh TOP chain variable. Because each addition is at the top, the encoder
is a *sequence of extends* — no chain-merging is ever needed.

`chainExtend c ne nr` appends a function `ne` with relation `nr : MultiPoly
(n+1)`, lifting every existing relation through `liftLastY` (they don't
depend on the new variable). Key facts:

- `chainExtend_chainRestrict` — `chainRestrict (chainExtend c ne nr) = c`
  (round-trip: the descent peels the extension straight back off).
- `chainExtend_isCoherentAt` — coherence is preserved given the new
  variable actually has the derivative its relation prescribes.

No new axioms; pure structural bookkeeping over `liftLastY`/`dropLastY`.
-/

namespace MachLib

open MachLib.Real MachLib.MultiPolyMod MachLib.MultiPolyMod.MultiPoly
  MachLib.PfaffianChainMod MachLib.PfaffianChainMod.PfaffianChain
  MachLib.PfaffianGeneralReduce

/-- Append a top variable `ne` (relation `nr`) to a length-`n` chain,
lifting the existing relations to be free of the new variable. -/
noncomputable def chainExtend {n : Nat} (c : PfaffianChain n)
    (ne : Real → Real) (nr : MultiPoly (n + 1)) : PfaffianChain (n + 1) where
  evals := fun i => if h : i.val < n then c.evals ⟨i.val, h⟩ else ne
  relations := fun i =>
    if h : i.val < n then MultiPoly.liftLastY (c.relations ⟨i.val, h⟩) else nr

@[simp] theorem chainExtend_evals_of_lt {n : Nat} (c : PfaffianChain n)
    (ne : Real → Real) (nr : MultiPoly (n + 1)) (i : Fin (n + 1)) (h : i.val < n) :
    (chainExtend c ne nr).evals i = c.evals ⟨i.val, h⟩ := dif_pos h

@[simp] theorem chainExtend_relations_of_lt {n : Nat} (c : PfaffianChain n)
    (ne : Real → Real) (nr : MultiPoly (n + 1)) (i : Fin (n + 1)) (h : i.val < n) :
    (chainExtend c ne nr).relations i = MultiPoly.liftLastY (c.relations ⟨i.val, h⟩) :=
  dif_pos h

theorem chainExtend_evals_last {n : Nat} (c : PfaffianChain n)
    (ne : Real → Real) (nr : MultiPoly (n + 1)) :
    (chainExtend c ne nr).evals ⟨n, Nat.lt_succ_self n⟩ = ne :=
  dif_neg (Nat.lt_irrefl n)

theorem chainExtend_relations_last {n : Nat} (c : PfaffianChain n)
    (ne : Real → Real) (nr : MultiPoly (n + 1)) :
    (chainExtend c ne nr).relations ⟨n, Nat.lt_succ_self n⟩ = nr :=
  dif_neg (Nat.lt_irrefl n)

/-- **Round-trip:** restricting an extension returns the original chain. -/
theorem chainExtend_chainRestrict {n : Nat} (c : PfaffianChain n)
    (ne : Real → Real) (nr : MultiPoly (n + 1)) :
    chainRestrict (chainExtend c ne nr) = c := by
  obtain ⟨ce, cr⟩ := c
  show (⟨fun i => (chainExtend ⟨ce, cr⟩ ne nr).evals ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩,
        fun i => MultiPoly.dropLastY
          ((chainExtend ⟨ce, cr⟩ ne nr).relations ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩)⟩
      : PfaffianChain n) = ⟨ce, cr⟩
  congr 1
  · funext i
    rw [chainExtend_evals_of_lt ⟨ce, cr⟩ ne nr ⟨i.val, _⟩ i.isLt]
  · funext i
    rw [chainExtend_relations_of_lt ⟨ce, cr⟩ ne nr ⟨i.val, _⟩ i.isLt,
        MultiPoly.dropLastY_liftLastY]

/-- The extended chain's values at the first `n` indices agree with `c`'s. -/
theorem chainExtend_chainValues_of_lt {n : Nat} (c : PfaffianChain n)
    (ne : Real → Real) (nr : MultiPoly (n + 1)) (x : Real) (i : Fin (n + 1)) (h : i.val < n) :
    (chainExtend c ne nr).chainValues x i = c.chainValues x ⟨i.val, h⟩ := by
  show (chainExtend c ne nr).evals i x = c.evals ⟨i.val, h⟩ x
  rw [chainExtend_evals_of_lt c ne nr i h]

/-- A lifted relation evaluated along the extension equals the original
relation evaluated along `c` (the new top value is irrelevant). -/
theorem eval_liftLastY_chainExtend {n : Nat} (c : PfaffianChain n)
    (ne : Real → Real) (nr : MultiPoly (n + 1)) (r : MultiPoly n) (x : Real) :
    MultiPoly.eval (MultiPoly.liftLastY r) x ((chainExtend c ne nr).chainValues x)
      = MultiPoly.eval r x (c.chainValues x) := by
  rw [MultiPoly.eval_liftLastY]
  congr 1
  funext i
  exact chainExtend_chainValues_of_lt c ne nr x ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ i.isLt

/-- **Coherence is preserved** by `chainExtend`, provided the new variable
`ne` genuinely has the derivative its relation `nr` prescribes at `x`. -/
theorem chainExtend_isCoherentAt {n : Nat} (c : PfaffianChain n)
    (ne : Real → Real) (nr : MultiPoly (n + 1)) (x : Real)
    (hc : c.IsCoherentAt x)
    (hne : HasDerivAt ne
        (MultiPoly.eval nr x ((chainExtend c ne nr).chainValues x)) x) :
    (chainExtend c ne nr).IsCoherentAt x := by
  intro i
  by_cases h : i.val < n
  · -- old variable: derivative value matches through `liftLastY`
    have hbase := hc ⟨i.val, h⟩
    rw [chainExtend_evals_of_lt c ne nr i h,
        chainExtend_relations_of_lt c ne nr i h,
        eval_liftLastY_chainExtend c ne nr (c.relations ⟨i.val, h⟩) x]
    exact hbase
  · -- new top variable: `i = ⟨n, _⟩`
    have hi : i = ⟨n, Nat.lt_succ_self n⟩ := by
      apply Fin.ext
      show i.val = n
      have hlt := i.isLt
      omega
    rw [hi, chainExtend_evals_last c ne nr, chainExtend_relations_last c ne nr]
    exact hne

/-- **Coherence on an interval** transfers, given the new variable has the
prescribed derivative throughout `(a,b)`. -/
theorem chainExtend_isCoherentOn {n : Nat} (c : PfaffianChain n)
    (ne : Real → Real) (nr : MultiPoly (n + 1)) (a b : Real)
    (hc : c.IsCoherentOn a b)
    (hne : ∀ x, a < x → x < b →
        HasDerivAt ne (MultiPoly.eval nr x ((chainExtend c ne nr).chainValues x)) x) :
    (chainExtend c ne nr).IsCoherentOn a b :=
  fun x hxa hxb => chainExtend_isCoherentAt c ne nr x (hc x hxa hxb) (hne x hxa hxb)

/-- **Positivity of all chain values** transfers on `(a,b)`, given the new
variable is positive there. This is the descent's `hpos` hypothesis. -/
theorem chainExtend_positivity {n : Nat} (c : PfaffianChain n)
    (ne : Real → Real) (nr : MultiPoly (n + 1)) (a b : Real)
    (hpos : ∀ z, a < z → z < b → ∀ i : Fin n, 0 < c.evals i z)
    (hnepos : ∀ z, a < z → z < b → 0 < ne z) :
    ∀ z, a < z → z < b → ∀ i : Fin (n + 1), 0 < (chainExtend c ne nr).evals i z := by
  intro z hza hzb i
  by_cases h : i.val < n
  · rw [chainExtend_evals_of_lt c ne nr i h]; exact hpos z hza hzb ⟨i.val, h⟩
  · have hi : i = ⟨n, Nat.lt_succ_self n⟩ := by
      apply Fin.ext; show i.val = n; have := i.isLt; omega
    rw [hi, chainExtend_evals_last c ne nr]; exact hnepos z hza hzb

end MachLib
