import MachLib.MultiPolyCanonYN

/-!
# Individual-entry coefficient extraction (L1) — for the log Khovanskii step

`log_hard`'s leading-coefficient identity needs the coefficient at a SPECIFIC
degree of `chainTotalDeriv c p` (`yCoeffsAt top · .getD d`), not the whole-poly
reconstruction the existing `eval_yCoeffsAt_*` lemmas give. This file builds the
missing individual-entry (`getD d`) machinery: `getD d` commutes with the
coefficient-list operations (`listAddN` here; `listSubN`, `listMulN`-convolution
to follow) at the eval level. See the exploration FINDINGS "L1/L2" decomposition.
-/
namespace MachLib
namespace MultiPolyMod
namespace MultiPoly
open MachLib.Real

/-- **L1 brick 1.** `getD d` commutes with `listAddN` at the eval level:
`(listAddN l1 l2).getD d` evaluates to `l1.getD d + l2.getD d` (with `const 0`
default, `eval (const 0) = 0`). The `add`-case ingredient of the `idN`-log
individual-entry induction. -/
theorem getD_listAddN_eval {n : Nat} :
    ∀ (l1 l2 : List (MultiPoly n)) (d : Nat) (x : Real) (env : Fin n → Real),
    MultiPoly.eval ((listAddN l1 l2).getD d (MultiPoly.const 0)) x env
      = MultiPoly.eval (l1.getD d (MultiPoly.const 0)) x env
        + MultiPoly.eval (l2.getD d (MultiPoly.const 0)) x env
  | [], l2, d, x, env => by
    have hla : listAddN ([] : List (MultiPoly n)) l2 = l2 := rfl
    have hnil : (([] : List (MultiPoly n)).getD d (MultiPoly.const 0)) = (MultiPoly.const 0 : MultiPoly n) := by
      cases d <;> rfl
    rw [hla, hnil]
    show MultiPoly.eval (l2.getD d (MultiPoly.const 0)) x env
        = MultiPoly.eval (MultiPoly.const 0 : MultiPoly n) x env
          + MultiPoly.eval (l2.getD d (MultiPoly.const 0)) x env
    show _ = (0 : Real) + _
    mach_ring
  | p :: ps, [], d, x, env => by
    have hla : listAddN (p :: ps) ([] : List (MultiPoly n)) = p :: ps := rfl
    have hnil : (([] : List (MultiPoly n)).getD d (MultiPoly.const 0)) = (MultiPoly.const 0 : MultiPoly n) := by
      cases d <;> rfl
    rw [hla, hnil]
    show MultiPoly.eval ((p :: ps).getD d (MultiPoly.const 0)) x env
        = MultiPoly.eval ((p :: ps).getD d (MultiPoly.const 0)) x env
          + MultiPoly.eval (MultiPoly.const 0 : MultiPoly n) x env
    show _ = _ + (0 : Real)
    rw [add_zero]
  | p :: ps, q :: qs, 0, x, env => by
    show MultiPoly.eval (MultiPoly.add p q) x env
        = MultiPoly.eval p x env + MultiPoly.eval q x env
    rfl
  | p :: ps, q :: qs, d + 1, x, env => by
    show MultiPoly.eval ((listAddN ps qs).getD d (MultiPoly.const 0)) x env
        = MultiPoly.eval (ps.getD d (MultiPoly.const 0)) x env
          + MultiPoly.eval (qs.getD d (MultiPoly.const 0)) x env
    exact getD_listAddN_eval ps qs d x env

/-- **L1 brick 2.** `getD d` commutes with `listSubN` at the eval level. Six
cases (the `listSubN` nil rules split `[]`/`[]`, `[]`/`cons` (`0−q`), `cons`/`[]`,
`cons`/`cons`). The `sub`-case ingredient of the `idN`-log induction. -/
theorem getD_listSubN_eval {n : Nat} :
    ∀ (l1 l2 : List (MultiPoly n)) (d : Nat) (x : Real) (env : Fin n → Real),
    MultiPoly.eval ((listSubN l1 l2).getD d (MultiPoly.const 0)) x env
      = MultiPoly.eval (l1.getD d (MultiPoly.const 0)) x env
        - MultiPoly.eval (l2.getD d (MultiPoly.const 0)) x env
  | [], [], d, x, env => by
    have hnil : (([] : List (MultiPoly n)).getD d (MultiPoly.const 0)) = (MultiPoly.const 0 : MultiPoly n) := by
      cases d <;> rfl
    show MultiPoly.eval ((([] : List (MultiPoly n))).getD d (MultiPoly.const 0)) x env = _ - _
    rw [hnil]
    show (0 : Real) = (0 : Real) - (0 : Real)
    mach_ring
  | [], q :: qs, 0, x, env => by
    show MultiPoly.eval (MultiPoly.sub (MultiPoly.const 0) q) x env
        = MultiPoly.eval (MultiPoly.const 0 : MultiPoly n) x env - MultiPoly.eval q x env
    show (0 : Real) - MultiPoly.eval q x env = (0 : Real) - MultiPoly.eval q x env
    rfl
  | [], q :: qs, d + 1, x, env => by
    show MultiPoly.eval ((listSubN ([] : List (MultiPoly n)) qs).getD d (MultiPoly.const 0)) x env
        = MultiPoly.eval (([] : List (MultiPoly n)).getD d (MultiPoly.const 0)) x env
          - MultiPoly.eval (qs.getD d (MultiPoly.const 0)) x env
    exact getD_listSubN_eval [] qs d x env
  | p :: ps, [], d, x, env => by
    have hla : listSubN (p :: ps) ([] : List (MultiPoly n)) = p :: ps := rfl
    have hnil : (([] : List (MultiPoly n)).getD d (MultiPoly.const 0)) = (MultiPoly.const 0 : MultiPoly n) := by
      cases d <;> rfl
    rw [hla, hnil]
    show MultiPoly.eval ((p :: ps).getD d (MultiPoly.const 0)) x env
        = MultiPoly.eval ((p :: ps).getD d (MultiPoly.const 0)) x env - (0 : Real)
    mach_ring
  | p :: ps, q :: qs, 0, x, env => by
    show MultiPoly.eval (MultiPoly.sub p q) x env
        = MultiPoly.eval p x env - MultiPoly.eval q x env
    rfl
  | p :: ps, q :: qs, d + 1, x, env => by
    show MultiPoly.eval ((listSubN ps qs).getD d (MultiPoly.const 0)) x env
        = MultiPoly.eval (ps.getD d (MultiPoly.const 0)) x env
          - MultiPoly.eval (qs.getD d (MultiPoly.const 0)) x env
    exact getD_listSubN_eval ps qs d x env

end MultiPoly
end MultiPolyMod
end MachLib
