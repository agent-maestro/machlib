import MachLib.PfaffianGeneralBase
import MachLib.ChainExp2CTDCongr

/-!
# Generalize — the cTD eval-congruence for y1-free polynomials (general chains)

The canonical single-exp descent's phantom-peeling recursion needs `cTD c' a ~ cTD c' b` for eval-equal
y1-free `a, b` (Seam A). The ∀N `eval_cTD_congr_y1free` is IterExp-specific; here the only chain-dependent
piece is the cTD DECOMPOSITION (`cTD c' r = partialX r + relations 0 · partialY0 r`, coefficient generalized
from `env(⟨0⟩) = eval(y0)` to `eval(c'.relations ⟨0⟩)`). The partial-derivative machinery (hasDerivAt_eval
_partialX/Y0) is chain-agnostic and reused, so `eval_cTD_zero_of_y1free_gen` and the congruence follow.
-/
namespace MachLib.PfaffianGeneralReduce
open MachLib.Real MachLib.MultiPolyMod MachLib.PfaffianChainMod
open MachLib.PfaffianChainMod.PfaffianFn MachLib.IterExpDepthN MachLib.ChainExp2CTDCongr MachLib.IterExpTopIdentity

set_option maxHeartbeats 2000000 in
/-- **General cTD decomposition (y1-free).** `eval(cTD c' r) = eval(partialX r) + eval(relations 0)·eval
(partialY0 r)` — generalizes cTD_decomp_y1free (coefficient env(⟨0⟩)=eval(y0) → eval(c'.relations ⟨0⟩)). -/
theorem cTD_decomp_y1free_gen (c' : PfaffianChain 2) (r : MultiPoly 2) (x : Real) (env : Fin 2 → Real) :
    MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) r = 0 →
    MultiPoly.eval (chainTotalDeriv c' r) x env
    = MultiPoly.eval (partialX r) x env
      + MultiPoly.eval (c'.relations (⟨0, by omega⟩ : Fin 2)) x env * MultiPoly.eval (partialY0 r) x env := by
  induction r with
  | const c => intro _; show (0 : Real) = 0 + _ * 0; mach_ring
  | varX => intro _; show (1 : Real) = 1 + _ * 0; mach_ring
  | varY j =>
    intro hy1
    by_cases hj : j = (⟨0, by omega⟩ : Fin 2)
    · rw [hj]
      show MultiPoly.eval (c'.relations (⟨0, by omega⟩ : Fin 2)) x env
         = MultiPoly.eval (MultiPoly.const 0) x env
           + MultiPoly.eval (c'.relations (⟨0, by omega⟩ : Fin 2)) x env
             * MultiPoly.eval (if (⟨0, by omega⟩ : Fin 2) = (⟨0, by omega⟩ : Fin 2) then MultiPoly.const 1 else MultiPoly.const 0) x env
      rw [if_pos rfl, MultiPoly.eval_const, MultiPoly.eval_const]; mach_ring
    · exfalso
      by_cases hj1 : j = (⟨1, by omega⟩ : Fin 2)
      · rw [hj1] at hy1; exact Nat.one_ne_zero hy1
      · have h0 : j.val ≠ 0 := fun h => hj (Fin.ext h)
        have h1 : j.val ≠ 1 := fun h => hj1 (Fin.ext h)
        have := j.isLt; omega
  | add p q ihp ihq =>
    intro hy1
    have hp1 : MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) p = 0 := by
      have hle : MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) p ≤ MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) (MultiPoly.add p q) := Nat.le_max_left _ _; omega
    have hq1 : MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) q = 0 := by
      have hle : MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) q ≤ MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) (MultiPoly.add p q) := Nat.le_max_right _ _; omega
    show MultiPoly.eval (MultiPoly.add (chainTotalDeriv c' p) (chainTotalDeriv c' q)) x env = _
    rw [MultiPoly.eval_add, ihp hp1, ihq hq1,
        show partialX (MultiPoly.add p q) = MultiPoly.add (partialX p) (partialX q) from rfl,
        show partialY0 (MultiPoly.add p q) = MultiPoly.add (partialY0 p) (partialY0 q) from rfl,
        MultiPoly.eval_add, MultiPoly.eval_add]
    generalize MultiPoly.eval (partialX p) x env = Xp
    generalize MultiPoly.eval (partialX q) x env = Xq
    generalize MultiPoly.eval (partialY0 p) x env = Yp
    generalize MultiPoly.eval (partialY0 q) x env = Yq
    generalize MultiPoly.eval (c'.relations (⟨0, by omega⟩ : Fin 2)) x env = E
    mach_ring
  | sub p q ihp ihq =>
    intro hy1
    have hp1 : MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) p = 0 := by
      have hle : MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) p ≤ MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) (MultiPoly.sub p q) := Nat.le_max_left _ _; omega
    have hq1 : MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) q = 0 := by
      have hle : MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) q ≤ MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) (MultiPoly.sub p q) := Nat.le_max_right _ _; omega
    show MultiPoly.eval (MultiPoly.sub (chainTotalDeriv c' p) (chainTotalDeriv c' q)) x env = _
    rw [MultiPoly.eval_sub, ihp hp1, ihq hq1,
        show partialX (MultiPoly.sub p q) = MultiPoly.sub (partialX p) (partialX q) from rfl,
        show partialY0 (MultiPoly.sub p q) = MultiPoly.sub (partialY0 p) (partialY0 q) from rfl,
        MultiPoly.eval_sub, MultiPoly.eval_sub]
    generalize MultiPoly.eval (partialX p) x env = Xp
    generalize MultiPoly.eval (partialX q) x env = Xq
    generalize MultiPoly.eval (partialY0 p) x env = Yp
    generalize MultiPoly.eval (partialY0 q) x env = Yq
    generalize MultiPoly.eval (c'.relations (⟨0, by omega⟩ : Fin 2)) x env = E
    mach_ring
  | mul p q ihp ihq =>
    intro hy1
    have hp1 : MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) p = 0 := by
      have h2 : MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) (MultiPoly.mul p q) = 0 := hy1
      rw [degreeY_mul' (⟨1, by omega⟩ : Fin 2) p q] at h2; omega
    have hq1 : MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) q = 0 := by
      have h2 : MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) (MultiPoly.mul p q) = 0 := hy1
      rw [degreeY_mul' (⟨1, by omega⟩ : Fin 2) p q] at h2; omega
    show MultiPoly.eval (MultiPoly.add (MultiPoly.mul (chainTotalDeriv c' p) q) (MultiPoly.mul p (chainTotalDeriv c' q))) x env = _
    rw [MultiPoly.eval_add, MultiPoly.eval_mul, MultiPoly.eval_mul, ihp hp1, ihq hq1,
        show partialX (MultiPoly.mul p q) = MultiPoly.add (MultiPoly.mul (partialX p) q) (MultiPoly.mul p (partialX q)) from rfl,
        show partialY0 (MultiPoly.mul p q) = MultiPoly.add (MultiPoly.mul (partialY0 p) q) (MultiPoly.mul p (partialY0 q)) from rfl,
        MultiPoly.eval_add, MultiPoly.eval_mul, MultiPoly.eval_mul, MultiPoly.eval_add, MultiPoly.eval_mul, MultiPoly.eval_mul]
    generalize MultiPoly.eval (partialX p) x env = Xp
    generalize MultiPoly.eval (partialX q) x env = Xq
    generalize MultiPoly.eval (partialY0 p) x env = Yp
    generalize MultiPoly.eval (partialY0 q) x env = Yq
    generalize MultiPoly.eval p x env = P
    generalize MultiPoly.eval q x env = Q
    generalize MultiPoly.eval (c'.relations (⟨0, by omega⟩ : Fin 2)) x env = E
    mach_ring

/-- cTD kills eval-zero (general, y1-free). -/
theorem eval_cTD_zero_of_y1free_gen (c' : PfaffianChain 2) (r : MultiPoly 2)
    (hy1 : MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) r = 0)
    (hz : ∀ (x : Real) (env : Fin 2 → Real), MultiPoly.eval r x env = 0) :
    ∀ (x : Real) (env : Fin 2 → Real), MultiPoly.eval (chainTotalDeriv c' r) x env = 0 := by
  intro x env
  rw [cTD_decomp_y1free_gen c' r x env hy1]
  have hx : MultiPoly.eval (partialX r) x env = 0 := by
    have hd := hasDerivAt_eval_partialX r x env
    have hf : (fun t => MultiPoly.eval r t env) = fun _ => (0 : Real) := funext (fun t => hz t env)
    rw [hf] at hd
    exact MachLib.Real.HasDerivAt_unique (fun _ => (0 : Real)) (MultiPoly.eval (partialX r) x env) 0 x hd (MachLib.Real.HasDerivAt_const 0 x)
  have hy : MultiPoly.eval (partialY0 r) x env = 0 := by
    have hd := hasDerivAt_eval_partialY0 r x env
    have hf : (fun v => MultiPoly.eval r x (fun j => if j = (⟨0, by omega⟩ : Fin 2) then v else env j)) = fun _ => (0 : Real) := funext (fun v => hz x _)
    rw [hf] at hd
    exact MachLib.Real.HasDerivAt_unique (fun _ => (0 : Real)) (MultiPoly.eval (partialY0 r) x env) 0 (env (⟨0, by omega⟩ : Fin 2)) hd (MachLib.Real.HasDerivAt_const 0 _)
  rw [hx, hy]; mach_ring

/-- **General cTD eval-congruence (y1-free).** -/
theorem eval_cTD_congr_y1free_gen (c' : PfaffianChain 2) (a b : MultiPoly 2)
    (hya : MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) a = 0)
    (hyb : MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) b = 0)
    (heq : ∀ (x : Real) (env : Fin 2 → Real), MultiPoly.eval a x env = MultiPoly.eval b x env) :
    ∀ (x : Real) (env : Fin 2 → Real),
      MultiPoly.eval (chainTotalDeriv c' a) x env = MultiPoly.eval (chainTotalDeriv c' b) x env := by
  have hsub1 : MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) (MultiPoly.sub a b) = 0 := by
    show Nat.max _ _ = 0; rw [hya, hyb]; exact Nat.max_self 0
  have hz : ∀ (x : Real) (env : Fin 2 → Real), MultiPoly.eval (MultiPoly.sub a b) x env = 0 := by
    intro x env; rw [MultiPoly.eval_sub, heq x env]; mach_ring
  intro x env
  have h0 := eval_cTD_zero_of_y1free_gen c' (MultiPoly.sub a b) hsub1 hz x env
  rw [show chainTotalDeriv c' (MultiPoly.sub a b) = MultiPoly.sub (chainTotalDeriv c' a) (chainTotalDeriv c' b) from rfl, MultiPoly.eval_sub] at h0
  calc MultiPoly.eval (chainTotalDeriv c' a) x env
      = (MultiPoly.eval (chainTotalDeriv c' a) x env - MultiPoly.eval (chainTotalDeriv c' b) x env) + MultiPoly.eval (chainTotalDeriv c' b) x env := by mach_ring
    _ = 0 + MultiPoly.eval (chainTotalDeriv c' b) x env := by rw [h0]
    _ = MultiPoly.eval (chainTotalDeriv c' b) x env := by mach_ring

end MachLib.PfaffianGeneralReduce
