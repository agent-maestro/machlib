import MachLib.PfaffianGeneralWF

/-!
# General Rolle step (multiplier 0) — a piece of `log_hard`

`pfaffianChainFn_reduce_step_gen` (the Rolle step) is general — no `IsExpChain`.
With multiplier `m = 0` the integrating factor is the CONSTANT function
(antiderivative of `−0`), so no `vehExpo` is needed, and the step reduces the
zero-count of `f` to that of its total derivative `f'`. This is the reduction a
log-type top uses (`y' = w` top-free — no exp-style multiplier exists). The
remaining content of `log_hard` is the well-founded measure that
`chainTotalDeriv` descends (the leading-coefficient evolves by total derivative
over the lower chain — genuine classical Khovanskii content).
-/
namespace MachLib
namespace PfaffianGeneralReduce
open MachLib.Real MachLib.MultiPolyMod MachLib.PfaffianChainMod
open MachLib.PfaffianChainMod.PfaffianFn

/-- **General Rolle step (multiplier 0).** For ANY coherent chain, the zeros of
`pfaffianChainFn c p` are at most one more than the zeros of its total derivative
`pfaffianChainFn c (chainTotalDeriv c p)`. Instance of `pfaffianChainFn_reduce_step_gen`
with `m = 0`: the integrating factor is then the constant function (antiderivative
of `−0`), so NO `vehExpo` is needed. This is the Rolle reduction a log-type top
uses (`y' = w` top-free — no exp-style multiplier); the remaining content of
`log_hard` is the well-founded measure that `chainTotalDeriv` descends. -/
theorem chainTotalDeriv_rolle {n : Nat} (c : PfaffianChain n) (p : MultiPoly n)
    (a b : Real) (hab : a < b) (hcoh : c.IsCoherentOn a b) (N : Nat)
    (hN : ∀ zeros : List Real, zeros.Nodup →
        (∀ z ∈ zeros, a < z ∧ z < b ∧ (pfaffianChainFn c (chainTotalDeriv c p)).eval z = 0) →
        zeros.length ≤ N) :
    ∀ zeros : List Real, zeros.Nodup →
      (∀ z ∈ zeros, a < z ∧ z < b ∧ (pfaffianChainFn c p).eval z = 0) →
      zeros.length ≤ N + 1 := by
  have hEeq : ∀ z : Real, -(pfaffianChainFn c (MultiPoly.const 0)).eval z = 0 := by
    intro z; show -(MultiPoly.eval (MultiPoly.const 0) z (c.chainValues z)) = 0
    show -(0 : Real) = 0; rw [neg_zero]
  have hE : ∀ z, a < z → z < b →
      HasDerivAt (fun _ => (0 : Real)) (-(pfaffianChainFn c (MultiPoly.const 0)).eval z) z := by
    intro z _ _; rw [hEeq z]; exact HasDerivAt_const 0 z
  have hRedEq : ∀ z : Real,
      (pfaffianChainFn c (chainReduce c (MultiPoly.const 0) p)).eval z
        = (pfaffianChainFn c (chainTotalDeriv c p)).eval z := by
    intro z
    show MultiPoly.eval (chainReduce c (MultiPoly.const 0) p) z (c.chainValues z)
        = MultiPoly.eval (chainTotalDeriv c p) z (c.chainValues z)
    show MultiPoly.eval (MultiPoly.sub (chainTotalDeriv c p) (MultiPoly.mul (MultiPoly.const 0) p)) z
          (c.chainValues z)
        = MultiPoly.eval (chainTotalDeriv c p) z (c.chainValues z)
    show MultiPoly.eval (chainTotalDeriv c p) z (c.chainValues z)
          - (0 : Real) * MultiPoly.eval p z (c.chainValues z)
        = MultiPoly.eval (chainTotalDeriv c p) z (c.chainValues z)
    mach_ring
  refine pfaffianChainFn_reduce_step_gen c (MultiPoly.const 0) p a b hab (fun _ => 0) hcoh hE N ?_
  intro zeros hnd hz
  exact hN zeros hnd (fun z hzmem => by
    obtain ⟨ha, hb, h0⟩ := hz z hzmem
    exact ⟨ha, hb, by rw [← hRedEq z]; exact h0⟩)

/-! ## Log-top total-derivative degree bound (first `log_hard` cTD brick) -/

/-- **Log-top `cTD` degree bound.** For a LOG-type top (top-free relation,
`degreeY top (relations top) = 0`), the total derivative does NOT raise the
top-degree — it can only preserve or drop it (`varY top ↦ relations top` goes
`1 → 0`). Contrast the exp case (`degreeYtop_cTD_eq_gen`, which needs the
relation to have `degreeY top = 1` and gives equality). This is the degree half
of the Wronskian degree-drop the log descent (`log_hard`) rests on. Pure algebra
— no analytic axiom. -/
theorem degreeYtop_cTD_le_log {N : Nat} (c : PfaffianChain N) (top : Fin N)
    (h_top : MultiPoly.degreeY top (c.relations top) = 0)
    (h_tri : ∀ j : Fin N, j ≠ top → MultiPoly.degreeY top (c.relations j) = 0)
    (p : MultiPoly N) :
    MultiPoly.degreeY top (chainTotalDeriv c p) ≤ MultiPoly.degreeY top p := by
  induction p with
  | const cval => exact Nat.le_of_eq rfl
  | varX => exact Nat.le_of_eq rfl
  | varY j =>
    show MultiPoly.degreeY top (c.relations j) ≤ MultiPoly.degreeY top (MultiPoly.varY j)
    by_cases hj : j = top
    · rw [hj, h_top]; exact Nat.zero_le _
    · rw [h_tri j hj]; exact Nat.zero_le _
  | add p q ihp ihq =>
    show Nat.max (MultiPoly.degreeY top (chainTotalDeriv c p))
                 (MultiPoly.degreeY top (chainTotalDeriv c q))
       ≤ Nat.max (MultiPoly.degreeY top p) (MultiPoly.degreeY top q)
    exact Nat.max_le.mpr ⟨Nat.le_trans ihp (Nat.le_max_left _ _),
                          Nat.le_trans ihq (Nat.le_max_right _ _)⟩
  | sub p q ihp ihq =>
    show Nat.max (MultiPoly.degreeY top (chainTotalDeriv c p))
                 (MultiPoly.degreeY top (chainTotalDeriv c q))
       ≤ Nat.max (MultiPoly.degreeY top p) (MultiPoly.degreeY top q)
    exact Nat.max_le.mpr ⟨Nat.le_trans ihp (Nat.le_max_left _ _),
                          Nat.le_trans ihq (Nat.le_max_right _ _)⟩
  | mul p q ihp ihq =>
    show Nat.max (MultiPoly.degreeY top (chainTotalDeriv c p) + MultiPoly.degreeY top q)
                 (MultiPoly.degreeY top p + MultiPoly.degreeY top (chainTotalDeriv c q))
       ≤ MultiPoly.degreeY top p + MultiPoly.degreeY top q
    exact Nat.max_le.mpr ⟨Nat.add_le_add_right ihp _, Nat.add_le_add_left ihq _⟩

end PfaffianGeneralReduce
end MachLib
