import MachLib.IterExpDepth3Vehicle

/-!
# Depth-3 polynomial-multiplier Rolle transfer: `#zeros(f) ≤ N + 1`

The "reduce costs one zero" step, built on the depth-3 vehicle (`IterExpDepth3Vehicle`). If `N` bounds
the zeros of the graded reduce value `f' − (d₂·y₀y₁ + d₁·y₀ + c)·f` on `(a,b)`, then `f` has at most
`N + 1` zeros there. This is the counting content that the classical axiom `zero_count_bound_classical`
merely asserts — here derived by *reduction* via Rolle (`zero_count_bound_by_deriv`) applied to the
vehicle (same zeros as `f`), plus the bridge (a zero of the vehicle's derivative is a zero of the
reduce). Mirrors chain-2's `ChainExp2PolyMultRolle.zero_count_polyMultReduce_transfer` one level up.
Path B; no `sorry`.
-/

namespace MachLib.IterExpDepth3Rolle

open MachLib.Real
open MachLib.MultiPolyMod
open MachLib.PfaffianChainMod
open MachLib.PfaffianChainMod.PfaffianFn
open MachLib.IterExpChainMod
open MachLib.IterExpDepth3Descent
open MachLib.IterExpDepth3Vehicle

/-- **The Rolle bridge.** At a point `z` where the vehicle's derivative is 0, the graded reduce value
`f' − (d₂·y₀y₁ + d₁·y₀ + c)·f` is 0. -/
theorem polyMultReduce3_eval_zero_of_vehicle_deriv_zero
    (f : PfaffianFn) (d2 d1 : Nat) (c : Real) (z : Real)
    (hf : HasDerivAt f.eval (f.chainTotalDerivative.eval z) z)
    (g'' : Real)
    (hg''_deriv : HasDerivAt (vehicleM3 f d2 d1 c) g'' z)
    (hg''_zero : g'' = 0) :
    f.chainTotalDerivative.eval z
      - (MachLib.Real.natCast d2 * (iterExp 0 z * iterExp 1 z)
         + MachLib.Real.natCast d1 * iterExp 0 z + c) * f.eval z = 0 := by
  have hcanonical := hasDerivAt_vehicleM3 f d2 d1 c z hf
  have huniq := HasDerivAt_unique (vehicleM3 f d2 d1 c) g''
                  (f.chainTotalDerivative.eval z
                      * Real.exp ((-MachLib.Real.natCast d2) * iterExp 1 z
                          + (-MachLib.Real.natCast d1) * iterExp 0 z + (-c) * z)
                    + f.eval z
                      * (Real.exp ((-MachLib.Real.natCast d2) * iterExp 1 z
                            + (-MachLib.Real.natCast d1) * iterExp 0 z + (-c) * z)
                         * ((-MachLib.Real.natCast d2) * (iterExp 0 z * iterExp 1 z)
                            + (-MachLib.Real.natCast d1) * iterExp 0 z + (-c))))
                  z hg''_deriv hcanonical
  have hraw_zero :
      f.chainTotalDerivative.eval z
          * Real.exp ((-MachLib.Real.natCast d2) * iterExp 1 z
              + (-MachLib.Real.natCast d1) * iterExp 0 z + (-c) * z)
        + f.eval z
          * (Real.exp ((-MachLib.Real.natCast d2) * iterExp 1 z
                + (-MachLib.Real.natCast d1) * iterExp 0 z + (-c) * z)
             * ((-MachLib.Real.natCast d2) * (iterExp 0 z * iterExp 1 z)
                + (-MachLib.Real.natCast d1) * iterExp 0 z + (-c))) = 0 := by
    rw [← huniq]; exact hg''_zero
  rw [vehicle3_deriv_factor (f.chainTotalDerivative.eval z) (f.eval z)
        (Real.exp ((-MachLib.Real.natCast d2) * iterExp 1 z
          + (-MachLib.Real.natCast d1) * iterExp 0 z + (-c) * z))
        (MachLib.Real.natCast d2) (MachLib.Real.natCast d1) (iterExp 0 z) (iterExp 1 z) c] at hraw_zero
  exact mul_eq_zero_of_factor_ne_zero (exp_ne_zero _) hraw_zero

/-- **Raw zero-count transfer** (in terms of zeros of the vehicle's derivative). -/
theorem zero_count_polyMultReduce3_transfer_raw
    (f : PfaffianFn) (d2 d1 : Nat) (c : Real) (a b : Real) (hab : a < b)
    (hcoherent : f.chain.IsCoherentOn a b)
    (N : Nat)
    (h_reduced_bound : ∀ zeros' : List Real,
        zeros'.Nodup →
        (∀ z ∈ zeros', a < z ∧ z < b ∧
          ∃ f'' : Real, HasDerivAt (vehicleM3 f d2 d1 c) f'' z ∧ f'' = 0) →
        zeros'.length ≤ N) :
    ∀ zeros_f : List Real,
      zeros_f.Nodup →
      (∀ z ∈ zeros_f, a < z ∧ z < b ∧ f.eval z = 0) →
      zeros_f.length ≤ N + 1 := by
  intro zeros_f hnodup hzeros
  have hzeros_g : ∀ z ∈ zeros_f, a < z ∧ z < b ∧ vehicleM3 f d2 d1 c z = 0 := by
    intro z hz
    obtain ⟨haz, hzb, hfz⟩ := hzeros z hz
    exact ⟨haz, hzb, (vehicleM3_zero_iff f d2 d1 c z).mpr hfz⟩
  have hdiff : ∀ x : Real, a < x → x < b →
                ∃ f' : Real, HasDerivAt (vehicleM3 f d2 d1 c) f' x := by
    intro x hax hxb
    exact ⟨_, hasDerivAt_vehicleM3 f d2 d1 c x (hasDerivAt_eval_natural f x (hcoherent x hax hxb))⟩
  exact zero_count_bound_by_deriv (vehicleM3 f d2 d1 c) a b hab hdiff N
          h_reduced_bound zeros_f hnodup hzeros_g

/-- **Zero-count transfer (eval form).** If the graded reduce value has at most `N` zeros on `(a,b)`,
then `f` has at most `N + 1`. The constructive Rolle step for the depth-3 poly-multiplier reduce. -/
theorem zero_count_polyMultReduce3_transfer
    (f : PfaffianFn) (d2 d1 : Nat) (c : Real) (a b : Real) (hab : a < b)
    (hcoherent : f.chain.IsCoherentOn a b)
    (N : Nat)
    (h_reduced_bound_eval : ∀ zeros' : List Real,
        zeros'.Nodup →
        (∀ z ∈ zeros', a < z ∧ z < b ∧
          f.chainTotalDerivative.eval z
            - (MachLib.Real.natCast d2 * (iterExp 0 z * iterExp 1 z)
               + MachLib.Real.natCast d1 * iterExp 0 z + c) * f.eval z = 0) →
        zeros'.length ≤ N) :
    ∀ zeros_f : List Real,
      zeros_f.Nodup →
      (∀ z ∈ zeros_f, a < z ∧ z < b ∧ f.eval z = 0) →
      zeros_f.length ≤ N + 1 := by
  apply zero_count_polyMultReduce3_transfer_raw f d2 d1 c a b hab hcoherent N
  intro zeros' hnodup' hzeros'_prop
  apply h_reduced_bound_eval zeros' hnodup'
  intro z hz
  obtain ⟨haz, hzb, g'', hg''_deriv, hg''_zero⟩ := hzeros'_prop z hz
  exact ⟨haz, hzb,
    polyMultReduce3_eval_zero_of_vehicle_deriv_zero f d2 d1 c z
      (hasDerivAt_eval_natural f z (hcoherent z haz hzb)) g'' hg''_deriv hg''_zero⟩

/-- **Reduce step for the depth-3 bound.** `#zeros(chain3Fn p) ≤ N + 1` whenever `N` bounds the zeros
of `chain3Fn (chain3Reduce c p)` — the reduce value along the chain (`chain3Fn_chain3Reduce_eval`). This
is the `+1`-per-reduce Rolle step, wired to the actual `chain3Reduce` AST. -/
theorem chain3Fn_reduce_step (c : Real) (p : MultiPoly 3) (a b : Real) (hab : a < b)
    (N : Nat)
    (hN : ∀ zeros' : List Real, zeros'.Nodup →
        (∀ z ∈ zeros', a < z ∧ z < b ∧ (chain3Fn (chain3Reduce c p)).eval z = 0) →
        zeros'.length ≤ N) :
    ∀ zeros_f : List Real, zeros_f.Nodup →
      (∀ z ∈ zeros_f, a < z ∧ z < b ∧ (chain3Fn p).eval z = 0) →
      zeros_f.length ≤ N + 1 := by
  apply zero_count_polyMultReduce3_transfer (chain3Fn p)
    (MultiPoly.degreeY (⟨2, by omega⟩ : Fin 3) p)
    (MultiPoly.degreeY (⟨1, by omega⟩ : Fin 3) (MultiPoly.leadingCoeffY (⟨2, by omega⟩ : Fin 3) p))
    c a b hab (IterExpChain_isCoherentOn 3 a b) N
  intro zeros' hnodup' hz'
  apply hN zeros' hnodup'
  intro z hzmem
  obtain ⟨haz, hzb, hval⟩ := hz' z hzmem
  refine ⟨haz, hzb, ?_⟩
  rw [chain3Fn_chain3Reduce_eval]
  exact hval

end MachLib.IterExpDepth3Rolle
