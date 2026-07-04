import MachLib.PfaffianChain
import MachLib.Differentiation
import MachLib.Log
import MachLib.MultiPoly

/-!
# General exp-chain integrating-factor exponent (log-vehExpo) — the analytic heart

For an ARBITRARY Pfaffian chain `c` that is coherent and positive at `z`, the exponent
`E(z) = Σ_{i<k} (−degᵢ)·log(yᵢ(z))` has derivative `Σ_{i<k} (−degᵢ)·(yᵢ'(z)/yᵢ(z))`. Since coherence gives
`yᵢ'(z) = (relations i)(z, chainValues)`, this is the general integrating factor. Positivity is genuinely
needed (unlike the iterated-exp `vehExpo`, whose iterExp levels ARE polynomial antiderivatives) because a
general exp-chain's `Gᵢ = yᵢ'/yᵢ` integrates to `log yᵢ`.
-/

namespace MachLib.PfaffianGeneralVehExpo
open MachLib.Real MachLib.PfaffianChainMod MachLib.MultiPolyMod

/-- The general log-vehExpo exponent summed over the first `k` chain levels:
`Σ_{i<k} (−degᵢ)·log(yᵢ(·))`. -/
noncomputable def logVehExpoAux {n : Nat} (c : PfaffianChain n) (deg : Fin n → Nat) :
    (k : Nat) → k ≤ n → (Real → Real)
  | 0, _ => fun _ => 0
  | k + 1, hk => fun z =>
      (-MachLib.Real.natCast (deg ⟨k, hk⟩)) * Real.log (c.evals ⟨k, hk⟩ z)
      + logVehExpoAux c deg k (Nat.le_of_succ_le hk) z

/-- The derivative value of `logVehExpoAux` at `z`: `Σ_{i<k} (−degᵢ)·((1/yᵢ(z))·(relations i)(z,·))`. -/
noncomputable def logVehExpoDerivAux {n : Nat} (c : PfaffianChain n) (deg : Fin n → Nat) (z : Real) :
    (k : Nat) → k ≤ n → Real
  | 0, _ => 0
  | k + 1, hk =>
      (-MachLib.Real.natCast (deg ⟨k, hk⟩))
        * ((1 / c.evals ⟨k, hk⟩ z) * MultiPoly.eval (c.relations ⟨k, hk⟩) z (c.chainValues z))
      + logVehExpoDerivAux c deg z k (Nat.le_of_succ_le hk)

/-- **`HasDerivAt` for the general log-vehExpo exponent, `∀ k ≤ n`.** By induction on the level count `k`;
each level is `HasDerivAt_mul (const)` of the log-chain-rule `HasDerivAt_comp log (evals i)` (coherence +
positivity). This is the general analog of `HasDerivAt_vehExpo`. -/
theorem HasDerivAt_logVehExpoAux {n : Nat} (c : PfaffianChain n) (deg : Fin n → Nat) (z : Real)
    (hcoh : PfaffianChain.IsCoherentAt c z) (hpos : ∀ i : Fin n, 0 < c.evals i z) :
    ∀ (k : Nat) (hk : k ≤ n),
      HasDerivAt (logVehExpoAux c deg k hk) (logVehExpoDerivAux c deg z k hk) z := by
  intro k
  induction k with
  | zero =>
    intro hk
    show HasDerivAt (fun _ => 0) 0 z
    exact HasDerivAt_const 0 z
  | succ k ih =>
    intro hk
    show HasDerivAt
      (fun z => (-MachLib.Real.natCast (deg ⟨k, hk⟩)) * Real.log (c.evals ⟨k, hk⟩ z)
                + logVehExpoAux c deg k (Nat.le_of_succ_le hk) z)
      ((-MachLib.Real.natCast (deg ⟨k, hk⟩))
          * ((1 / c.evals ⟨k, hk⟩ z) * MultiPoly.eval (c.relations ⟨k, hk⟩) z (c.chainValues z))
        + logVehExpoDerivAux c deg z k (Nat.le_of_succ_le hk)) z
    have hlog : HasDerivAt (fun z => Real.log (c.evals ⟨k, hk⟩ z))
        ((1 / c.evals ⟨k, hk⟩ z) * MultiPoly.eval (c.relations ⟨k, hk⟩) z (c.chainValues z)) z :=
      HasDerivAt_comp Real.log (c.evals ⟨k, hk⟩)
        (MultiPoly.eval (c.relations ⟨k, hk⟩) z (c.chainValues z)) (1 / c.evals ⟨k, hk⟩ z) z
        (hcoh ⟨k, hk⟩) (HasDerivAt_log_pos (c.evals ⟨k, hk⟩ z) (hpos ⟨k, hk⟩))
    have hlvl : HasDerivAt (fun z => (-MachLib.Real.natCast (deg ⟨k, hk⟩)) * Real.log (c.evals ⟨k, hk⟩ z))
        ((-MachLib.Real.natCast (deg ⟨k, hk⟩))
          * ((1 / c.evals ⟨k, hk⟩ z) * MultiPoly.eval (c.relations ⟨k, hk⟩) z (c.chainValues z))) z := by
      have h := HasDerivAt_mul (fun _ => -MachLib.Real.natCast (deg ⟨k, hk⟩))
        (fun z => Real.log (c.evals ⟨k, hk⟩ z)) 0
        ((1 / c.evals ⟨k, hk⟩ z) * MultiPoly.eval (c.relations ⟨k, hk⟩) z (c.chainValues z)) z
        (HasDerivAt_const _ z) hlog
      rw [zero_mul, zero_add] at h
      exact h
    exact HasDerivAt_add
      (fun z => (-MachLib.Real.natCast (deg ⟨k, hk⟩)) * Real.log (c.evals ⟨k, hk⟩ z))
      (logVehExpoAux c deg k (Nat.le_of_succ_le hk)) _ _ z hlvl (ih (Nat.le_of_succ_le hk))

end MachLib.PfaffianGeneralVehExpo
