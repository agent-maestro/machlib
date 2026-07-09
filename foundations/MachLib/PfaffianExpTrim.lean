import MachLib.PfaffianExpEliminate
import MachLib.PfaffianLogGeneralDegree

/-!
# `exp_hard` — the eval-zero trim of `expEliminate` (B2)

B1 (`PfaffianExpEliminate`) built the elimination polynomial `expEliminate c G top p`, whose **formal**
`degreeY_top` equals `degreeY_top p = D+1` (`expEliminate_degreeY_top_eq`) but whose leading `y_top`
coefficient **evaluates** to 0 along the chain (`expEliminate_lcY_top_eval_zero`). That leading term is
therefore *phantom*: dropping it does not change `pfaffianChainFn c (expEliminate …)` on the interval, and
the trimmed polynomial has `degreeY_top ≤ D`.

This is exactly the hypothesis of the log-arm's already-general trim-and-recurse `bound_via_trim_rec`
(`PfaffianLogGeneralDegree`): given a recursor `rec` valid at top-degree `≤ D`, it bounds the zeros of any
`q` with `degreeY_top q ≤ D+1` whose degree-`(D+1)` coefficient is eval-zero everywhere. Specialising `q :=
expEliminate c G top p` and discharging its `h_lead` from B1 gives **B2**: the exp-eliminated barrier's
zeros are bounded by the depth-`≤ D` recursor. No new axioms — pure reuse of the log-arm trim + B1.
-/

namespace MachLib.PfaffianExpTrim

open MachLib.Real
open MachLib.MultiPolyMod MachLib.MultiPolyMod.MultiPoly
open MachLib.PfaffianChainMod
open MachLib.PfaffianChainMod.PfaffianFn
open MachLib.PfaffianGeneralReduce
open MachLib.PfaffianExpEliminate
open MachLib.PfaffianLogLead

/-- **B2 — the eval-zero trim.** For an exp top (`relations top = G·y_top`, `degreeY_top G = 0`, triangular)
and a barrier `p` with `degreeY_top p = D+1`, the elimination polynomial `expEliminate c G top p` has its top
exponential eliminated: its formal top degree is `D+1` but the leading coefficient evaluates to 0, so a
recursor `rec` valid at top-degree `≤ D` bounds its zeros on `(a,b)`. Direct specialisation of
`bound_via_trim_rec` with `h_lead` discharged by `expEliminate_lcY_top_eval_zero` (B1). -/
theorem expEliminate_zeros_bound {N : Nat} (c : PfaffianChain N) (G : MultiPoly N) (top : Fin N)
    (h_reltop : c.relations top = MultiPoly.mul G (MultiPoly.varY top))
    (h_Gtop : MultiPoly.degreeY top G = 0)
    (h_tri : ∀ j : Fin N, j ≠ top → MultiPoly.degreeY top (c.relations j) = 0)
    (p : MultiPoly N) (D : Nat) (hDp : MultiPoly.degreeY top p = D + 1)
    (a b : Real)
    (rec : ∀ r : MultiPoly N, MultiPoly.degreeY top r ≤ D →
        (∃ z, a < z ∧ z < b ∧ (pfaffianChainFn c r).eval z ≠ 0) →
        ∃ M : Nat, ∀ zeros : List Real, zeros.Nodup →
          (∀ z ∈ zeros, a < z ∧ z < b ∧ (pfaffianChainFn c r).eval z = 0) → zeros.length ≤ M)
    (hne : ∃ z, a < z ∧ z < b ∧ (pfaffianChainFn c (expEliminate c G top p)).eval z ≠ 0) :
    ∃ M : Nat, ∀ zeros : List Real, zeros.Nodup →
      (∀ z ∈ zeros, a < z ∧ z < b ∧ (pfaffianChainFn c (expEliminate c G top p)).eval z = 0) →
        zeros.length ≤ M := by
  have hEEdeg : MultiPoly.degreeY top (expEliminate c G top p) = D + 1 := by
    rw [expEliminate_degreeY_top_eq c G top h_reltop h_Gtop h_tri p, hDp]
  refine bound_via_trim_rec c top a b D rec (expEliminate c G top p) (Nat.le_of_eq hEEdeg) ?_ hne
  intro _hq1 x env
  rw [← hEEdeg, getD_at_degreeY_eq_lcY_eval top (expEliminate c G top p) x env]
  exact expEliminate_lcY_top_eval_zero c G top h_reltop h_Gtop h_tri p x env

end MachLib.PfaffianExpTrim
