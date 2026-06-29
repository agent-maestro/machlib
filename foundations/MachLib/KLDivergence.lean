import MachLib.EntropyDuality

/-!
# The Gibbs inequality — `KL(p ‖ q) ≥ 0` over a finite distribution (machine-checked)

`EntropyDuality.gibbs_pointwise` already verifies the *pointwise* content of relative
entropy — `pᵢ · log(qᵢ/pᵢ) ≤ qᵢ − pᵢ`, the tangent-line bound. This file lifts it to the
**full, summed** statement: for any finite pair of strictly-positive weight lists with the
same total mass, the Kullback–Leibler divergence is non-negative,

  `KL(p ‖ q) = Σ pᵢ · log(pᵢ / qᵢ) ≥ 0`   (Gibbs' inequality),

with equality the conjugacy point of the exp↔entropy duality. This is the
information-theory frontier's (`T1.B` / `T3.D`) load-bearing inequality — *why entropy is
bounded* and *why MaxEnt selects the exponential family* — now machine-checked as a theorem
over a distribution, not just pointwise.

The proof is one `List` induction summing `gibbs_pointwise` (the same fold shape as
`VectorError.aerr_sum`): `Σ pᵢ·log(qᵢ/pᵢ) ≤ Σ(qᵢ − pᵢ) = (Σqᵢ) − (Σpᵢ)`, which is `≤ 0`
when the masses match. No integration, no measure theory — Mathlib-free, `sorryAx`-free,
**no new axioms** (rests on the existing `Log`/`EntropyDuality` base).

A finite distribution is a `List (Real × Real)` of `(pᵢ, qᵢ)` pairs.
-/

namespace MachLib
namespace Real

/-- `Σ pᵢ` (total mass of the first component). `foldr` reduces by `rfl`. -/
noncomputable def psum (d : List (Real × Real)) : Real := d.foldr (fun c acc => c.1 + acc) 0
/-- `Σ qᵢ` (total mass of the second component). -/
noncomputable def qsum (d : List (Real × Real)) : Real := d.foldr (fun c acc => c.2 + acc) 0
/-- `Σ pᵢ · log(qᵢ / pᵢ)` — the **negative** KL divergence; `KL(p‖q) = −klGap`. -/
noncomputable def klGap (d : List (Real × Real)) : Real :=
  d.foldr (fun c acc => c.1 * Real.log (c.2 / c.1) + acc) 0
/-- The KL divergence `Σ pᵢ · log(pᵢ / qᵢ) = −klGap`. -/
noncomputable def kl (d : List (Real × Real)) : Real := -klGap d

/-- Every component is strictly positive (`pᵢ, qᵢ > 0`) — a genuine distribution support. -/
def Pos (d : List (Real × Real)) : Prop :=
  d.foldr (fun c acc => 0 < c.1 ∧ 0 < c.2 ∧ acc) True

/-- **The summed Gibbs bound.** `Σ pᵢ·log(qᵢ/pᵢ) ≤ (Σqᵢ) − (Σpᵢ)` — one list induction
folding the pointwise `gibbs_pointwise` tangent-line bound. -/
theorem klGap_le : ∀ {d : List (Real × Real)}, Pos d → klGap d ≤ qsum d - psum d
  | [], _ => le_of_eq (show (0 : Real) = 0 - 0 from by mach_ring)
  | (c :: r), h => by
      obtain ⟨hp, hq, hr⟩ := h
      show c.1 * Real.log (c.2 / c.1) + klGap r ≤ (c.2 + qsum r) - (c.1 + psum r)
      exact le_trans (add_le_add_both (gibbs_pointwise hp hq) (klGap_le hr))
        (le_of_eq (by mach_ring))

/-- **Gibbs' inequality / non-negativity of KL divergence.** For a finite distribution of
strictly-positive weights with equal total mass (`Σpᵢ = Σqᵢ`, e.g. both normalised to 1),
`KL(p ‖ q) = Σ pᵢ·log(pᵢ/qᵢ) ≥ 0`. The information-theory frontier's keystone, machine-checked
over a distribution — lifting the pointwise `gibbs_pointwise` to the full sum. -/
theorem kl_nonneg {d : List (Real × Real)} (h : Pos d) (hmass : psum d = qsum d) :
    0 ≤ kl d := by
  have hle : klGap d ≤ 0 := by
    have h0 := klGap_le h
    rwa [hmass, show qsum d - qsum d = (0 : Real) from by mach_ring] at h0
  show 0 ≤ -klGap d
  rw [show (0 : Real) = -0 from by mach_ring]
  exact neg_le_neg hle

/-- **A concrete two-point distribution.** Two strictly-positive `(pᵢ, qᵢ)` pairs of equal
total mass (e.g. `p, q` both summing to 1) have `KL(p ‖ q) ≥ 0` — the theorem applied to a
real distribution, machine-checked. -/
theorem kl_nonneg_two {p1 q1 p2 q2 : Real}
    (hp1 : 0 < p1) (hq1 : 0 < q1) (hp2 : 0 < p2) (hq2 : 0 < q2)
    (hmass : p1 + p2 = q1 + q2) :
    0 ≤ kl [(p1, q1), (p2, q2)] :=
  kl_nonneg ⟨hp1, hq1, hp2, hq2, trivial⟩
    (by show p1 + (p2 + 0) = q1 + (q2 + 0)
        rw [show p1 + (p2 + 0) = p1 + p2 from by mach_ring,
            show q1 + (q2 + 0) = q1 + q2 from by mach_ring]
        exact hmass)

end Real
end MachLib
