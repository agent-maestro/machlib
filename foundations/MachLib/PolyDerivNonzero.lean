/-
# The derivative of an irreducible polynomial is not the zero polynomial

`no_rational_logarithm` takes `hchar : ∀ r, DerivCoprime q (r + 1)`. `derivCoprime_of_ne_zero`
(`PolyDerivShort`) reduces that to `pnorm (pnsum (k+1) (pderiv q)) ≠ []`, and this module discharges
it outright from `PIrred q`.

**Why the route is analytic rather than algebraic.** The obvious argument is "the leading coefficient
of `q'` is `(n-1)·aₙ ≠ 0`", but `pderiv` does not trim: `pderiv [a, b] = [b, 0]`. Reading a leading
coefficient off it means the index development `PolyDerivShort` deliberately avoided. Instead this
goes through `pev`: if `q' ≡ 0` then `pev q` has zero derivative everywhere, the mean value theorem
makes it constant, and `peq_of_ev_eq` turns that back into `PEq q [c]` — so `q` has length ≤ 1,
contradicting `2 ≤ q.length`. No new axioms, and `peq_of_ev_eq` finds its first consumer.
-/
import MachLib.PevEvEq
import MachLib.PevDeriv
import MachLib.Rolle
import MachLib.PolyDivision
import MachLib.QuadraticRoots
import MachLib.Forge
import MachLib.Differentiation
import MachLib.PolyDerivShort
import MachLib.BipevClearedDeriv
import MachLib.FieldLemmas

namespace MachLib


theorem pnorm_pderiv_ne_nil {q : List Real} (hqn : PNormal q) (hq2 : 2 ≤ q.length) :
    pnorm (pderiv q) ≠ [] := by
  intro hzero
  have hdz : ∀ x : Real, pev (pderiv q) x = 0 := by
    intro x
    have h := pev_pnorm (pderiv q) x
    rw [hzero] at h
    exact h.symm
  have hsing : ∀ x : Real, pev [pev q 1] x = pev q 1 := by
    intro x
    show pev q 1 + x * (0:Real) = pev q 1
    mach_ring
  -- `1 < 1+1`, inlined rather than imported: the only public home is a witness module, and a
  -- polynomial file should not depend on one.
  have h11 : (1:Real) < 1 + 1 := by
    have h := Real.add_lt_add_left Real.zero_lt_one_ax (1 : Real)
    rwa [Real.add_zero] at h
  -- Base the comparison at `1` but only ever *evaluate* from `1+1` on, so `1 < x` is free
  -- and the MVT never sees a degenerate interval.
  have hconst : ∀ x : Real, (1+1:Real) ≤ x → pev q x = pev [pev q 1] x := by
    intro x hx
    rw [hsing x]
    have hlt : (1:Real) < x := Real.lt_of_lt_of_le h11 hx
    obtain ⟨c, f', _, _, hd, heq⟩ :=
      Real.mean_value_theorem_ct (fun y => pev q y) 1 x hlt
        (fun c _ _ => ⟨pev (pderiv q) c, hasDerivAt_pev q c⟩)
    have hf0 : f' = 0 := by
      rw [Real.HasDerivAt_unique (fun y => pev q y) f' (pev (pderiv q) c) c hd (hasDerivAt_pev q c)]
      exact hdz c
    rw [hf0] at heq
    refine QuadraticRoots.eq_of_sub_eq_zero ?_
    show pev q x - pev q 1 = 0
    rw [heq]; mach_ring
  have hpeq : PEq q [pev q 1] := peq_of_ev_eq (X := 1+1) (Real.le_of_lt h11) hconst
  have hq_eq : q = pnorm [pev q 1] := Eq.trans (pnorm_eq_self q hqn).symm hpeq
  have hlen : q.length ≤ 1 := by
    rw [hq_eq]
    exact Nat.le_trans (pnorm_length_le _) (Nat.le_refl 1)
  omega

/-- Scaling by a positive integer cannot annihilate a non-zero polynomial. -/
theorem pnorm_pnsum_succ_ne_nil {Z : List Real} {k : Nat} (hZ : pnorm Z ≠ []) :
    pnorm (pnsum (k + 1) Z) ≠ [] := by
  intro hzero
  refine hZ ?_
  have hscale : (0 : Real) < natMul (k + 1) 1 := by
    have h0 : (0 : Real) ≤ natMul k 1 := natMul_nonneg k
    have h1 : (1 : Real) + 0 ≤ 1 + natMul k 1 := Real.add_le_add_left h0 1
    rw [Real.add_zero] at h1
    exact Real.lt_of_lt_of_le Real.zero_lt_one_ax h1
  have hne : natMul (k + 1) 1 ≠ 0 := fun h => Real.lt_irrefl_ax 0 (h ▸ hscale)
  have hev : ∀ x : Real, (1:Real) ≤ x → pev Z x = pev [] x := by
    intro x _
    have h := pev_pnorm (pnsum (k + 1) Z) x
    rw [hzero] at h
    have hz : natMul (k + 1) (pev Z x) = 0 := by
      rw [← pev_pnsum]; exact h.symm
    rw [natMul_eq] at hz
    -- `by_contra` does not exist in MachLib; cancel the scalar on the left instead
    refine Real.mul_left_cancel hne ?_
    exact Eq.trans hz (show (0:Real) = natMul (k + 1) 1 * (0:Real) by mach_ring)
  exact peq_of_ev_eq (X := 1) (Real.le_refl 1) hev

/-- **`hchar`, discharged.** -/
theorem derivCoprime_of_irred {q : List Real} (hq : PIrred q) (r : Nat) :
    DerivCoprime q (r + 1) :=
  derivCoprime_of_ne_zero hq (pnorm_pnsum_succ_ne_nil (pnorm_pderiv_ne_nil hq.1 hq.2.1))

end MachLib
