import MachLib.EMLQueryGermTerm
import MachLib.EMLZeroBoundRay
import MachLib.PolynomialRootCount
import MachLib.PevRoots

/-!
# The query germ's ZERO branch — `u` eventually zero

`ratGerm_eventual_sign` (`PevSignGerm`) splits a rational germ three ways, and
`oneQueryDichotomy_of_uniformBoundsFrom` needs a uniform zero bound on each. `EMLQueryGermTerm`
handled the branch where `u = pev P / pev Q` is eventually **positive**. This is the branch where it
is eventually **zero**, and it is the cheap one — for a reason worth naming.

## Totalisation does the work

Where `u x = 0`, `Fbasis (u x) = exp 0 + log₀ 0 = 1 + 0 = 1` (`Fbasis_zero`): the totalised `log`
annihilates itself at the boundary. So on that ray the germ is

```
bipev N x (Fbasis (u x))  =  bipev N x 1  =  pev (sumCoeffs N) x
```

— an ordinary univariate polynomial, whose coefficient list is the **coefficientwise sum** of `N`'s
rows, because Horner at `y = 1` just adds them. No transcendental survives, so none of the Khovanskii
machinery is needed: `poly_root_count_bound` applies directly, and its bound is `degreeUpper`, which
**mentions no interval**. That is exactly the `UniformZeroBoundFrom` shape.

The `¬ EvZeroF` hypothesis is what makes the polynomial non-trivial: without it the germ could be
identically zero and no bound would exist, which is the same conditioning `EMLZeroBoundRay` explains
at length for the general antecedent.
-/

namespace MachLib

open Real
open MachLib.PolynomialEvidence
open MachLib.PolynomialRootCount

/-- A coefficient list as a `Poly`, Horner — mirroring `pev` constructor for constructor, so the
eval agreement is definitional at every step. -/
noncomputable def pevPoly : List Real → Poly
  | []      => Poly.const 0
  | c :: cs => Poly.add (Poly.const c) (Poly.mul Poly.var (pevPoly cs))

theorem pevPoly_eval : ∀ (L : List Real) (x : Real), Poly.eval (pevPoly L) x = pev L x
  | [], _ => rfl
  | c :: cs, x => by
      show c + x * Poly.eval (pevPoly cs) x = c + x * pev cs x
      rw [pevPoly_eval cs x]

/-- The coefficientwise sum of a bivariate polynomial's rows — what Horner collapses to at `y = 1`. -/
noncomputable def sumCoeffs : List (List Real) → List Real
  | []      => []
  | L :: Ls => padd L (sumCoeffs Ls)

/-- **At `y = 1`, a bivariate polynomial is the sum of its rows.** -/
theorem bipev_at_one : ∀ (N : List (List Real)) (x : Real),
    bipev N x 1 = pev (sumCoeffs N) x
  | [], _ => rfl
  | L :: Ls, x => by
      show pev L x + 1 * bipev Ls x 1 = pev (padd L (sumCoeffs Ls)) x
      rw [pev_padd, bipev_at_one Ls x]
      mach_ring

/-- **The zero branch, bounded.** Where `u` is eventually zero the germ is a polynomial on that ray,
so `degreeUpper` of its Horner encoding bounds the zeros of every interval beyond it — one constant,
no interval in it.

Note which hypothesis does what: `hz` collapses the germ to a polynomial, and `hne` is what makes
that polynomial non-zero, hence boundable at all. -/
theorem queryGerm_zero_branch_bound (N : List (List Real)) (P Q : List Real)
    (hz : EvZeroF (fun x => pev P x / pev Q x))
    (hne : ¬ EvZeroF (fun x => bipev N x (Fbasis (pev P x / pev Q x)))) :
    ∃ (K : Nat) (R : Real),
      UniformZeroBoundFrom (fun x => bipev N x (Fbasis (pev P x / pev Q x))) R K := by
  obtain ⟨X, hX1, hu0raw⟩ := hz
  -- `obtain` leaves an UNREDUCED application `(fun x => …) x`; bind it through a typed `have`
  -- so `rw` can match the beta-reduced goal (the standing gotcha for this corpus)
  have hu0 : ∀ x : Real, X ≤ x → pev P x / pev Q x = 0 := fun x hx => hu0raw x hx
  -- on the ray the germ IS the polynomial
  have hgerm : ∀ x : Real, X ≤ x →
      bipev N x (Fbasis (pev P x / pev Q x)) = Poly.eval (pevPoly (sumCoeffs N)) x := by
    intro x hx
    rw [hu0 x hx, Fbasis_zero, bipev_at_one, pevPoly_eval]
  -- `¬ EvZeroF` gives the nonzero witness the root count needs
  have hwit : ∃ x : Real, Poly.eval (pevPoly (sumCoeffs N)) x ≠ 0 := by
    rcases Classical.em (∃ x : Real, X ≤ x ∧
        bipev N x (Fbasis (pev P x / pev Q x)) ≠ 0) with ⟨w, hw, hw0⟩ | hno
    · exact ⟨w, by rw [← hgerm w hw]; exact hw0⟩
    · exact absurd ⟨X, hX1, fun x hx => by
        rcases Classical.em (bipev N x (Fbasis (pev P x / pev Q x)) = 0) with h | h
        · exact h
        · exact absurd ⟨x, hx, h⟩ hno⟩ hne
  refine ⟨degreeUpper (pevPoly (sumCoeffs N)), X, ?_⟩
  intro a b hXa hab zeros hnd hz'
  refine poly_root_count_bound (pevPoly (sumCoeffs N)) a b hab hwit zeros hnd ?_
  intro z hzmem
  obtain ⟨h1, h2, h0⟩ := hz' z hzmem
  exact ⟨h1, h2, by rw [← hgerm z (le_trans hXa (le_of_lt h1))]; exact h0⟩

end MachLib
