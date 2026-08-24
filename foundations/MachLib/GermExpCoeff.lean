import MachLib.GermDerivEntry
import MachLib.BipevAllZero

/-!
# Germ coefficients that are polynomials in `e^S`

`minimal_grel_identity` is stated for arbitrary differentiable germ coefficients. The `S > 0` branch
instantiates it at the ones that matter: coefficients in `R(x)[E]`, i.e. `cⱼ(x) = Cⱼ(x, e^(S x))`
for syntactic `Cⱼ : List (List Real)`.

The only thing to supply is `GDerivAt`, and `hasDerivAt_bipev_exp` already differentiates exactly
this shape — `dbipevExp` is its derivative, kept in value form rather than as a coefficient family
precisely because `S'` is rational rather than polynomial. That decision, made for brick four, is
what makes this instantiation a map over a list and nothing more.

## What this does *not* do

It does not yet turn the resulting germ identity into a **syntactic** one. That is
`all_coeffs_nil_of_relation`'s job, and it needs the identity rearranged into a relation in `e^S`
first — the coefficients of that rearrangement are products of the `Cⱼ`, so the step is polynomial
bookkeeping over `R(x)[E]`, not analysis.
-/

namespace MachLib

open Real

/-- Coefficients `cⱼ(x) = Cⱼ(x, e^(S x))`. -/
noncomputable def expCoeffs (S : Real → Real) (Cs : List (List (List Real))) : List (Real → Real) :=
  Cs.map (fun C => fun x => bipev C x (exp (S x)))

/-- Their derivatives, in `dbipevExp`'s value form. -/
noncomputable def expCoeffsD (S S' : Real → Real) (Cs : List (List (List Real))) :
    List (Real → Real) :=
  Cs.map (fun C => fun x => dbipevExp C S (S' x) x)

theorem gDerivAt_expCoeffs {S S' : Real → Real} {x : Real} (hS : HasDerivAt S (S' x) x) :
    ∀ Cs : List (List (List Real)), GDerivAt x (expCoeffs S Cs) (expCoeffsD S S' Cs) := by
  intro Cs
  induction Cs with
  | nil => exact trivial
  | cons C Cs ih => exact ⟨hasDerivAt_bipev_exp C S (S' x) x hS, ih⟩

theorem expCoeffs_concat (S : Real → Real) (Cs₀ : List (List (List Real)))
    (Cd : List (List Real)) :
    expCoeffs S (Cs₀ ++ [Cd]) = expCoeffs S Cs₀ ++ [fun x => bipev Cd x (exp (S x))] := by
  simp [expCoeffs]

theorem expCoeffsD_concat (S S' : Real → Real) (Cs₀ : List (List (List Real)))
    (Cd : List (List Real)) :
    expCoeffsD S S' (Cs₀ ++ [Cd]) = expCoeffsD S S' Cs₀ ++ [fun x => dbipevExp Cd S (S' x) x] := by
  simp [expCoeffsD]

/-! ## The identity, at `R(x)[E]` coefficients -/

/-- **`minimal_grel_identity`, instantiated.** A minimal relation for `u` whose coefficients are
polynomials in `e^S` forces the same two-coefficient identity, now written entirely in `bipev` and
`dbipevExp` — no germ variables left. -/
theorem minimal_expRel_identity {S S' u v : Real → Real}
    {Cs Cs₀ : List (List (List Real))} {Cd Cd1 : List (List Real)} {m : Nat}
    (hS : ∃ X : Real, 1 ≤ X ∧ ∀ x : Real, X ≤ x → HasDerivAt S (S' x) x)
    (hu : ∃ X : Real, 1 ≤ X ∧ ∀ x : Real, X ≤ x → HasDerivAt u (v x) x)
    (hmin : ∀ ns : List (Real → Real), GProperRel u ns → (expCoeffs S Cs).length ≤ ns.length)
    (hrel : GEvRel u (expCoeffs S Cs))
    (hCs : Cs = Cs₀ ++ [Cd]) (hlen0 : Cs₀.length = m + 1)
    (hCd1 : Cs₀[m]? = some Cd1) :
    EvZeroF (fun x =>
      bipev Cd x (exp (S x)) *
          (dbipevExp Cd1 S (S' x) x
            + v x * (natMul (m + 1) 1 * bipev Cd x (exp (S x))))
        - dbipevExp Cd S (S' x) x * bipev Cd1 x (exp (S x))) := by
  obtain ⟨X, hX, hS'⟩ := hS
  refine minimal_grel_identity (es := expCoeffsD S S' Cs) hu
    ⟨X, hX, fun x hx => gDerivAt_expCoeffs (hS' x hx) Cs⟩ hmin hrel
    (by rw [hCs, expCoeffs_concat]) (by rw [hCs, expCoeffsD_concat])
    (by rw [expCoeffs]; simpa using hlen0) (by rw [expCoeffsD]; simpa using hlen0)
    (by rw [expCoeffs, List.getElem?_map, hCd1]; rfl)
    (by rw [expCoeffsD, List.getElem?_map, hCd1]; rfl)

end MachLib
