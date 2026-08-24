import MachLib.GermIdentityClass
import MachLib.GermExpCoeff

/-!
# The `R(x)[E]` instantiation, with minimality restricted to a class

Third of the four modules (ca) named. `minimal_expRel_identity_in` is `minimal_expRel_identity` with
`Pr` threaded through — the body is unchanged and the three added hypotheses pass straight down to
`minimal_grel_identity_in`. `minimal_expRel_identity_unrestricted` recovers the existing theorem as
the `Pr := fun _ => True` instance.

## What `hPrd` has to say here

At the germ layer the split obligation is about `gscaleSub cd dtop cs₀ ds₀`. At this layer `cd` is
`fun x => bipev Cd x (e^(S x))` and `cs₀` is `expCoeffs S Cs₀`, so the obligation is spelled out in
those terms. It is still quantified over the split, for the same reason: `ds₀` and `dtop` are
produced inside the proof below this one.

## The remaining module

**No concrete class has been supplied yet.** Every theorem here is parameterised, and until some
caller instantiates `Pr` at a class for which minimality is *dischargeable* — for the `S > 0` arc,
germs of the form (rational in `x`)·(polynomial in `E`) — `positive_branch_impossible` stays a
degree-one statement. That instantiation is the fourth module, and it is the one with genuine
content: the other three were transcription.
-/

namespace MachLib

open Real

/-- **The `R(x)[E]` identity, with minimality restricted to `Pr`.** -/
theorem minimal_expRel_identity_in {S S' u v : Real → Real}
    {Cs Cs₀ : List (List (List Real))} {Cd Cd1 : List (List Real)} {m : Nat}
    {Pr : List (Real → Real) → Prop}
    (hS : ∃ X : Real, 1 ≤ X ∧ ∀ x : Real, X ≤ x → HasDerivAt S (S' x) x)
    (hu : ∃ X : Real, 1 ≤ X ∧ ∀ x : Real, X ≤ x → HasDerivAt u (v x) x)
    (hdrop : ∀ (fs : List (Real → Real)) (c : Real → Real), Pr (fs ++ [c]) → Pr fs)
    (hPrd : ∀ (ds₀ : List (Real → Real)) (dtop : Real → Real),
      gdrel v (expCoeffs S Cs) (expCoeffsD S S' Cs) = ds₀ ++ [dtop] →
        Pr (gscaleSub (fun x => bipev Cd x (exp (S x))) dtop (expCoeffs S Cs₀) ds₀))
    (hmin : ∀ ns : List (Real → Real), Pr ns → GProperRel u ns →
      (expCoeffs S Cs).length ≤ ns.length)
    (hrel : GEvRel u (expCoeffs S Cs))
    (hCs : Cs = Cs₀ ++ [Cd]) (hlen0 : Cs₀.length = m + 1)
    (hCd1 : Cs₀[m]? = some Cd1) :
    EvZeroF (fun x =>
      bipev Cd x (exp (S x)) *
          (dbipevExp Cd1 S (S' x) x
            + v x * (natMul (m + 1) 1 * bipev Cd x (exp (S x))))
        - dbipevExp Cd S (S' x) x * bipev Cd1 x (exp (S x))) := by
  obtain ⟨X, hX, hS'⟩ := hS
  refine minimal_grel_identity_in (es := expCoeffsD S S' Cs) hu
    ⟨X, hX, fun x hx => gDerivAt_expCoeffs (hS' x hx) Cs⟩ hdrop hPrd hmin hrel
    (by rw [hCs, expCoeffs_concat]) (by rw [hCs, expCoeffsD_concat])
    (by rw [expCoeffs]; simpa using hlen0) (by rw [expCoeffsD]; simpa using hlen0)
    (by rw [expCoeffs, List.getElem?_map, hCd1]; rfl)
    (by rw [expCoeffsD, List.getElem?_map, hCd1]; rfl)

/-- **`minimal_expRel_identity` is the `Pr := True` instance.** -/
theorem minimal_expRel_identity_unrestricted {S S' u v : Real → Real}
    {Cs Cs₀ : List (List (List Real))} {Cd Cd1 : List (List Real)} {m : Nat}
    (hS : ∃ X : Real, 1 ≤ X ∧ ∀ x : Real, X ≤ x → HasDerivAt S (S' x) x)
    (hu : ∃ X : Real, 1 ≤ X ∧ ∀ x : Real, X ≤ x → HasDerivAt u (v x) x)
    (hmin : ∀ ns : List (Real → Real), GProperRel u ns →
      (expCoeffs S Cs).length ≤ ns.length)
    (hrel : GEvRel u (expCoeffs S Cs))
    (hCs : Cs = Cs₀ ++ [Cd]) (hlen0 : Cs₀.length = m + 1)
    (hCd1 : Cs₀[m]? = some Cd1) :
    EvZeroF (fun x =>
      bipev Cd x (exp (S x)) *
          (dbipevExp Cd1 S (S' x) x
            + v x * (natMul (m + 1) 1 * bipev Cd x (exp (S x))))
        - dbipevExp Cd S (S' x) x * bipev Cd1 x (exp (S x))) :=
  minimal_expRel_identity_in (Pr := fun _ => True) hS hu (fun _ _ _ => trivial)
    (fun _ _ _ => trivial) (fun ns _ hp => hmin ns hp) hrel hCs hlen0 hCd1

end MachLib
