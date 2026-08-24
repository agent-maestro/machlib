import MachLib.GermClearedStep
import MachLib.BipevClearedDeriv

/-!
# The differentiated relation clears, by one polynomial denominator

`GermClearedStep` discharged the consumer side of `hPrd`: given that the differentiated relation
clears by a single `pev G`, the `gscaleSub` output clears by the same `pev G`. This module is the
producer — it proves the antecedent.

```
gdrel v cs es  =  gadd es (gscale v (gyd cs))
```

with `cs = expCoeffs S Cs` and `es = expCoeffsD S S' Cs`. Two sources of denominator, and they are
different:

* `es` carries `S'`. `BipevClearedDeriv.bipev_cleared_deriv_zero` already clears it by `Q²`, with
  numerators `dcoeffs`.
* `gscale v (gyd cs)` carries `v = (log ∘ S)'`. `RatLogDeriv.ratLogDeriv_cleared` clears *that* by
  `P·Q²`, with numerator `Q·(P'Q − PQ')`.

**One denominator covers both**, because `Q²` divides `P·Q²`. That is why the statements below are
shaped as `pmul W QQ`: the `v`-side fixes the denominator, and the `S'`-side is cleared by a factor
of it, the surplus `W` being absorbed into the numerator by `biscale`. No least common multiple has
to be computed, and no denominator is multiplied by another anywhere in the descent.

## Syntactic mirrors

`gadd`, `gyd` and `gscale` act on germ lists; their numerators need counterparts one level up, on
`List (List (List Real))`. `cadd` and `cyd` are those, defined to mirror the recursions *pattern for
pattern* — including `gadd`'s asymmetric off-length cases — so no length hypothesis is needed
anywhere below.

The mirrors do **not** commute with `expCoeffs` on the nose: `gadd` produces
`fun x => bipev A x E + bipev B x E` where `cadd` produces `fun x => bipev (biadd A B) x E`, and
those are equal pointwise, not definitionally. Every statement here is therefore up to `GEvEq`,
which is what the class is stated with anyway.
-/

namespace MachLib

open Real

/-! ## `GEvEq` is an equivalence, and respects `gscale` -/

theorem evEqF_trans {a b c : Real → Real} (h₁ : EvEqF a b) (h₂ : EvEqF b c) : EvEqF a c := by
  obtain ⟨X₁, hX₁, e₁⟩ := h₁
  obtain ⟨X₂, hX₂, e₂⟩ := h₂
  obtain ⟨X, hX, hle1, hle2⟩ := two_bounds' hX₁ hX₂
  exact ⟨X, hX, fun x hx => by rw [e₁ x (le_trans hle1 hx)]; exact e₂ x (le_trans hle2 hx)⟩

theorem gEvEq_refl : ∀ as : List (Real → Real), GEvEq as as := by
  intro as
  induction as with
  | nil => trivial
  | cons a as ih => exact ⟨⟨1, le_refl 1, fun _ _ => rfl⟩, ih⟩

theorem gEvEq_trans : ∀ as bs cs : List (Real → Real), GEvEq as bs → GEvEq bs cs → GEvEq as cs := by
  intro as
  induction as with
  | nil =>
      intro bs cs h₁ h₂
      cases bs with
      | nil => exact h₂
      | cons _ _ => exact absurd h₁ (by intro hh; cases hh)
  | cons a as ih =>
      intro bs cs h₁ h₂
      cases bs with
      | nil => exact absurd h₁ (by intro hh; cases hh)
      | cons b bs =>
          cases cs with
          | nil => exact absurd h₂ (by intro hh; cases hh)
          | cons c cs => exact ⟨evEqF_trans h₁.1 h₂.1, ih bs cs h₁.2 h₂.2⟩

theorem gEvEq_gscale_congr (D : Real → Real) :
    ∀ as bs : List (Real → Real), GEvEq as bs → GEvEq (gscale D as) (gscale D bs) := by
  intro as
  induction as with
  | nil =>
      intro bs h
      cases bs with
      | nil => trivial
      | cons _ _ => exact absurd h (by intro hh; cases hh)
  | cons a as ih =>
      intro bs h
      cases bs with
      | nil => exact absurd h (by intro hh; cases hh)
      | cons b bs =>
          refine ⟨?_, ih bs h.2⟩
          obtain ⟨X, hX, e⟩ := h.1
          exact ⟨X, hX, fun x hx => by show D x * a x = D x * b x; rw [e x hx]⟩

/-! ## The syntactic mirrors -/

/-- `gadd`, one level up. Mirrors the asymmetric off-length cases exactly. -/
noncomputable def cadd :
    List (List (List Real)) → List (List (List Real)) → List (List (List Real))
  | [],      M       => M
  | A :: As, []      => A :: As
  | A :: As, B :: Bs => biadd A B :: cadd As Bs

/-- `gyd`, one level up. The trailing zero is the empty bipoly, and `bipev [] = 0`. -/
noncomputable def cyd : List (List (List Real)) → List (List (List Real))
  | []      => []
  | _ :: Cs => cadd Cs ([] :: cyd Cs)

theorem gEvEq_gadd {S : Real → Real} :
    ∀ (as bs : List (Real → Real)) (A B : List (List (List Real))),
      GEvEq as (expCoeffs S A) → GEvEq bs (expCoeffs S B) →
        GEvEq (gadd as bs) (expCoeffs S (cadd A B)) := by
  intro as
  induction as with
  | nil =>
      intro bs A B h₁ h₂
      cases A with
      | nil => exact h₂
      | cons _ _ => exact absurd h₁ (by intro hh; cases hh)
  | cons a as ih =>
      intro bs A B h₁ h₂
      cases A with
      | nil => exact absurd h₁ (by intro hh; cases hh)
      | cons C A =>
          cases bs with
          | nil =>
              cases B with
              | nil => exact h₁
              | cons _ _ => exact absurd h₂ (by intro hh; cases hh)
          | cons b bs =>
              cases B with
              | nil => exact absurd h₂ (by intro hh; cases hh)
              | cons Dd B =>
                  refine ⟨?_, ih bs A B h₁.2 h₂.2⟩
                  obtain ⟨X₁, hX₁, e₁⟩ := h₁.1
                  obtain ⟨X₂, hX₂, e₂⟩ := h₂.1
                  obtain ⟨X, hX, hle1, hle2⟩ := two_bounds' hX₁ hX₂
                  refine ⟨X, hX, fun x hx => ?_⟩
                  have e1' : a x = bipev C x (exp (S x)) := e₁ x (le_trans hle1 hx)
                  have e2' : b x = bipev Dd x (exp (S x)) := e₂ x (le_trans hle2 hx)
                  show a x + b x = bipev (biadd C Dd) x (exp (S x))
                  rw [bipev_biadd, e1', e2']

/-- **`gyd` of an `expCoeffs` image is one, up to `GEvEq`.** -/
theorem gEvEq_gyd {S : Real → Real} :
    ∀ Cs : List (List (List Real)), GEvEq (gyd (expCoeffs S Cs)) (expCoeffs S (cyd Cs)) := by
  intro Cs
  induction Cs with
  | nil => trivial
  | cons C Cs ih =>
      show GEvEq (gadd (expCoeffs S Cs) ((fun _ => (0 : Real)) :: gyd (expCoeffs S Cs)))
        (expCoeffs S (cadd Cs ([] :: cyd Cs)))
      refine gEvEq_gadd (expCoeffs S Cs) _ Cs ([] :: cyd Cs) (gEvEq_refl _) ?_
      exact ⟨⟨1, le_refl 1, fun _ _ => rfl⟩, ih⟩

/-- `gscale` distributes over `gadd`, pointwise. -/
theorem gEvEq_gscale_gadd (D : Real → Real) :
    ∀ as bs : List (Real → Real),
      GEvEq (gscale D (gadd as bs)) (gadd (gscale D as) (gscale D bs)) := by
  intro as
  induction as with
  | nil => intro bs; exact gEvEq_refl _
  | cons a as ih =>
      intro bs
      cases bs with
      | nil => exact gEvEq_refl _
      | cons b bs =>
          refine ⟨?_, ih bs⟩
          refine ⟨1, le_refl 1, fun x _ => ?_⟩
          show D x * (a x + b x) = D x * a x + D x * b x
          mach_ring

/-! ## The two sources, each cleared -/

/-- **The `v` side.** `v` clears by `pev G` with numerator `Nv`, so `gscale v` of an `expCoeffs`
image clears by the same `pev G`, with numerators scaled by `Nv`. -/
theorem gEvEq_gscale_v {S v : Real → Real} {G Nv : List Real}
    (hv : EvEqF (fun x => v x * pev G x) (fun x => pev Nv x)) :
    ∀ Y : List (List (List Real)),
      GEvEq (gscale (pev G) (gscale v (expCoeffs S Y)))
            (expCoeffs S (Y.map (biscale Nv))) := by
  intro Y
  induction Y with
  | nil => trivial
  | cons C Y ih =>
      refine ⟨?_, ih⟩
      obtain ⟨X, hX, e⟩ := hv
      refine ⟨X, hX, fun x hx => ?_⟩
      have hvx : v x * pev G x = pev Nv x := e x hx
      show pev G x * (v x * bipev C x (exp (S x))) = bipev (biscale Nv C) x (exp (S x))
      rw [bipev_biscale, ← hvx]
      mach_mpoly [pev G x, v x, bipev C x (exp (S x))]

/-- **The `S'` side.** `dbipevExp` clears by `pev QQ`; the surplus factor `W` of the common
denominator is absorbed into the numerator by `biscale`. -/
theorem gEvEq_gscale_expCoeffsD {S S' : Real → Real} {W QQ Dn : List Real}
    (hS' : ∃ X : Real, 1 ≤ X ∧ ∀ x : Real, X ≤ x → S' x * pev QQ x = pev Dn x) :
    ∀ Cs : List (List (List Real)),
      GEvEq (gscale (pev (pmul W QQ)) (expCoeffsD S S' Cs))
            (expCoeffs S (Cs.map (fun C => biscale W (dcoeffs QQ Dn 0 C)))) := by
  intro Cs
  induction Cs with
  | nil => trivial
  | cons C Cs ih =>
      refine ⟨?_, ih⟩
      obtain ⟨X, hX, e⟩ := hS'
      refine ⟨X, hX, fun x hx => ?_⟩
      have hcl : pev QQ x * dbipevExp C S (S' x) x
          = bipev (dcoeffs QQ Dn 0 C) x (exp (S x)) :=
        bipev_cleared_deriv_zero C QQ Dn S (S' x) x (e x hx)
      show pev (pmul W QQ) x * dbipevExp C S (S' x) x
          = bipev (biscale W (dcoeffs QQ Dn 0 C)) x (exp (S x))
      rw [bipev_biscale, ← hcl, pev_pmul]
      mach_ring

/-! ## The differentiated relation -/

/-- **`gdrel` clears, by one polynomial denominator.** -/
theorem gEvEq_gscale_gdrel {S S' v : Real → Real} {W QQ Dn Nv : List Real}
    (hS' : ∃ X : Real, 1 ≤ X ∧ ∀ x : Real, X ≤ x → S' x * pev QQ x = pev Dn x)
    (hv : EvEqF (fun x => v x * pev (pmul W QQ) x) (fun x => pev Nv x))
    (Cs : List (List (List Real))) :
    GEvEq (gscale (pev (pmul W QQ)) (gdrel v (expCoeffs S Cs) (expCoeffsD S S' Cs)))
          (expCoeffs S (cadd (Cs.map (fun C => biscale W (dcoeffs QQ Dn 0 C)))
                             ((cyd Cs).map (biscale Nv)))) := by
  have hpart2 : GEvEq (gscale (pev (pmul W QQ)) (gscale v (gyd (expCoeffs S Cs))))
      (expCoeffs S ((cyd Cs).map (biscale Nv))) :=
    gEvEq_trans _ _ _
      (gEvEq_gscale_congr (pev (pmul W QQ)) _ _
        (gEvEq_gscale_congr v _ _ (gEvEq_gyd Cs)))
      (gEvEq_gscale_v hv (cyd Cs))
  refine gEvEq_trans _ _ _
    (gEvEq_gscale_gadd (pev (pmul W QQ)) (expCoeffsD S S' Cs) (gscale v (gyd (expCoeffs S Cs))))
    ?_
  exact gEvEq_gadd _ _ _ _ (gEvEq_gscale_expCoeffsD hS' Cs) hpart2

/-! ## Splitting at the top, and the obligation -/

private theorem expCoeffs_split_last {S : Real → Real} {Cs : List (List (List Real))}
    {ds₀ : List (Real → Real)} {d : Real → Real} (h : expCoeffs S Cs = ds₀ ++ [d]) :
    ∃ (Cs₀ : List (List (List Real))) (Cd : List (List Real)),
      ds₀ = expCoeffs S Cs₀ ∧ d = fun x => bipev Cd x (exp (S x)) := by
  have hne : Cs ≠ [] := by
    intro hz
    rw [hz] at h
    simp [expCoeffs] at h
  refine ⟨Cs.dropLast, Cs.getLast hne, ?_, ?_⟩
  · have hsplit : Cs = Cs.dropLast ++ [Cs.getLast hne] := (List.dropLast_concat_getLast hne).symm
    rw [hsplit, expCoeffs_concat] at h
    have hd : (expCoeffs S Cs.dropLast
        ++ [fun x => bipev (Cs.getLast hne) x (exp (S x))]).dropLast = (ds₀ ++ [d]).dropLast := by
      rw [h]
    rw [List.dropLast_concat, List.dropLast_concat] at hd
    exact hd.symm
  · have hsplit : Cs = Cs.dropLast ++ [Cs.getLast hne] := (List.dropLast_concat_getLast hne).symm
    rw [hsplit, expCoeffs_concat] at h
    have hd : (expCoeffs S Cs.dropLast
        ++ [fun x => bipev (Cs.getLast hne) x (exp (S x))]).getLastD (fun _ => 0)
        = (ds₀ ++ [d]).getLastD (fun _ => 0) := by rw [h]
    rw [List.getLastD_concat, List.getLastD_concat] at hd
    exact hd.symm

/-- **`hPrd`, discharged for `ClearsToExp`.** Every hypothesis is a clearing fact about `S'` or `v`;
none is about the relation. -/
theorem clearsToExp_hPrd {S S' v : Real → Real} {W QQ Dn Nv : List Real}
    {Cs Cs₀ : List (List (List Real))} {Cd : List (List Real)}
    (hG : ¬ EvZeroF (pev (pmul W QQ)))
    (hS' : ∃ X : Real, 1 ≤ X ∧ ∀ x : Real, X ≤ x → S' x * pev QQ x = pev Dn x)
    (hv : EvEqF (fun x => v x * pev (pmul W QQ) x) (fun x => pev Nv x)) :
    ∀ (ds₀ : List (Real → Real)) (dtop : Real → Real),
      gdrel v (expCoeffs S Cs) (expCoeffsD S S' Cs) = ds₀ ++ [dtop] →
        ClearsToExp S
          (gscaleSub (fun x => bipev Cd x (exp (S x))) dtop (expCoeffs S Cs₀) ds₀) := by
  intro ds₀ dtop hsplit
  have hall := gEvEq_gscale_gdrel (S := S) hS' hv Cs
  rw [hsplit, gscale_concat] at hall
  obtain ⟨ns₀, ntop, hns, hEq, htop⟩ :=
    gEvEq_concat_right (gscale (pev (pmul W QQ)) ds₀) (fun x => pev (pmul W QQ) x * dtop x) _ hall
  obtain ⟨Ns₀, Ntop, hNs, hNtop⟩ := expCoeffs_split_last hns
  refine clearsToExp_gscaleSub (A := Cd) (Bt := Ntop) (Cs := Cs₀) (Ds := Ns₀) hG ?_ ?_
  · exact hNtop ▸ htop
  · exact hNs ▸ hEq

/-! ## The identity, with the class instantiated

An abstraction that is never instantiated is not known to be the *useful* one — a green build says
`True`, not "the one you need". This is the instantiation, and it is the receipt that the three
obligations `ClassMinimality` named are all dischargeable by one class at once.

What a caller now supplies is **three clearing facts and no closure obligations**: the denominator is
not eventually zero, `S'` clears by `QQ`, and `v` clears by `W·QQ`. `hdrop` and `hPrd` are gone. -/

/-- **`minimal_expRel_identity_in`, at `Pr := ClearsToExp S`.** -/
theorem minimal_expRel_identity_cleared {S S' u v : Real → Real} {W QQ Dn Nv : List Real}
    {Cs Cs₀ : List (List (List Real))} {Cd Cd1 : List (List Real)} {m : Nat}
    (hS : ∃ X : Real, 1 ≤ X ∧ ∀ x : Real, X ≤ x → HasDerivAt S (S' x) x)
    (hu : ∃ X : Real, 1 ≤ X ∧ ∀ x : Real, X ≤ x → HasDerivAt u (v x) x)
    (hG : ¬ EvZeroF (pev (pmul W QQ)))
    (hS'c : ∃ X : Real, 1 ≤ X ∧ ∀ x : Real, X ≤ x → S' x * pev QQ x = pev Dn x)
    (hvc : EvEqF (fun x => v x * pev (pmul W QQ) x) (fun x => pev Nv x))
    (hmin : ∀ ns : List (Real → Real), ClearsToExp S ns → GProperRel u ns →
      (expCoeffs S Cs).length ≤ ns.length)
    (hrel : GEvRel u (expCoeffs S Cs))
    (hCs : Cs = Cs₀ ++ [Cd]) (hlen0 : Cs₀.length = m + 1)
    (hCd1 : Cs₀[m]? = some Cd1) :
    EvZeroF (fun x =>
      bipev Cd x (exp (S x)) *
          (dbipevExp Cd1 S (S' x) x
            + v x * (natMul (m + 1) 1 * bipev Cd x (exp (S x))))
        - dbipevExp Cd S (S' x) x * bipev Cd1 x (exp (S x))) :=
  minimal_expRel_identity_in (Pr := ClearsToExp S) hS hu
    (fun _ _ h => clearsToExp_dropLast h) (clearsToExp_hPrd hG hS'c hvc)
    hmin hrel hCs hlen0 hCd1

end MachLib
