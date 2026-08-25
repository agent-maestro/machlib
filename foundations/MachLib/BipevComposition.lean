import MachLib.BipevElimLink
import MachLib.BipevCoeffIdentity
import MachLib.PolyPoleCount
import MachLib.PolyConstDvd
import MachLib.PolyEvZero

/-!
# The composition

Every link of `CRUX.md`'s argument now exists as a theorem. This module threads them, and adds
nothing mathematical beyond one nonvanishing fact about `Real`.

The chain, in the order it runs:

1. **`evRel_dcoeffs_ratFn`** — the relation holds on a tail ⟹ the *cleared differentiated* relation
   holds on a tail. (`BipevTailNonzero`.)
2. **`elim_coeff_vanishes`** — a minimal relation, differentiated and eliminated against its own
   leading coefficient, has every lower coefficient eventually zero. (`BipevElimLink`.)
3. **`pnorm_eq_nil_of_evZero`** — eventually zero as a *function* ⟹ zero as a *polynomial*.
   (`PolyEvZero`. This is where ℝ's infinitude enters, and why that module is deliberately outside
   `algebraSpineModules`.)
4. **`coeff_identity`** — the vanishing coefficient, rearranged into the count's identity
   `(u'v − uv')·Q² ≈ (m−j)·D·(uv)`. (`BipevCoeffIdentity`.)
5. **`cleared_relation_impossible`** — the pole-order count. (`PolyPoleCount`.)

## What the composition still needs, and where it comes from

`cleared_relation_impossible` asks for `q`-adic factorisations of the two coefficients `u` and `v`.
Neither is given; both come from `exists_ord_factor`, whose only hypothesis is that the polynomial is
nonzero. For `v` that is `ProperRel`'s second clause read through `pev_pnorm`; for `u` it is a
hypothesis of this theorem, discharged separately.

It also asks that `q` not divide the multiplier `Nc = (m − j)·1`. That is the **second and last**
characteristic-zero input of the arc, and unlike `DerivCoprime` it is not a hypothesis: over `Real`
it is a theorem, because `n·1 > 0` for `n ≥ 1`. `pnsum_one_ne_zero` below proves it from
`zero_lt_one_ax` and `add_lt_add_left` and nothing else.

That import of the order relation is why this module, like `PolyEvZero`, stays out of the algebra
spine. The spine proper never learns that `Real` is ordered.
-/

namespace MachLib

open Real

-- the zero test inside `pconsN` is classical, exactly as in `PolyCanonical`
attribute [local instance] Classical.propDecidable

/-! ## The constant `n·1` is nonzero

`pnsum n [1]` is the polynomial `n·1`. It is a single coefficient (`pnsum_one_length`), and over an
ordered field that coefficient is positive, hence nonzero, hence undivided by any irreducible.

Over `𝔽₂` with `n = 2` it is zero — the same boundary that `DerivCoprime` sits on, reached by a
different route. -/

/-- `n·1` is a positive single coefficient for every `n ≥ 1`. -/
theorem pnsum_one_pos : ∀ n : Nat, ∃ c : Real, 0 < c ∧ pnsum (n + 1) [(1 : Real)] = [c] := by
  intro n
  induction n with
  | zero =>
      refine ⟨1, zero_lt_one_ax, ?_⟩
      show padd [(1 : Real)] (pnsum 0 [(1 : Real)]) = [(1 : Real)]
      show padd [(1 : Real)] ([] : List Real) = [(1 : Real)]
      rw [padd_nil_right]
  | succ k ih =>
      obtain ⟨c, hc, hk⟩ := ih
      refine ⟨1 + c, ?_, ?_⟩
      · -- `0 < 1 = 1 + 0 < 1 + c`
        have h1 : (1 : Real) + 0 < 1 + c := add_lt_add_left hc 1
        rw [add_zero] at h1
        exact lt_trans_ax zero_lt_one_ax h1
      · show padd [(1 : Real)] (pnsum (k + 1) [(1 : Real)]) = [1 + c]
        rw [hk]
        show ((1 : Real) + c) :: padd ([] : List Real) [] = [1 + c]
        rfl

/-- **`q ∤ n·1` for `n ≥ 1`.** The arc's second characteristic-zero input, and a theorem rather than
a hypothesis because `Real` is ordered. -/
theorem not_Pdvd_pnsum_one' {q : List Real} (hq : PIrred q) {n : Nat} (hn : n ≠ 0) :
    ¬ Pdvd q (pnsum n [(1 : Real)]) := by
  obtain ⟨m, hm⟩ : ∃ m : Nat, n = m + 1 := ⟨n - 1, by omega⟩
  subst hm
  obtain ⟨c, hc, he⟩ := pnsum_one_pos m
  refine not_Pdvd_pnsum_one hq ?_
  rw [he]
  show pconsN c (pnorm ([] : List Real)) ≠ []
  show (if c = 0 then [] else [c]) ≠ []
  rw [if_neg (ne_of_gt hc)]
  exact fun h => by cases h

/-! ## Nonzero as a function, nonzero as a polynomial -/

/-- The contrapositive of `pnorm_eq_nil_of_evZero`, in the direction `ProperRel` supplies. -/
theorem pnorm_ne_nil_of_not_evZero {L : List Real} (h : ¬ EvZeroF (pev L)) : pnorm L ≠ [] := by
  intro hz
  refine h ⟨1, le_refl 1, fun x _ => ?_⟩
  rw [← pev_pnorm L x, hz]
  rfl

/-! ## The composition

Stated for a *minimal* relation together with a nonzero coefficient below the top. Both the
minimality and the nonzero lower coefficient are consumed, not produced: minimality by the descent,
the nonzero coefficient by the factorisation. -/

/-- **A minimal proper relation with a nonzero lower coefficient is impossible.** The whole of
`CRUX.md`, composed. -/
theorem minimal_relation_impossible {P Q q : List Real}
    (hq : PIrred q)
    (hchar : ∀ r : Nat, DerivCoprime q (r + 1))
    (hPd : ¬ Pdvd q P) (hPn : PNormal P)
    (hQn : PNormal Q) (hQne : Q ≠ []) (hQd : Pdvd q Q)
    (hQz : ¬ EvZeroF (pev Q))
    {Ms Ls₀ : List (List Real)} {v u : List Real} {j : Nat}
    (hmin : ∀ Ns : List (List Real),
      ProperRel (fun y => pev P y * (1 / pev Q y)) Ns → Ms.length ≤ Ns.length)
    (hrel : EvRel (fun y => pev P y * (1 / pev Q y)) Ms)
    (hMs : Ms = Ls₀ ++ [v]) (hvz : ¬ EvZeroF (pev v))
    (hu : Ls₀[j]? = some u) (huz : ¬ EvZeroF (pev u)) :
    False := by
  -- 1. the differentiated relation, cleared
  have hdiff := evRel_dcoeffs_ratFn hQz hrel
  -- 2. the j-th eliminated coefficient vanishes eventually
  have hvan := elim_coeff_vanishes hmin hMs hrel hdiff hu
  -- 3. eventually zero as a function is zero as a polynomial
  have hC := pnorm_eq_nil_of_evZero hvan
  rw [Nat.zero_add, Nat.zero_add] at hC
  -- 4. rearrange into the count's identity
  have hjlt : j < Ls₀.length := by
    by_cases h : j < Ls₀.length
    · exact h
    · rw [List.getElem?_eq_none (Nat.le_of_not_lt h)] at hu; cases hu
  have hident := coeff_identity (Nat.le_of_lt hjlt) hC
  -- 5. the q-adic factorisations the count consumes
  obtain ⟨k, ut, _, _, hutd, hufac⟩ :=
    exists_ord_factor (pnorm u).length q (pnorm u) hq (pnorm_normal u)
      (pnorm_ne_nil_of_not_evZero huz) (Nat.le_refl _)
  obtain ⟨l, vt, _, _, hvtd, hvfac⟩ :=
    exists_ord_factor (pnorm v).length q (pnorm v) hq (pnorm_normal v)
      (pnorm_ne_nil_of_not_evZero hvz) (Nat.le_refl _)
  have hu' : PEq u (pmul (ppow q k) ut) := PEq.trans (pnorm_idem u).symm hufac
  have hv' : PEq v (pmul (ppow q l) vt) := PEq.trans (pnorm_idem v).symm hvfac
  -- 6. the count
  exact cleared_relation_impossible hq hPd hPn hQn hQne hQd hchar
    hu' hutd hv' hvtd (not_Pdvd_pnsum_one' hq (by omega)) hident

end MachLib
