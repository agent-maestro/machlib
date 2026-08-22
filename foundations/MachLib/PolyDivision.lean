import MachLib.PolyCanonical

/-!
# Division with remainder — the theorem the PRS never supplied

`MultiVarPRS.prsLoop` is already the Euclidean loop in shape, but `reduceOnce` carries only
`reduceOnce_vanish`: *common zeros are preserved*. That is strictly weaker than what gcd, Bézout and
Euclid's lemma consume, all of which need the **identity** `A = B·Q + R`. This file supplies it, on
`List Real`, for an arbitrary nonzero divisor.

## Where the canonical invariant earns its keep

The step subtracts `c·xᵏ·B` from `A` with `c = α/β`, `α` and `β` the leading coefficients. If `β`
were allowed to be `0` — which an unnormalised list permits, since `[1, 0]` has a trailing zero —
then `c = α/0 = 0` under this corpus's totalised division and **the step would silently not
cancel**, the recursion would not descend, and the fuel would run out returning a wrong quotient.
`PNormal B` is exactly what forbids that. The invariant is not bookkeeping here; it is what makes
the algorithm correct.

## Why the cancellation is syntactic

Little-endian lists put the leading coefficient last, so the classical "cancel the top term"
argument would normally need `getLast?` reasoning about the difference. It does not, if the step is
written in concat form. With `A = A₀ ++ [α]` and `B = B₀ ++ [β]`:

```
c·xᵏ·B  =  P ++ [c·β]           where  P = pshift k (pscale c B₀)
A − c·xᵏ·B  =  padd A₀ (−P) ++ [α − c·β]  =  D ++ [0]
```

because `c·β = (α/β)·β = α`. The zero is *there in the list*, not merely a value the last
coefficient evaluates to — so `pnorm_concat_zero` applies and the length drops. That is the whole
descent, and it is why `padd_concat` / `pscale_concat` / `pshift_concat` are proved first: they are
what keep the step syntactic.

## What the canonical representation buys in the statement

The remainder condition is usually `R = 0 ∨ deg R < deg B`. Canonically it is just
`r.length < B.length` — the zero polynomial is `[]`, of length `0`, and `B ≠ []`, so the disjunction
collapses. One fewer case to carry through gcd and `ord_q`.
-/

namespace MachLib

open Real

attribute [local instance] Classical.propDecidable

/-! ## Shifting by a power of `x` -/

/-- `pshift k L` is `xᵏ · L`: `k` zero coefficients in front of a little-endian list. -/
noncomputable def pshift : Nat → List Real → List Real
  | 0,     L => L
  | k + 1, L => 0 :: pshift k L

theorem pshift_length : ∀ (k : Nat) (L : List Real), (pshift k L).length = k + L.length := by
  intro k
  induction k with
  | zero => intro L; show L.length = 0 + L.length; omega
  | succ n ih =>
      intro L
      show (pshift n L).length + 1 = n + 1 + L.length
      rw [ih L]; omega

theorem pev_pshift : ∀ (k : Nat) (L : List Real) (x : Real),
    pev (pshift k L) x = powNat x k * pev L x := by
  intro k
  induction k with
  | zero => intro L x; exact (one_mul_thm (pev L x)).symm
  | succ n ih =>
      intro L x
      show (0 : Real) + x * pev (pshift n L) x = (x * powNat x n) * pev L x
      rw [ih L x]; mach_ring

theorem pshift_concat : ∀ (k : Nat) (L : List Real) (w : Real),
    pshift k (L ++ [w]) = pshift k L ++ [w] := by
  intro k
  induction k with
  | zero => intro L w; rfl
  | succ n ih =>
      intro L w
      show (0 : Real) :: pshift n (L ++ [w]) = (0 : Real) :: pshift n L ++ [w]
      rw [ih L w]; rfl

/-! ## Concat forms of the coefficient operations

These are what keep the cancellation syntactic. Each is one induction and none mentions `getLast`. -/

theorem pscale_length : ∀ (c : Real) (L : List Real), (pscale c L).length = L.length := by
  intro c L
  induction L with
  | nil => rfl
  | cons a as ih => show (pscale c as).length + 1 = as.length + 1; rw [ih]

theorem pscale_concat : ∀ (c : Real) (L : List Real) (w : Real),
    pscale c (L ++ [w]) = pscale c L ++ [c * w] := by
  intro c L
  induction L with
  | nil => intro w; rfl
  | cons a as ih =>
      intro w
      show (c * a) :: pscale c (as ++ [w]) = (c * a) :: pscale c as ++ [c * w]
      rw [ih w]; rfl

theorem padd_length_eq : ∀ (L M : List Real), L.length = M.length →
    (padd L M).length = L.length := by
  intro L
  induction L with
  | nil => intro M h; cases M with
    | nil => rfl
    | cons b bs => exact absurd h.symm (by simp)
  | cons a as ih =>
      intro M h
      cases M with
      | nil => exact absurd h (by simp)
      | cons b bs =>
          show (padd as bs).length + 1 = as.length + 1
          rw [ih bs (by simpa using h)]

theorem padd_concat : ∀ (X Y : List Real), X.length = Y.length → ∀ u v : Real,
    padd (X ++ [u]) (Y ++ [v]) = padd X Y ++ [u + v] := by
  intro X
  induction X with
  | nil => intro Y h u v; cases Y with
    | nil => rfl
    | cons b bs => exact absurd h.symm (by simp)
  | cons a as ih =>
      intro Y h u v
      cases Y with
      | nil => exact absurd h (by simp)
      | cons b bs =>
          show (a + b) :: padd (as ++ [u]) (bs ++ [v]) = ((a + b) :: padd as bs) ++ [u + v]
          rw [ih bs (by simpa using h) u v]; rfl

/-! ## Normalisation facts the descent needs -/

theorem pnorm_length_le : ∀ L : List Real, (pnorm L).length ≤ L.length := by
  intro L
  induction L with
  | nil => exact Nat.le_refl 0
  | cons a as ih =>
      show (pconsN a (pnorm as)).length ≤ as.length + 1
      cases h : pnorm as with
      | nil =>
          by_cases ha : a = 0
          · show (if a = 0 then [] else [a]).length ≤ as.length + 1
            rw [if_pos ha]; exact Nat.zero_le _
          · show (if a = 0 then [] else [a]).length ≤ as.length + 1
            rw [if_neg ha]
            exact Nat.succ_le_succ (Nat.zero_le _)
      | cons d ds =>
          have hlen : (d :: ds).length ≤ as.length := by rw [← h]; exact ih
          show (a :: d :: ds).length ≤ as.length + 1
          exact Nat.succ_le_succ hlen

/-- **A trailing zero is invisible to `pnorm`.** The descent lemma: the step produces a list ending
in a literal `0`, so its normal form is that of the shorter list. -/
theorem pnorm_concat_zero : ∀ L : List Real, pnorm (L ++ [0]) = pnorm L := by
  intro L
  induction L with
  | nil => exact pnorm_nil_zero
  | cons a as ih =>
      show pconsN a (pnorm (as ++ [0])) = pconsN a (pnorm as)
      rw [ih]

/-- The length strictly drops once a trailing zero is normalised away. -/
theorem pnorm_concat_zero_length_lt (L : List Real) :
    (pnorm (L ++ [0])).length < (L ++ [0]).length := by
  rw [pnorm_concat_zero]
  have h1 : (pnorm L).length ≤ L.length := pnorm_length_le L
  have h2 : (L ++ [(0 : Real)]).length = L.length + 1 := by simp
  omega


/-! ## The step, and why its leading term cancels syntactically -/

/-- `a/b · b = a`, from `div_def` and `mul_inv` only. Proved locally rather than imported from
`DivisionError`, which carries the ordered-real base this module is gated against. -/
private theorem div_mul_cancel_field {a b : Real} (hb : b ≠ 0) : a / b * b = a := by
  rw [div_def a b hb, mul_assoc, mul_comm (1 / b) b, mul_inv b hb, mul_one_ax]

theorem getLastD_concat (L : List Real) (a d : Real) : (L ++ [a]).getLastD d = a := by
  simp

/-- **The cancellation, as a list identity.** Equal lengths and an equal final coefficient make the
difference end in a *literal* `0` — not merely a coefficient that evaluates to zero. -/
theorem psub_concat_self (X Y : List Real) (h : X.length = Y.length) (u : Real) :
    psub (X ++ [u]) (Y ++ [u]) = padd X (pscale (0 - 1) Y) ++ [0] := by
  show padd (X ++ [u]) (pscale (0 - 1) (Y ++ [u])) = padd X (pscale (0 - 1) Y) ++ [0]
  rw [pscale_concat]
  rw [padd_concat X (pscale (0 - 1) Y) (by rw [pscale_length]; exact h) u ((0 - 1) * u)]
  have hz : u + (0 - 1) * u = 0 := by mach_ring
  rw [hz]

/-- One long-division step: subtract `c·xᵏ·B` from `A` and renormalise. -/
noncomputable def pdivStep (A B : List Real) : List Real :=
  pnorm (psub A (pshift (A.length - B.length) (pscale (A.getLastD 0 / B.getLastD 0) B)))

/-- The quotient monomial one step contributes. -/
noncomputable def pdivMono (A B : List Real) : List Real :=
  pshift (A.length - B.length) [A.getLastD 0 / B.getLastD 0]

theorem pev_pdivMono (A B : List Real) (x : Real) :
    pev (pdivMono A B) x
      = powNat x (A.length - B.length) * (A.getLastD 0 / B.getLastD 0) := by
  show pev (pshift (A.length - B.length) [A.getLastD 0 / B.getLastD 0]) x = _
  rw [pev_pshift]
  have e : pev [A.getLastD 0 / B.getLastD 0] x = A.getLastD 0 / B.getLastD 0 := by
    show A.getLastD 0 / B.getLastD 0 + x * 0 = A.getLastD 0 / B.getLastD 0
    mach_ring
  rw [e]

theorem pev_pdivStep (A B : List Real) (x : Real) :
    pev (pdivStep A B) x
      = pev A x - powNat x (A.length - B.length) * ((A.getLastD 0 / B.getLastD 0) * pev B x) := by
  show pev (pnorm (psub A (pshift _ (pscale _ B)))) x = _
  rw [pev_pnorm, pev_psub, pev_pshift, pev_pscale]

/-- `pshift`+`pscale` in concat form: the leading coefficient survives both, scaled. -/
theorem pshift_pscale_concat (k : Nat) (c b : Real) (B0 : List Real) :
    pshift k (pscale c (B0 ++ [b])) = pshift k (pscale c B0) ++ [c * b] := by
  rw [pscale_concat, pshift_concat]

/-- **The descent.** One step strictly shortens the canonical list. This is where `PNormal B` is
load-bearing: it is what makes `β ≠ 0`, hence `c·β = α`, hence the cancellation. With `β = 0` the
totalised `α/0 = 0` would leave `A` unchanged and the recursion would not descend at all. -/
theorem pdivStep_length {A B : List Real} (hB : PNormal B) (hBne : B ≠ [])
    (hle : B.length ≤ A.length) : (pdivStep A B).length < A.length := by
  have hBlen : 1 ≤ B.length := by
    cases B with
    | nil => exact absurd rfl hBne
    | cons _ _ => exact Nat.succ_le_succ (Nat.zero_le _)
  have hAlen : 1 ≤ A.length := Nat.le_trans hBlen hle
  have hAne : A ≠ [] := by
    intro h; rw [h] at hAlen; simp at hAlen
  obtain ⟨A0, a, hA⟩ : ∃ A0 a, A = A0 ++ [a] :=
    ⟨A.dropLast, A.getLast hAne, (List.dropLast_concat_getLast hAne).symm⟩
  obtain ⟨B0, b, hBc⟩ : ∃ B0 b, B = B0 ++ [b] :=
    ⟨B.dropLast, B.getLast hBne, (List.dropLast_concat_getLast hBne).symm⟩
  have hbne : b ≠ 0 := hB b (by rw [hBc]; simp)
  have hgA : A.getLastD 0 = a := by rw [hA]; exact getLastD_concat A0 a 0
  have hgB : B.getLastD 0 = b := by rw [hBc]; exact getLastD_concat B0 b 0
  have hA0len : A0.length + 1 = A.length := by rw [hA]; simp
  have hB0len : B0.length + 1 = B.length := by rw [hBc]; simp
  have hcb : (a / b) * b = a := div_mul_cancel_field hbne
  show (pnorm (psub A (pshift (A.length - B.length)
      (pscale (A.getLastD 0 / B.getLastD 0) B)))).length < A.length
  rw [hgA, hgB]
  -- freeze the shift exponent so `B` survives only inside `pscale (a/b) B`
  have hklen : (A.length - B.length) + B0.length = A0.length := by omega
  generalize hk : A.length - B.length = k at hklen ⊢
  have hPlen : (pshift k (pscale (a / b) B0)).length = A0.length := by
    rw [pshift_length, pscale_length]; omega
  have hshift : pshift k (pscale (a / b) B) = pshift k (pscale (a / b) B0) ++ [a] := by
    rw [hBc, pshift_pscale_concat, hcb]
  have hstep : psub A (pshift k (pscale (a / b) B))
      = padd A0 (pscale (0 - 1) (pshift k (pscale (a / b) B0))) ++ [0] := by
    rw [hA, hshift]
    exact psub_concat_self A0 _ hPlen.symm a
  have hDlen : (padd A0 (pscale (0 - 1) (pshift k (pscale (a / b) B0)))).length = A0.length := by
    refine padd_length_eq A0 _ ?_
    rw [pscale_length, hPlen]
  rw [hstep]
  have hlt := pnorm_concat_zero_length_lt
    (padd A0 (pscale (0 - 1) (pshift k (pscale (a / b) B0))))
  have hcat : (padd A0 (pscale (0 - 1) (pshift k (pscale (a / b) B0))) ++ [(0 : Real)]).length
      = A0.length + 1 := by simp [hDlen]
  omega

/-! ## The algorithm, and the identity it satisfies -/

/-- Long division on a fuel budget. `pdivStep` strictly shortens `A`, so `fuel = A.length` is
always enough; the budget is a termination device, not an approximation. -/
noncomputable def pdivmod : Nat → List Real → List Real → List Real × List Real
  | 0,        A, _ => ([], A)
  | fuel + 1, A, B =>
      if A.length < B.length then ([], A)
      else (padd (pdivMono A B) (pdivmod fuel (pdivStep A B) B).1,
            (pdivmod fuel (pdivStep A B) B).2)

theorem pdivmod_zero (A B : List Real) : pdivmod 0 A B = ([], A) := rfl

theorem pdivmod_succ (fuel : Nat) (A B : List Real) :
    pdivmod (fuel + 1) A B =
      if A.length < B.length then ([], A)
      else (padd (pdivMono A B) (pdivmod fuel (pdivStep A B) B).1,
            (pdivmod fuel (pdivStep A B) B).2) := rfl

/-- **Division with remainder.** `A = B·Q + R` with `R` canonical and `deg R < deg B` — stated as
`R.length < B.length`, which by canonicity already covers `R = 0`.

This is the statement `MultiVarPRS` never proves: `reduceOnce_vanish` preserves *common zeros*,
which is enough for a resultant and not enough for gcd, Bézout or Euclid's lemma. -/
theorem pdivmod_spec : ∀ (fuel : Nat) (A B : List Real),
    PNormal A → PNormal B → B ≠ [] → A.length ≤ fuel →
      (∀ x : Real, pev A x
          = pev B x * pev (pdivmod fuel A B).1 x + pev (pdivmod fuel A B).2 x)
      ∧ PNormal (pdivmod fuel A B).2
      ∧ (pdivmod fuel A B).2.length < B.length := by
  intro fuel
  induction fuel with
  | zero =>
      intro A B hA _ hBne hlen
      have hBpos : 1 ≤ B.length := by
        cases B with
        | nil => exact absurd rfl hBne
        | cons _ _ => exact Nat.succ_le_succ (Nat.zero_le _)
      rw [pdivmod_zero]
      refine ⟨fun x => ?_, hA, by simp; omega⟩
      show pev A x = pev B x * pev ([] : List Real) x + pev A x
      show pev A x = pev B x * 0 + pev A x
      mach_ring
  | succ fuel ih =>
      intro A B hA hB hBne hlen
      have hBpos : 1 ≤ B.length := by
        cases B with
        | nil => exact absurd rfl hBne
        | cons _ _ => exact Nat.succ_le_succ (Nat.zero_le _)
      rw [pdivmod_succ]
      by_cases h : A.length < B.length
      · rw [if_pos h]
        refine ⟨fun x => ?_, hA, h⟩
        show pev A x = pev B x * pev ([] : List Real) x + pev A x
        show pev A x = pev B x * 0 + pev A x
        mach_ring
      · rw [if_neg h]
        have hle : B.length ≤ A.length := Nat.le_of_not_lt h
        have hdrop : (pdivStep A B).length < A.length := pdivStep_length hB hBne hle
        have hfuel : (pdivStep A B).length ≤ fuel := by omega
        obtain ⟨hev, hnr, hlr⟩ := ih (pdivStep A B) B (pnorm_normal _) hB hBne hfuel
        refine ⟨fun x => ?_, hnr, hlr⟩
        have hq := hev x
        rw [pev_pdivStep A B x] at hq
        show pev A x
            = pev B x * pev (padd (pdivMono A B) (pdivmod fuel (pdivStep A B) B).1) x
              + pev (pdivmod fuel (pdivStep A B) B).2 x
        rw [pev_padd, pev_pdivMono]
        -- `hq` says  A − xᵏ·(c·B) = B·q + r; turn it round and the goal is a ring identity
        have ha : pev A x
            = (pev B x * pev (pdivmod fuel (pdivStep A B) B).1 x
                + pev (pdivmod fuel (pdivStep A B) B).2 x)
              + powNat x (A.length - B.length)
                  * ((A.getLastD 0 / B.getLastD 0) * pev B x) := by
          rw [← hq]; mach_ring
        rw [ha]; mach_ring

/-- The budget-free form: `A.length` is always enough fuel. -/
theorem pdivmod_spec' (A B : List Real) (hA : PNormal A) (hB : PNormal B) (hBne : B ≠ []) :
    (∀ x : Real, pev A x
        = pev B x * pev (pdivmod A.length A B).1 x + pev (pdivmod A.length A B).2 x)
    ∧ PNormal (pdivmod A.length A B).2
    ∧ (pdivmod A.length A B).2.length < B.length :=
  pdivmod_spec A.length A B hA hB hBne (Nat.le_refl _)

/-! ## The public API, on canonical polynomials

The contract this module is meant to export is `PolyNF → PolyNF`, not a family of list lemmas. Note
what is and is not claimed: the **remainder** is canonical and length-bounded, while the *quotient*
is `padd (pdivMono …) …` and is correct only up to `pev` — `padd` can leave a trailing zero. `of`
normalises both, and `pev_pnorm` carries the identity across. -/

namespace PolyNF

/-- Division with remainder on canonical polynomials. -/
noncomputable def divMod (A B : PolyNF) : PolyNF × PolyNF :=
  (PolyNF.of (pdivmod A.coeffs.length A.coeffs B.coeffs).1,
   PolyNF.of (pdivmod A.coeffs.length A.coeffs B.coeffs).2)

/-- **`A = B·Q + R`, with `deg R < deg B`.** The remainder bound needs no `R = 0` disjunct: the zero
polynomial is `[]`, of length `0`, and `B` is nonzero. -/
theorem divMod_spec (A B : PolyNF) (hB : B.coeffs ≠ []) :
    (∀ x : Real, A.eval x = B.eval x * (A.divMod B).1.eval x + (A.divMod B).2.eval x)
    ∧ (A.divMod B).2.coeffs.length < B.coeffs.length := by
  obtain ⟨hev, hnr, hlr⟩ :=
    pdivmod_spec' A.coeffs B.coeffs A.normal B.normal hB
  constructor
  · intro x
    show pev A.coeffs x
        = pev B.coeffs x * pev (pnorm (pdivmod A.coeffs.length A.coeffs B.coeffs).1) x
          + pev (pnorm (pdivmod A.coeffs.length A.coeffs B.coeffs).2) x
    rw [pev_pnorm, pev_pnorm]
    exact hev x
  · show (pnorm (pdivmod A.coeffs.length A.coeffs B.coeffs).2).length < B.coeffs.length
    rw [pnorm_eq_self _ hnr]
    exact hlr

end PolyNF

/-! ## A worked specimen — computed, not instantiated

An instantiation of `pdivmod_spec` at concrete lists proves nothing the spec does not already
prove: it cannot fail unless the spec fails, so it convicts nothing. The specimen below instead
**computes**, and would break on an off-by-one in the shift exponent, on a leading term that failed
to cancel, or on a recursion that stopped a step early.

`x²` divided by `x`. Little-endian `A = [0, 0, 1]`, `B = [0, 1]`. One step takes `k = 1`,
`c = 1/1`, subtracts `x·x` and leaves `[0, 0, 0]`, which normalises to `[]` — so the remainder is
**exactly the zero polynomial**, not merely something short. -/

theorem pdivStep_specimen : pdivStep [(0 : Real), 0, 1] [(0 : Real), 1] = [] := by
  have hc : (1 : Real) / 1 * 1 = 1 := div_mul_cancel_field one_ne_zero
  have hlist : psub [(0 : Real), 0, 1] (pshift 1 (pscale ((1 : Real) / 1) [(0 : Real), 1]))
      = [(0 : Real), 0, 0] := by
    show [(0 : Real) + (0 - 1) * 0,
          (0 : Real) + (0 - 1) * ((1 / 1) * 0),
          (1 : Real) + (0 - 1) * ((1 / 1) * 1)] = [(0 : Real), 0, 0]
    have h1 : (0 : Real) + (0 - 1) * 0 = 0 := by mach_ring
    have h2 : (0 : Real) + (0 - 1) * (((1 : Real) / 1) * 0) = 0 := by mach_ring
    have h3 : (1 : Real) + (0 - 1) * (((1 : Real) / 1) * 1) = 0 := by rw [hc]; mach_ring
    rw [h1, h2, h3]
  have hz : pnorm [(0 : Real), 0, 0] = [] := by
    show pconsN (0 : Real) (pnorm [(0 : Real), 0]) = []
    rw [pnorm_specimen_all_zero]
    show (if (0 : Real) = 0 then [] else [(0 : Real)]) = []
    rw [if_pos rfl]
  show pnorm (psub [(0 : Real), 0, 1]
      (pshift ([(0 : Real), 0, 1].length - [(0 : Real), 1].length)
        (pscale ([(0 : Real), 0, 1].getLastD 0 / [(0 : Real), 1].getLastD 0) [(0 : Real), 1]))) = []
  show pnorm (psub [(0 : Real), 0, 1] (pshift 1 (pscale ((1 : Real) / 1) [(0 : Real), 1]))) = []
  rw [hlist, hz]

/-- **The remainder is exactly zero** — computed through the whole recursion. -/
theorem pdivmod_specimen_remainder_is_zero :
    (pdivmod 3 [(0 : Real), 0, 1] [(0 : Real), 1]).2 = [] := by
  have hne : ¬ ([(0 : Real), 0, 1].length < [(0 : Real), 1].length) := by simp
  rw [show (3 : Nat) = 2 + 1 from rfl, pdivmod_succ, if_neg hne, pdivStep_specimen]
  show (pdivmod 2 ([] : List Real) [(0 : Real), 1]).2 = []
  rw [show (2 : Nat) = 1 + 1 from rfl, pdivmod_succ, if_pos (by simp)]

/-- And the quotient really is `x`: `pev` of it is `x` for every `x`. -/
theorem pdivmod_specimen_quotient :
    ∀ x : Real, pev (pdivmod 3 [(0 : Real), 0, 1] [(0 : Real), 1]).1 x = x := by
  intro x
  have hne : ¬ ([(0 : Real), 0, 1].length < [(0 : Real), 1].length) := by simp
  rw [show (3 : Nat) = 2 + 1 from rfl, pdivmod_succ, if_neg hne, pdivStep_specimen]
  show pev (padd (pdivMono [(0 : Real), 0, 1] [(0 : Real), 1])
      (pdivmod 2 ([] : List Real) [(0 : Real), 1]).1) x = x
  rw [show (2 : Nat) = 1 + 1 from rfl, pdivmod_succ, if_pos (by simp)]
  show pev (padd (pdivMono [(0 : Real), 0, 1] [(0 : Real), 1]) []) x = x
  rw [pev_padd, pev_pdivMono]
  have hc : (1 : Real) / 1 * 1 = 1 := div_mul_cancel_field one_ne_zero
  show powNat x ([(0 : Real), 0, 1].length - [(0 : Real), 1].length)
      * ([(0 : Real), 0, 1].getLastD 0 / [(0 : Real), 1].getLastD 0) + pev ([] : List Real) x = x
  show powNat x 1 * ((1 : Real) / 1) + (0 : Real) = x
  show (x * powNat x 0) * ((1 : Real) / 1) + (0 : Real) = x
  show (x * 1) * ((1 : Real) / 1) + (0 : Real) = x
  have h1 : (1 : Real) / 1 = 1 := by
    have := hc; rw [mul_one_ax] at this; exact this
  rw [h1]; mach_ring

end MachLib
