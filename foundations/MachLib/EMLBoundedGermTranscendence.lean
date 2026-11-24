import MachLib.EMLFTranscendence
import MachLib.GermClearedDescent
import MachLib.GermClearedDrel
import MachLib.BipevGerm
import MachLib.BipevComposition
import MachLib.PolyLowestTerms
import MachLib.PolyDerivNonzero
import MachLib.PevSignGerm
import MachLib.PevLeading
import MachLib.PevSign
import MachLib.PolyEvZero

/-!
# `BoundedGermTranscendence`, discharged

`boundedGermTranscendence_holds : BoundedGermTranscendence`. A rational germ `S` that is bounded and
not eventually constant makes `F ∘ S = exp ∘ S + log ∘ S` satisfy no polynomial relation with
polynomial coefficients and a leading coefficient bounded below by `c·xᵏ`.

## The route: three cited refutations and one case split

1. **Lowest terms.** `exists_irred_not_dividing` reduces `P/Q` to `P'/Q'` and splits: either `Q'` is a
   constant, or some irreducible `q` divides `Q'` and not `P'`.
2. **`Q'` constant** is the only place boundedness is spent. `S` is then a polynomial on a ray, and
   `pev_evConst_of_bounded` makes a bounded polynomial eventually constant. That contradicts
   nonconstancy.
3. **A genuine pole `q`.** `ratGerm_eventual_sign` makes `S` eventually zero (which contradicts
   nonconstancy), eventually negative, or eventually positive.
   * **Negative.** Totalisation gives `log (S x) = 0`, so `F (S x) = exp (S x)`. The obligation's
     relation is then `ProperRel S (Ls ++ [A])`, which `germ_relation_impossible` refutes.
   * **Positive.** Write `E = exp ∘ S` and `L = log ∘ S`. `expand_shift` re-expands
     `Σ pₖ(x)·(E + L)ᵏ` as `Σⱼ cⱼ(x, E)·Lʲ`, and the top `L`-coefficient is `pev A` unchanged. That is
     a `GProperRel` for `log ∘ (P'/Q')` whose coefficients are an `expCoeffs` image, so
     `clearsToExp_expCoeffs` places it in the class with denominator `1`.
     `no_proper_cleared_relation` refutes it.

Both pole theorems take `∀ r, DerivCoprime q (r + 1)`, which is `derivCoprime_of_irred`. The positive
one also takes `∀ r, ¬ Pdvd q (pnsum (r + 1) [1])`, which is `not_Pdvd_pnsum_one'`. Neither is
assumed here.

## What is new in this file

* `expand_shift`: the binomial re-expansion, as an existence statement over `tripev`, a Horner form
  in `L` whose coefficients are `bipev` lists in `E`. It is built on `cadd` from `GermClearedDrel`.
  It never computes a binomial coefficient: Horner in `y = E + L` needs only
  `(E + L)·G = E·G + L·G`, which is `map ([] :: ·)` plus a cons of `[]`.
* `pev_evConst_of_bounded`: peel off the constant term. A tail that is not eventually zero has a
  floor `c > 0` (`pev_leading_form`), so `|x·tail| ≥ c·x` grows past the bound at one explicit `x`.
* Small transfers: `pev_evNonvanish`, `not_evZeroF_of_evDom`, `div_eq_of_cross`.

## Cheapest counter-cases, read against each step (by reading the proof, not by a specimen)

* **Constant `S`.** Excluded by the nonconstancy hypothesis, which `constant_germ_is_algebraic` shows
  cannot be dropped. The proof uses it three times: `P = 0`, the `Q'`-constant branch, and the
  eventually-zero sign.
* **Bounded but polynomial.** Only constants qualify, and that is the `Q'`-constant branch.
* **`S → 0` from either side**, for example `±1/x`. There is still a pole (`q = x`), so the sign
  split covers it. The decay rate is never used.
* **`S` changing sign infinitely often.** Impossible for a rational germ: `ratGerm_eventual_sign`.
-/

namespace MachLib

open Real

/-! ## The binomial re-expansion -/

/-- `Σⱼ bipev Cⱼ x E · Lʲ`: a polynomial in `L` whose coefficients are polynomials in `x` and `E`. -/
noncomputable def tripev : List (List (List Real)) → Real → Real → Real → Real
  | [], _, _, _ => 0
  | C :: Cs, x, E, L => bipev C x E + L * tripev Cs x E L

/-- An `expCoeffs` relation, evaluated at `u`, is `tripev` at `E = exp ∘ S`. -/
theorem gbipev_expCoeffs_tripev (S : Real → Real) :
    ∀ (Cs : List (List (List Real))) (x u : Real),
      gbipev (expCoeffs S Cs) x u = tripev Cs x (exp (S x)) u := by
  intro Cs
  induction Cs with
  | nil => intro x u; rfl
  | cons C Cs ih =>
      intro x u
      show bipev C x (exp (S x)) + u * gbipev (expCoeffs S Cs) x u
          = bipev C x (exp (S x)) + u * tripev Cs x (exp (S x)) u
      rw [ih x u]

theorem tripev_cadd : ∀ (A B : List (List (List Real))) (x E L : Real),
    tripev (cadd A B) x E L = tripev A x E L + tripev B x E L := by
  intro A
  induction A with
  | nil => intro B x E L; show tripev B x E L = 0 + tripev B x E L; mach_ring
  | cons C Cs ih =>
      intro B x E L
      cases B with
      | nil => show tripev (C :: Cs) x E L = tripev (C :: Cs) x E L + 0; mach_ring
      | cons D Ds =>
          show bipev (biadd C D) x E + L * tripev (cadd Cs Ds) x E L
              = (bipev C x E + L * tripev Cs x E L) + (bipev D x E + L * tripev Ds x E L)
          rw [bipev_biadd, ih Ds x E L]
          mach_mpoly [bipev C x E, bipev D x E, L, tripev Cs x E L, tripev Ds x E L]

theorem tripev_shift : ∀ (Cs : List (List (List Real))) (x E L : Real),
    tripev (Cs.map (fun C => [] :: C)) x E L = E * tripev Cs x E L := by
  intro Cs
  induction Cs with
  | nil => intro x E L; show (0 : Real) = E * 0; mach_ring
  | cons C Cs ih =>
      intro x E L
      show (pev [] x + E * bipev C x E) + L * tripev (Cs.map (fun C => [] :: C)) x E L
          = E * (bipev C x E + L * tripev Cs x E L)
      rw [ih x E L]
      show ((0 : Real) + E * bipev C x E) + L * (E * tripev Cs x E L)
          = E * (bipev C x E + L * tripev Cs x E L)
      mach_mpoly [E, L, bipev C x E, tripev Cs x E L]

theorem cadd_length_of_le : ∀ (A B : List (List (List Real))),
    A.length ≤ B.length → (cadd A B).length = B.length := by
  intro A
  induction A with
  | nil => intro B _; rfl
  | cons C Cs ih =>
      intro B h
      cases B with
      | nil => exact absurd h (by simp)
      | cons D Ds =>
          show (biadd C D :: cadd Cs Ds).length = (D :: Ds).length
          simp only [List.length_cons]
          rw [ih Ds (by simpa using h)]

theorem cadd_append_of_le : ∀ (A B : List (List (List Real))) (Z : List (List Real)),
    A.length ≤ B.length → cadd A (B ++ [Z]) = cadd A B ++ [Z] := by
  intro A
  induction A with
  | nil => intro B Z _; rfl
  | cons C Cs ih =>
      intro B Z h
      cases B with
      | nil => exact absurd h (by simp)
      | cons D Ds =>
          show biadd C D :: cadd Cs (Ds ++ [Z]) = (biadd C D :: cadd Cs Ds) ++ [Z]
          rw [ih Ds Z (by simpa using h)]
          rfl

/-- **The binomial re-expansion, as an existence statement.** A polynomial in `y` with polynomial
coefficients, evaluated at `y = E + L`, is a polynomial in `L` with coefficients polynomial in `x`
and `E` — and the top `L`-coefficient is the top `y`-coefficient, verbatim. -/
theorem expand_shift : ∀ (Ls₀ : List (List Real)) (A : List Real),
    ∃ Cs₀ : List (List (List Real)), Cs₀.length = Ls₀.length ∧
      ∀ x E L : Real, tripev (Cs₀ ++ [[A]]) x E L = bipev (Ls₀ ++ [A]) x (E + L) := by
  intro Ls₀
  induction Ls₀ with
  | nil =>
      intro A
      refine ⟨[], rfl, fun x E L => ?_⟩
      show (pev A x + E * 0) + L * 0 = pev A x + (E + L) * 0
      mach_ring
  | cons p ps ih =>
      intro A
      obtain ⟨Cs', hlen', hid'⟩ := ih A
      let G : List (List (List Real)) := Cs' ++ [[A]]
      let H : List (List (List Real)) := cadd [[p]] (G.map (fun C => [] :: C))
      have hGlen : G.length = ps.length + 1 := by
        show (Cs' ++ [[A]]).length = ps.length + 1
        simp [hlen']
      have hHlen : H.length = ps.length + 1 := by
        show (cadd [[p]] (G.map (fun C => [] :: C))).length = ps.length + 1
        rw [cadd_length_of_le [[p]] _ (by simp [hGlen])]
        simp [hGlen]
      refine ⟨cadd H ([] :: Cs'), ?_, fun x E L => ?_⟩
      · rw [cadd_length_of_le H _ (by simp [hHlen, hlen'])]
        simp [hlen']
      · have happ : cadd H ([] :: Cs') ++ [[A]] = cadd H (([] :: Cs') ++ [[A]]) :=
          (cadd_append_of_le H ([] :: Cs') [A] (by simp [hHlen, hlen'])).symm
        rw [happ, tripev_cadd]
        show tripev (cadd [[p]] (G.map (fun C => [] :: C))) x E L
            + (bipev [] x E + L * tripev G x E L)
            = pev p x + (E + L) * bipev (ps ++ [A]) x (E + L)
        rw [tripev_cadd, tripev_shift]
        have hG : tripev G x E L = bipev (ps ++ [A]) x (E + L) := hid' x E L
        rw [hG]
        show ((pev p x + E * 0) + L * 0) + E * bipev (ps ++ [A]) x (E + L)
            + (0 + L * bipev (ps ++ [A]) x (E + L))
            = pev p x + (E + L) * bipev (ps ++ [A]) x (E + L)
        mach_mpoly [pev p x, E, L, bipev (ps ++ [A]) x (E + L)]



/-! ## A bounded polynomial is eventually constant -/

/-- **A polynomial bounded on a ray is eventually constant.** If the tail dies, the polynomial is its
head. Otherwise `pev_leading_form` floors the tail at `c > 0`, so `|x · tail| ≥ c·x`, while the
triangle inequality caps it at `K + |a|`. One explicit `x` refutes the cap. -/
theorem pev_evConst_of_bounded {P : List Real} {K X : Real} (hX : 1 ≤ X)
    (hb : ∀ x : Real, X ≤ x → abs (pev P x) ≤ K) :
    ∃ a W : Real, 1 ≤ W ∧ ∀ x : Real, W ≤ x → pev P x = a := by
  cases P with
  | nil => exact ⟨0, 1, le_refl 1, fun _ _ => rfl⟩
  | cons a as =>
      rcases pev_leading_form as with ⟨Z, hZ, hz⟩ | ⟨c, C, d, Xl, hc, hXl, hbl⟩
      · refine ⟨a, Z, hZ, fun x hx => ?_⟩
        show a + x * pev as x = a
        rw [hz x hx]; mach_ring
      · exfalso
        have hcne : c ≠ 0 := ne_of_gt hc
        have hX0 : (0 : Real) ≤ X := le_trans (le_of_lt zero_lt_one_ax) hX
        have hXl0 : (0 : Real) ≤ Xl := le_trans (le_of_lt zero_lt_one_ax) hXl
        have hM0 : (0 : Real) ≤ (abs K + abs a) / c :=
          div_nonneg_of_nonneg_pos (add_nonneg (abs_nonneg K) (abs_nonneg a)) hc
        have hxX : X ≤ X + Xl + (abs K + abs a) / c :=
          le_trans (le_add_nonneg' hXl0) (le_add_nonneg' hM0)
        have hxXl : Xl ≤ X + Xl + (abs K + abs a) / c := by
          have e : X + Xl + (abs K + abs a) / c = Xl + (X + (abs K + abs a) / c) := by
            mach_ring
          rw [e]; exact le_add_nonneg' (add_nonneg hX0 hM0)
        have hx1 : (1 : Real) ≤ X + Xl + (abs K + abs a) / c := le_trans hX hxX
        have hx0 : (0 : Real) ≤ X + Xl + (abs K + abs a) / c :=
          le_trans (le_of_lt zero_lt_one_ax) hx1
        -- the tail is floored at `c`
        have hfloor : c ≤ abs (pev as (X + Xl + (abs K + abs a) / c)) := by
          refine le_trans ?_ (hbl _ hxXl).1
          have v := mul_le_mul_of_nonneg_left (one_le_powNat hx1 d) (le_of_lt hc)
          have e : c * 1 = c := by mach_ring
          rw [e] at v; exact v
        -- so the product is at least `x·c`
        have hprod : (X + Xl + (abs K + abs a) / c) * c
            ≤ abs ((X + Xl + (abs K + abs a) / c) * pev as (X + Xl + (abs K + abs a) / c)) := by
          rw [abs_mul, abs_of_nonneg hx0]
          exact mul_le_mul_of_nonneg_left hfloor hx0
        -- and at most `|K| + |a|`
        have hcap : abs ((X + Xl + (abs K + abs a) / c) * pev as (X + Xl + (abs K + abs a) / c))
            ≤ abs K + abs a := by
          have h1 := abs_add_ge (a := a)
            (b := (X + Xl + (abs K + abs a) / c) * pev as (X + Xl + (abs K + abs a) / c))
          have h2 : abs (pev (a :: as) (X + Xl + (abs K + abs a) / c)) ≤ abs K :=
            le_trans (hb _ hxX) (le_abs_self K)
          have h3 := le_trans h1 h2
          have v := add_le_add_wit h3 (le_refl (abs a))
          have e : abs ((X + Xl + (abs K + abs a) / c) * pev as (X + Xl + (abs K + abs a) / c))
              - abs a + abs a
              = abs ((X + Xl + (abs K + abs a) / c) * pev as (X + Xl + (abs K + abs a) / c)) := by
            mach_ring
          rw [e] at v; exact v
        -- while `x·c` exceeds it
        have hbig : abs K + abs a < (X + Xl + (abs K + abs a) / c) * c := by
          have e : (X + Xl + (abs K + abs a) / c) * c = (X + Xl) * c + (abs K + abs a) / c * c := by
            mach_ring
          rw [e, div_mul_self' hcne]
          have hpos : (0 : Real) < (X + Xl) * c :=
            mul_pos (lt_of_lt_of_le zero_lt_one_ax (le_trans hX (le_add_nonneg' hXl0))) hc
          have v := add_lt_add_left hpos (abs K + abs a)
          have e2 : abs K + abs a + 0 = abs K + abs a := by mach_ring
          have e3 : abs K + abs a + (X + Xl) * c = (X + Xl) * c + (abs K + abs a) := by mach_ring
          rw [e2, e3] at v; exact v
        exact absurd (lt_of_lt_of_le hbig (le_trans hprod hcap)) (lt_irrefl_ax _)



/-! ## Small transfers -/

/-- `PEq` is `pnorm`-equality, so equal polynomials evaluate equally. -/
private theorem pev_of_peq' {A B : List Real} (h : PEq A B) (x : Real) : pev A x = pev B x := by
  rw [← pev_pnorm A, h, pev_pnorm B]

/-- `EvDom` gives "not eventually zero". -/
theorem not_evZeroF_of_evDom {f : Real → Real} (h : EvDom f) : ¬ EvZeroF f := by
  obtain ⟨X₁, hX₁, hnv⟩ := evNonvanish_of_evDom h
  intro ⟨X₂, hX₂, hz⟩
  obtain ⟨X, _, hXa, hXb⟩ := two_bounds' hX₁ hX₂
  exact hnv X hXa (hz X hXb)

/-- A nonzero polynomial is eventually nonzero. -/
theorem pev_evNonvanish {L : List Real} (hL : pnorm L ≠ []) :
    ∃ X : Real, 1 ≤ X ∧ ∀ x : Real, X ≤ x → pev L x ≠ 0 := by
  rcases pev_eventual_sign L with hz | ⟨c, d, X, hc, hX, hb⟩ | ⟨c, d, X, hc, hX, hb⟩
  · exact absurd (pnorm_eq_nil_of_evZero hz) hL
  · refine ⟨X, hX, fun x hx hzero => ?_⟩
    have hx0 : (0 : Real) < x := lt_of_lt_of_le zero_lt_one_ax (le_trans hX hx)
    have hp : 0 < c * powNat x d := mul_pos hc (powNat_pos hx0 d)
    have h1 := hb x hx
    rw [hzero] at h1
    exact absurd (lt_of_lt_of_le hp h1) (lt_irrefl_ax 0)
  · refine ⟨X, hX, fun x hx hzero => ?_⟩
    have hx0 : (0 : Real) < x := lt_of_lt_of_le zero_lt_one_ax (le_trans hX hx)
    have hp : 0 < c * powNat x d := mul_pos hc (powNat_pos hx0 d)
    have h1 := hb x hx
    rw [hzero] at h1
    have e : (0 : Real) - 0 = 0 := by mach_ring
    rw [e] at h1
    exact absurd (lt_of_lt_of_le hp h1) (lt_irrefl_ax 0)

/-- The cross-multiplied identity, divided out where both denominators live. -/
theorem div_eq_of_cross {p q p' q' : Real} (hq : q ≠ 0) (hq' : q' ≠ 0)
    (h : p * q' = p' * q) : p / q = p' * (1 / q') := by
  rw [div_def p q hq]
  have e1 : p * (1 / q) = p * (1 / q) * (q' * (1 / q')) := by
    rw [mul_inv q' hq']; mach_ring
  have e2 : p * (1 / q) * (q' * (1 / q')) = (p * q') * (1 / q) * (1 / q') := by
    mach_mpoly [p, q', (1 : Real) / q, (1 : Real) / q']
  have e3 : (p' * q) * (1 / q) * (1 / q') = p' * (1 / q') * (q * (1 / q)) := by
    mach_mpoly [p', q, (1 : Real) / q, (1 : Real) / q']
  rw [e1, e2, h, e3, mul_inv q hq]
  mach_ring

/-! ## The capstone -/

/-- **`BoundedGermTranscendence` holds.** See the module docstring for the route. -/
theorem boundedGermTranscendence_holds : BoundedGermTranscendence := by
  intro S hS hbd hnc A Ls hA hrelEx
  obtain ⟨K, XK, hXK, hK⟩ := hbd
  obtain ⟨P, Q, X₀, hX₀, hQ0, hSPQ⟩ := hS
  obtain ⟨Xr, hXr, hr⟩ := hrelEx
  -- the obligation's relation, as one coefficient list
  have hrel : ∀ x : Real, Xr ≤ x → bipev (Ls ++ [A]) x (Fbasis (S x)) = 0 := by
    intro x hx
    have h := hr x hx
    rw [bipev_concat]
    have e : bipev Ls x (Fbasis (S x)) + powNat (Fbasis (S x)) Ls.length * pev A x
        = bipevLead A Ls x (Fbasis (S x)) := by
      show bipev Ls x (Fbasis (S x)) + powNat (Fbasis (S x)) Ls.length * pev A x
          = pev A x * powNat (Fbasis (S x)) Ls.length + bipev Ls x (Fbasis (S x))
      mach_ring
    rw [e]; exact h
  have hAnz : ¬ EvZeroF (pev A) := not_evZeroF_of_evDom hA
  -- numerator and denominator are nonzero polynomials
  have hPz : pnorm P ≠ [] := by
    intro hP
    refine hnc ⟨0, X₀, hX₀, fun x hx => ?_⟩
    show S x - 0 = 0
    rw [hSPQ x hx, ← pev_pnorm P x, hP]
    show (0 : Real) / pev Q x - 0 = 0
    rw [zero_div_eq (hQ0 x hx)]; mach_ring
  have hQz : pnorm Q ≠ [] := by
    intro hQ
    apply hQ0 X₀ (le_refl X₀)
    rw [← pev_pnorm Q X₀, hQ]; rfl
  -- lowest terms
  obtain ⟨P', Q', hP'n, hQ'n, hP'z, hQ'z, hcross, hlast⟩ :=
    exists_irred_not_dividing (pnorm Q).length (pnorm P) (pnorm Q) (Nat.le_refl _)
      (pnorm_normal P) (pnorm_normal Q) (by rw [pnorm_idem]; exact hPz)
      (by rw [pnorm_idem]; exact hQz)
  have hcrossx : ∀ x : Real, pev P x * pev Q' x = pev P' x * pev Q x := by
    intro x
    have h := pev_of_peq' hcross x
    rw [pev_pmul, pev_pmul, pev_pnorm, pev_pnorm] at h
    exact h
  have hQ'ne : Q' ≠ [] := by intro h; rw [h] at hQ'z; exact hQ'z rfl
  have hQ'ev : ¬ EvZeroF (pev Q') := fun h => hQ'z (pnorm_eq_nil_of_evZero h)
  obtain ⟨XQ, hXQ, hQ'nv⟩ := pev_evNonvanish hQ'z
  -- `S` agrees with `P'/Q'` on a tail
  have hagree : EvEqF S (fun y => pev P' y * (1 / pev Q' y)) := by
    obtain ⟨W, hW, hWa, hWb⟩ := two_bounds' hX₀ hXQ
    refine ⟨W, hW, fun x hx => ?_⟩
    rw [hSPQ x (le_trans hWa hx)]
    exact div_eq_of_cross (hQ0 x (le_trans hWa hx)) (hQ'nv x (le_trans hWb hx)) (hcrossx x)
  rcases hlast with hQ'1 | ⟨q, hq, hqQ', hqP'⟩
  · -- the reduced denominator is a constant: `S` is a bounded polynomial, hence constant
    obtain ⟨c0, hc0⟩ : ∃ c0 : Real, Q' = [c0] := by
      cases Q' with
      | nil => exact absurd rfl hQ'ne
      | cons c0 cs =>
          cases cs with
          | nil => exact ⟨c0, rfl⟩
          | cons _ _ => exact absurd hQ'1 (by simp)
    subst hc0
    have hc0ne : c0 ≠ 0 := hQ'n c0 rfl
    have e0 : ∀ x : Real, pev [c0] x = c0 := fun x => by show c0 + x * 0 = c0; mach_ring
    obtain ⟨Xa, hXa, hag⟩ := hagree
    obtain ⟨W, hW, hWa, hWb⟩ := two_bounds' hXa hXK
    have hbT : ∀ x : Real, W ≤ x → abs (pev (pscale (1 / c0) P') x) ≤ K := by
      intro x hx
      have e : pev (pscale (1 / c0) P') x = S x := by
        rw [pev_pscale, hag x (le_trans hWa hx)]
        show 1 / c0 * pev P' x = pev P' x * (1 / pev [c0] x)
        rw [e0 x]; mach_ring
      rw [e]; exact hK x (le_trans hWb hx)
    obtain ⟨a, W', hW', hconst⟩ := pev_evConst_of_bounded hW hbT
    refine hnc ⟨a, ?_⟩
    obtain ⟨V, hV, hVa, hVb⟩ := two_bounds' hW hW'
    refine ⟨V, hV, fun x hx => ?_⟩
    show S x - a = 0
    rw [hag x (le_trans hWa (le_trans hVa hx)), ← hconst x (le_trans hVb hx), pev_pscale]
    show pev P' x * (1 / pev [c0] x) - 1 / c0 * pev P' x = 0
    rw [e0 x]; mach_ring
  · -- a genuine pole at the irreducible `q`
    have hchar : ∀ r : Nat, DerivCoprime q (r + 1) := fun r => derivCoprime_of_irred hq r
    rcases ratGerm_eventual_sign ⟨P, Q, X₀, hX₀, hQ0, hSPQ⟩ with
      ⟨Z, hZ, hz⟩ | ⟨Xp, hXp, hp⟩ | ⟨Xn, hXn, hn⟩
    · -- eventually zero is eventually constant
      exact hnc ⟨0, Z, hZ, fun x hx => by show S x - 0 = 0; rw [hz x hx]; mach_ring⟩
    · -- positive: `F(S) = exp S + log S`; re-expand in `log S` over `R[x][exp S]`
      obtain ⟨Cs₀, _, hexp⟩ := expand_shift Ls A
      obtain ⟨Xa, hXa, hag⟩ := hagree
      have hag' : ∀ x : Real, Xa ≤ x → S x = pev P' x * (1 / pev Q' x) := hag
      have hpos : ∃ X : Real, 1 ≤ X ∧ ∀ x : Real, X ≤ x → 0 < pev P' x * (1 / pev Q' x) := by
        obtain ⟨W, hW, hWa, hWb⟩ := two_bounds' hXa hXp
        refine ⟨W, hW, fun x hx => ?_⟩
        rw [← hag' x (le_trans hWa hx)]
        exact hp x (le_trans hWb hx)
      refine no_proper_cleared_relation hq hchar hqP' hP'n hQ'n hQ'ne hqQ' hQ'ev hpos
        (fun r => not_Pdvd_pnsum_one' hq (Nat.succ_ne_zero r))
        (clearsToExp_expCoeffs (fun y => pev P' y * (1 / pev Q' y)) (Cs₀ ++ [[A]])) ?_
      refine ⟨?_, expCoeffs (fun y => pev P' y * (1 / pev Q' y)) Cs₀,
        fun x => bipev [A] x (exp (pev P' x * (1 / pev Q' x))), expCoeffs_concat _ _ _, ?_⟩
      · obtain ⟨W, hW, hWa, hWb⟩ := two_bounds' hXa hXr
        refine ⟨W, hW, fun x hx => ?_⟩
        show gbipev (expCoeffs (fun y => pev P' y * (1 / pev Q' y)) (Cs₀ ++ [[A]])) x
          (Real.log (pev P' x * (1 / pev Q' x))) = 0
        rw [gbipev_expCoeffs_tripev, hexp]
        show bipev (Ls ++ [A]) x
          (exp (pev P' x * (1 / pev Q' x)) + Real.log (pev P' x * (1 / pev Q' x))) = 0
        rw [← hag' x (le_trans hWa hx)]
        exact hrel x (le_trans hWb hx)
      · intro ⟨Z, hZ, hz⟩
        refine hAnz ⟨Z, hZ, fun x hx => ?_⟩
        have h : bipev [A] x (exp (pev P' x * (1 / pev Q' x))) = 0 := hz x hx
        have e : bipev [A] x (exp (pev P' x * (1 / pev Q' x))) = pev A x := by
          show pev A x + exp (pev P' x * (1 / pev Q' x)) * 0 = pev A x
          mach_ring
        rw [e] at h; exact h
    · -- negative: totalisation deletes the logarithm, `F(S) = exp S`
      have hrelN : ProperRel S (Ls ++ [A]) := by
        refine ⟨?_, Ls, A, rfl, hAnz⟩
        obtain ⟨W, hW, hWa, hWb⟩ := two_bounds' hXn hXr
        refine ⟨W, hW, fun x hx => ?_⟩
        have h := hrel x (le_trans hWb hx)
        have e : Fbasis (S x) = exp (S x) := by
          show exp (S x) + Real.log (S x) = exp (S x)
          rw [log_nonpos (le_of_lt (hn x (le_trans hWa hx)))]; mach_ring
        rw [e] at h; exact h
      exact germ_relation_impossible hq hchar hqP' hP'n hQ'n hQ'ne hqQ' hQ'ev hagree hrelN


end MachLib
