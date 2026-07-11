import MachLib.SingleExpKhovanskii

/-!
# `expPoly_effective_bound` — the clean single-exp Khovanskii bound (no propagation hypotheses)

`expPoly_auto_bound_with_propagation_aux` proves `#zeros ≤ length + Σdeg` for an `ExpPoly`, but only
under two hypotheses that are false in general: `h_prop` (every measure-≤-M ExpPoly is non-vanishing —
false for the zero polynomial) and `h_strict_last` (the last coefficient always has positive degree —
false for a constant top term such as `eˣ`). Those hypotheses let the `aux` sidestep the two genuinely
hard cases; users then had to hand-build an `IsKhovanskiiReducibleExp` witness per kernel (which is why
the 1op Khovanskii Counter hardcodes its preset bounds).

This file discharges both, giving a directly-usable bound for any non-vanishing `ExpPoly`. Every
analytic ingredient already exists and is `rolle_ct`-audited:

* base — `expPoly_zero_count_bound_length_one_simplified`;
* Rolle transfer — `zero_count_scaledReduction_transfer` (`#zeros(ep) ≤ N+1`, unconditional);
* **Case A** (the vanishing reduction `scaledReduction ep c ≡ 0`, i.e. `ep = K·eˣ` is a pure
  exponential) — `expPoly_ode_no_zeros` gives `ep` has NO zeros;
* measure decrease — `sumSimplifiedDegrees_scaledReductionAux_lt` (last of positive degree);
* the drop — `eval_drop_last_when_zero`.

The proof is the strong induction on the measure `length + ΣsimplifiedDeg` that the `aux` does, with
its two false hypotheses replaced by honest case-splits (Case A vs. reduce; last-degree positive vs.
constant).
-/

namespace MachLib.SingleExpKhovanskii.ExpPoly

open MachLib MachLib.SingleExpKhovanskii MachLib.Real MachLib.PolynomialEvidence
open MachLib.PolynomialRootCount

/-- `scaledReductionAux` preserves list length. -/
theorem scaledReductionAux_length (c : Real) (coeffs : List Poly) (offset : Nat) :
    (scaledReductionAux c coeffs offset).length = coeffs.length := by
  induction coeffs generalizing offset with
  | nil => rfl
  | cons hd tl ih => simp [scaledReductionAux, ih]

/-- **Constant-top companion to `sumSimplifiedDegrees_scaledReductionAux_lt`.** When reducing at the
top rate `natCast(offset+len-1)`, the last coefficient produced is exactly the fixed
`polyDerivative last + (const 0)·last` step (the `natCast offset − natCast offset = 0` cancellation at
the top). Returned in `head ++ [step]` concat form so the drop machinery (`eval_drop_last_when_zero`)
applies. The `_lt` lemma handles the positive-degree top (measure strictly drops); this handles the
constant top (the reduced last coefficient is droppable — evaluates to 0). -/
theorem scaledReductionAux_concat_const_top
    (coeffs : List Poly) (offset : Nat) (hne : coeffs ≠ []) :
    ∃ head : List Poly,
      scaledReductionAux (natCast (offset + coeffs.length - 1)) coeffs offset
        = head ++ [Poly.add (polyDerivative (coeffs.getLast hne))
                            (Poly.mul (Poly.const 0) (coeffs.getLast hne))] := by
  induction coeffs generalizing offset with
  | nil => exact absurd rfl hne
  | cons head tail ih =>
    by_cases htail : tail = []
    · subst htail
      refine ⟨[], ?_⟩
      have hoff : offset + 1 - 1 = offset := by omega
      show (Poly.add (polyDerivative head)
                     (Poly.mul (Poly.const ((natCast offset : Real) -
                                            (natCast (offset + 1 - 1)))) head)
            :: scaledReductionAux (natCast (offset + 1 - 1)) [] (offset + 1))
         = _
      rw [hoff]
      have hsub : (natCast offset : Real) - natCast offset = 0 := sub_self _
      rw [hsub]
      rfl
    · have htail_ne : tail ≠ [] := htail
      have hgetlast : (head :: tail).getLast hne = tail.getLast htail_ne :=
        List.getLast_cons htail_ne
      obtain ⟨headTail, hHT⟩ := ih (offset + 1) htail_ne
      refine ⟨Poly.add (polyDerivative head)
                       (Poly.mul (Poly.const ((natCast offset : Real) -
                                              (natCast (offset + (tail.length + 1) - 1)))) head)
              :: headTail, ?_⟩
      have hlen : (head :: tail).length = tail.length + 1 := rfl
      have hoff_eq : offset + (tail.length + 1) - 1 = (offset + 1) + tail.length - 1 := by omega
      show (Poly.add (polyDerivative head)
                     (Poly.mul (Poly.const ((natCast offset : Real) -
                                            (natCast (offset + (tail.length + 1) - 1)))) head)
            :: scaledReductionAux (natCast (offset + (tail.length + 1) - 1)) tail (offset + 1))
         = _
      rw [hoff_eq, hHT, hgetlast, List.cons_append]

/-- `sumSimplifiedDegrees` of a prefix is at most that of the whole (append of a singleton). -/
theorem sumSimplifiedDegrees_append_singleton (L : List Poly) (b : Poly) :
    sumSimplifiedDegrees L ≤ sumSimplifiedDegrees (L ++ [b]) := by
  induction L with
  | nil => rw [List.nil_append, sumSimplifiedDegrees_nil]; exact Nat.zero_le _
  | cons hd tl ih =>
    rw [List.cons_append, sumSimplifiedDegrees_cons, sumSimplifiedDegrees_cons]; omega

/-- Strong-induction core: bound by any measure ceiling `M`. -/
theorem expPoly_bound_by_measure :
    ∀ (M : Nat) (ep : ExpPoly),
      ep.coeffs.length + sumSimplifiedDegrees ep.coeffs ≤ M →
      ∀ (a b : Real), a < b →
      (∃ x : Real, a < x ∧ x < b ∧ ep.eval x ≠ 0) →
      ∀ zeros : List Real, zeros.Nodup →
        (∀ z ∈ zeros, a < z ∧ z < b ∧ ep.eval z = 0) →
        zeros.length ≤ M := by
  intro M
  induction M with
  | zero =>
    intro ep hM a b _ hne_in _ _ _
    -- measure ≤ 0 ⟹ length = 0 ⟹ ep ≡ 0, contradicting hne_in
    obtain ⟨x, _, _, hx⟩ := hne_in
    have hlen : ep.coeffs.length = 0 := by omega
    have : ep.coeffs = [] := List.length_eq_zero.mp hlen
    exact absurd (by show evalAux ep.coeffs 0 x = 0; rw [this]; rfl) hx
  | succ M' ih =>
    intro ep hM a b hab hne_in zeros hnodup hzeros
    match h_coeffs : ep.coeffs with
    | [] =>
      obtain ⟨x, _, _, hx⟩ := hne_in
      exact absurd (by show evalAux ep.coeffs 0 x = 0; rw [h_coeffs]; rfl) hx
    | [p] =>
      -- base case: length 1 ⟹ ⟨[p]⟩; bound by degreeUpper (polySimplify p) ≤ M
      have hne_p : ∃ x : Real, (⟨[p]⟩ : ExpPoly).eval x ≠ 0 := by
        obtain ⟨x, _, _, hx⟩ := hne_in
        exact ⟨x, by show evalAux [p] 0 x ≠ 0; rw [← h_coeffs]; exact hx⟩
      have hzeros_p : ∀ z ∈ zeros, a < z ∧ z < b ∧ (⟨[p]⟩ : ExpPoly).eval z = 0 := by
        intro z hz; obtain ⟨h1, h2, h3⟩ := hzeros z hz
        exact ⟨h1, h2, by show evalAux [p] 0 z = 0; rw [← h_coeffs]; exact h3⟩
      have hbnd := expPoly_zero_count_bound_length_one_simplified p a b hab hne_p zeros hnodup hzeros_p
      have h_meas : sumSimplifiedDegrees ep.coeffs = degreeUpper (polySimplify p) := by
        rw [h_coeffs, sumSimplifiedDegrees_cons, sumSimplifiedDegrees_nil]; omega
      have hlen1 : ep.coeffs.length = 1 := by rw [h_coeffs]; rfl
      omega
    | p :: q :: rest =>
      have hne_coeffs : ep.coeffs ≠ [] := by rw [h_coeffs]; exact List.cons_ne_nil _ _
      have hlen_ge_2 : ep.coeffs.length ≥ 2 := by rw [h_coeffs]; simp
      let c : Real := natCast (ep.coeffs.length - 1)
      let ep_red := scaledReduction ep c
      by_cases hA : ∀ x : Real, a < x → x < b → ep_red.eval x = 0
      · -- Case A: the reduction vanishes ⟹ ep is a pure exponential ⟹ no zeros
        have hno := expPoly_ode_no_zeros ep c a b hab hA hne_in
        have : zeros = [] := by
          rcases zeros with _ | ⟨z, zs⟩
          · rfl
          · obtain ⟨hz1, hz2, hz3⟩ := hzeros z (List.mem_cons_self z zs)
            exact absurd hz3 (hno z hz1 hz2)
        rw [this]; exact Nat.zero_le _
      · -- Case B: the reduction is non-vanishing somewhere on (a,b)
        have hne_red : ∃ x : Real, a < x ∧ x < b ∧ ep_red.eval x ≠ 0 := by
          rcases Classical.em (∃ x : Real, a < x ∧ x < b ∧ ep_red.eval x ≠ 0) with h | h
          · exact h
          · refine absurd (fun x hx1 hx2 => ?_) hA
            rcases Classical.em (ep_red.eval x = 0) with he | he
            · exact he
            · exact absurd ⟨x, hx1, hx2, he⟩ h
        by_cases hlast : degreeUpper (polySimplify (ep.coeffs.getLast hne_coeffs)) > 0
        · -- B1: top of positive degree ⟹ measure strictly drops ⟹ IH on ep_red, transfer +1
          have h_strict := sumSimplifiedDegrees_scaledReductionAux_lt ep.coeffs 0 hne_coeffs hlast
          have h_off : (0 : Nat) + ep.coeffs.length - 1 = ep.coeffs.length - 1 := by omega
          rw [h_off] at h_strict
          have h_len_eq : ep_red.coeffs.length = ep.coeffs.length :=
            scaledReductionAux_length c ep.coeffs 0
          have h_sum_red : sumSimplifiedDegrees ep_red.coeffs
              = sumSimplifiedDegrees (scaledReductionAux (natCast (ep.coeffs.length - 1)) ep.coeffs 0) :=
            rfl
          have h_measure : ep_red.coeffs.length + sumSimplifiedDegrees ep_red.coeffs ≤ M' := by
            rw [h_len_eq, h_sum_red]; omega
          have h_eval_bound := ih ep_red h_measure a b hab hne_red
          have h_transfer := zero_count_scaledReduction_transfer ep c a b hab M' h_eval_bound
          have := h_transfer zeros hnodup hzeros
          omega
        · -- B2: constant top coefficient — the reduced top coefficient vanishes; drop it, then the
          -- surviving head has strictly smaller measure (length −1), so the IH applies to it.
          have hlast0 : degreeUpper (polySimplify (ep.coeffs.getLast hne_coeffs)) = 0 := by omega
          obtain ⟨headRed, hconcat⟩ := scaledReductionAux_concat_const_top ep.coeffs 0 hne_coeffs
          have h_off0 : (0 : Nat) + ep.coeffs.length - 1 = ep.coeffs.length - 1 := by omega
          rw [h_off0] at hconcat
          -- (`set` is a Mathlib tactic, unavailable here — spell the last coefficient out)
          -- the dropped (last) coefficient of `ep_red` evaluates to 0 everywhere
          have h_drop_simp :
              polySimplify (Poly.add (polyDerivative (ep.coeffs.getLast hne_coeffs))
                             (Poly.mul (Poly.const 0) (ep.coeffs.getLast hne_coeffs)))
                = Poly.const 0 :=
            coeffStep_eq_const_zero_when_degreeUpper_zero (ep.coeffs.getLast hne_coeffs) hlast0
          have h_drop_zero :
              ∀ x, Poly.eval (Poly.add (polyDerivative (ep.coeffs.getLast hne_coeffs))
                     (Poly.mul (Poly.const 0) (ep.coeffs.getLast hne_coeffs))) x = 0 :=
            eval_zero_of_eq_polySimplify_const_zero _ h_drop_simp
          -- `ep_red.coeffs = headRed ++ [drop step]` (as a plain list equation over `ep_red`)
          have hconcat' : ep_red.coeffs
              = headRed ++ [Poly.add (polyDerivative (ep.coeffs.getLast hne_coeffs))
                             (Poly.mul (Poly.const 0) (ep.coeffs.getLast hne_coeffs))] := hconcat
          -- eval of `ep_red` equals eval of the head after dropping the vanishing last coefficient
          have h_eval_eq : ∀ x, ep_red.eval x = (⟨headRed⟩ : ExpPoly).eval x := by
            intro x
            have hstep : ep_red.eval x
                = (⟨headRed ++ [Poly.add (polyDerivative (ep.coeffs.getLast hne_coeffs))
                     (Poly.mul (Poly.const 0) (ep.coeffs.getLast hne_coeffs))]⟩
                    : ExpPoly).eval x := by
              show evalAux ep_red.coeffs 0 x = evalAux _ 0 x
              rw [hconcat']
            rw [hstep]
            exact eval_drop_last_when_zero headRed _ h_drop_zero x
          -- measure of the head is ≤ M' (length drops by one; simplified-degree sum can only shrink)
          have h_len_red : ep_red.coeffs.length = ep.coeffs.length :=
            scaledReductionAux_length c ep.coeffs 0
          have h_len_split : ep_red.coeffs.length = headRed.length + 1 := by
            rw [hconcat', List.length_append]; rfl
          have h_headlen : headRed.length + 1 = ep.coeffs.length := by
            rw [← h_len_split, h_len_red]
          have h_sum_head_le : sumSimplifiedDegrees headRed ≤ sumSimplifiedDegrees ep_red.coeffs := by
            rw [hconcat']; exact sumSimplifiedDegrees_append_singleton headRed _
          have h_sum_red_le : sumSimplifiedDegrees ep_red.coeffs ≤ sumSimplifiedDegrees ep.coeffs :=
            sumSimplifiedDegrees_scaledReduction_le ep c
          have h_measure_head :
              (⟨headRed⟩ : ExpPoly).coeffs.length + sumSimplifiedDegrees (⟨headRed⟩ : ExpPoly).coeffs
                ≤ M' := by
            show headRed.length + sumSimplifiedDegrees headRed ≤ M'
            omega
          -- the head is non-vanishing on `(a,b)` (same eval as `ep_red`, which is non-vanishing)
          have hne_head : ∃ x : Real, a < x ∧ x < b ∧ (⟨headRed⟩ : ExpPoly).eval x ≠ 0 := by
            obtain ⟨x0, hx01, hx02, hx0⟩ := hne_red
            exact ⟨x0, hx01, hx02, by rw [← h_eval_eq x0]; exact hx0⟩
          have h_ih_head := ih ⟨headRed⟩ h_measure_head a b hab hne_head
          -- transport the head's bound back to `ep_red`, then Rolle-transfer to `ep` (+1)
          have h_eval_bound : ∀ zeros' : List Real, zeros'.Nodup →
              (∀ z ∈ zeros', a < z ∧ z < b ∧ ep_red.eval z = 0) → zeros'.length ≤ M' := by
            intro zeros' hnd hz'
            apply h_ih_head zeros' hnd
            intro z hz
            obtain ⟨h1, h2, h3⟩ := hz' z hz
            exact ⟨h1, h2, by rw [← h_eval_eq z]; exact h3⟩
          have h_transfer := zero_count_scaledReduction_transfer ep c a b hab M' h_eval_bound
          have hfin := h_transfer zeros hnodup hzeros
          omega

/-- **The clean single-exp Khovanskii bound.** For any `ExpPoly` non-vanishing somewhere on `(a,b)`,
its real zeros on `(a,b)` number at most `length + ΣsimplifiedDeg` — no reducibility witness, no
propagation hypotheses. -/
theorem expPoly_effective_bound (ep : ExpPoly) (a b : Real) (hab : a < b)
    (hne : ∃ x : Real, a < x ∧ x < b ∧ ep.eval x ≠ 0) :
    ∀ zeros : List Real, zeros.Nodup →
      (∀ z ∈ zeros, a < z ∧ z < b ∧ ep.eval z = 0) →
      zeros.length ≤ ep.coeffs.length + sumSimplifiedDegrees ep.coeffs :=
  expPoly_bound_by_measure _ ep (Nat.le_refl _) a b hab hne

/-- If every coefficient has syntactic degree `≤ D`, the simplified-degree sum is `≤ length · D`
(`polySimplify` only lowers degree). -/
theorem sumSimplifiedDegrees_le_length_mul (coeffs : List Poly) (D : Nat)
    (hdeg : ∀ p ∈ coeffs, degreeUpper p ≤ D) :
    sumSimplifiedDegrees coeffs ≤ coeffs.length * D := by
  induction coeffs with
  | nil => rw [sumSimplifiedDegrees_nil]; exact Nat.zero_le _
  | cons p rest ih =>
    rw [sumSimplifiedDegrees_cons, List.length_cons]
    have h1 : degreeUpper (polySimplify p) ≤ D :=
      Nat.le_trans (degreeUpper_polySimplify_le_self p) (hdeg p (List.mem_cons_self p rest))
    have h2 : sumSimplifiedDegrees rest ≤ rest.length * D :=
      ih (fun q hq => hdeg q (List.mem_cons_of_mem p hq))
    have hexp : (rest.length + 1) * D = rest.length * D + D := by rw [Nat.add_mul, Nat.one_mul]
    omega

/-- **Effective count, closed form in the model parameters.** For an `ExpPoly` non-vanishing on
`(a,b)` whose coefficients all have degree `≤ D`, the real-zero count is `≤ length · (D+1)`. With
`length = K+1` (number of exponential modes kept) this is the explicit `(K+1)(D+1)` dependence a
*counting* bound wants — where o-minimality gives only "finite." -/
theorem expPoly_effective_bound_uniform (ep : ExpPoly) (D : Nat)
    (hdeg : ∀ p ∈ ep.coeffs, degreeUpper p ≤ D)
    (a b : Real) (hab : a < b)
    (hne : ∃ x : Real, a < x ∧ x < b ∧ ep.eval x ≠ 0) :
    ∀ zeros : List Real, zeros.Nodup →
      (∀ z ∈ zeros, a < z ∧ z < b ∧ ep.eval z = 0) →
      zeros.length ≤ ep.coeffs.length * (D + 1) := by
  intro zeros hnd hz
  have h := expPoly_effective_bound ep a b hab hne zeros hnd hz
  have h2 := sumSimplifiedDegrees_le_length_mul ep.coeffs D hdeg
  have hexp : ep.coeffs.length * (D + 1) = ep.coeffs.length * D + ep.coeffs.length := by
    rw [Nat.mul_add, Nat.mul_one]
  omega

end MachLib.SingleExpKhovanskii.ExpPoly
