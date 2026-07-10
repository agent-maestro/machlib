import MachLib.Rolle
import MachLib.Differentiation
import MachLib.AnalyticFiniteZerosReal
import MachLib.FieldLemmas

/-!
# Wronskian proportionality — the `g ≡ 0` leaf discharge

The log-descent's isolated non-`rolle`-derivable case (`hDegen` in
`log_step_multilinear`) is: a degree-1-in-`y_top` barrier `q` whose
Wronskian `g = c_D·q' − c_D'·q` vanishes identically, with `c_D`
(= leading coefficient) not identically zero. Abstractly this cannot be
bounded — `q ≡ 0` on a sub-interval would give unbounded zeros — but for
a *concrete analytic* barrier the degenerate branch is killed by the
identity theorem, and the count reduces to `c_D`'s (lower-degree) count.

This file builds that reduction as a self-contained analytic lemma over
abstract `F, G : Real → Real` carrying `HasDerivAt` hypotheses (so it
applies to `pfaffianChainFn c q` / `pfaffianChainFn c c_D` via
`hasDerivAt_eval_natural`, and to any concrete analytic pair):

- `eq_endpoints_of_deriv_zero` — `f' ≡ 0` on `(p,q)` ⇒ `f p = f q` (MVT).
- `phi_deriv` / `phi_identity` — generalise `SturmNonOscillation`'s
  `phi_euler_*`: the quotient `φ = F·(1/G)` has derivative
  `F'/G − F·G'/G²`, and `φ'·G² = F'·G − F·G'` (the Wronskian).
- `phi_deriv_zero` — when the Wronskian vanishes, `φ' = 0`.
- `wronskian_zero_zeros_subset` — the payoff: `W ≡ 0`, `F` analytic and
  not identically zero ⇒ every zero of `F` is a zero of `G`. Hence
  `#zeros(F) ≤ #zeros(G)`, a UNIFORM reduction (unlike the non-uniform
  `analytic_open_interval_bounded_zeros`).

`analytic_ne_zero_nbhd` is the one new honest analytic axiom (an analytic
function nonzero at a point is nonzero on a neighborhood — a continuity
consequence). No `zero_count_bound_classical`. No sorryAx.
-/

namespace MachLib

open MachLib.Real

/-- `a - b = 0 ⇒ a = b` (self-contained, avoids importing the Khovanskii file). -/
private theorem eq_of_sub_eq_zero' {a b : Real} (h : a - b = 0) : a = b := by
  rw [sub_def] at h
  calc a = (a + -b) + b := by rw [add_assoc, neg_add_self, add_zero]
    _ = 0 + b := by rw [h]
    _ = b := zero_add b

/-- `v · w = 0` with `w ≠ 0` ⇒ `v = 0` (right cancellation via `mul_inv`). -/
private theorem eq_zero_of_mul_right' {v w : Real} (hw : w ≠ 0) (h : v * w = 0) : v = 0 := by
  calc v = v * 1 := (mul_one_ax v).symm
    _ = v * (w * (1 / w)) := by rw [mul_inv w hw]
    _ = v * w * (1 / w) := by rw [← mul_assoc]
    _ = 0 * (1 / w) := by rw [h]
    _ = 0 := zero_mul _

/-- **`f' ≡ 0` ⇒ `f` constant** (endpoints form), directly from the MVT:
the mean-value slope is a derivative, forced to `0` by uniqueness. -/
theorem eq_endpoints_of_deriv_zero (f : Real → Real) (p q : Real) (hpq : p < q)
    (hderiv0 : ∀ c, p ≤ c → c ≤ q → HasDerivAt f 0 c) :
    f p = f q := by
  obtain ⟨c, f', hpc, hcq, hd, heq⟩ :=
    mean_value_theorem_ct f p q hpq (fun c h1 h2 => ⟨0, hderiv0 c h1 h2⟩)
  have hf'0 : f' = 0 :=
    HasDerivAt_unique f f' 0 c hd (hderiv0 c (le_of_lt_r hpc) (le_of_lt_r hcq))
  rw [hf'0, zero_mul] at heq
  exact (eq_of_sub_eq_zero' heq).symm

/-- Quotient-derivative (general `G`): `(F·(1/G))' = F'·(1/G) + F·(−G'/G²)`.
Generalises `SturmNonOscillation.phi_euler_deriv` from `G = vpow α`. -/
theorem phi_deriv (F G : Real → Real) (Fp Gp x : Real)
    (hG_ne : G x ≠ 0) (hF : HasDerivAt F Fp x) (hG : HasDerivAt G Gp x) :
    HasDerivAt (fun y => F y * (1 / G y))
      (Fp * (1 / G x) + F x * (-Gp / (G x * G x))) x :=
  HasDerivAt_mul F (fun y => 1 / G y) Fp (-Gp / (G x * G x)) x hF
    (HasDerivAt_inv G Gp x hG_ne hG)

/-- Wronskian bridge (general `G`): `φ'·G² = F'·G − F·G'`. Generalises
`SturmNonOscillation.phi_euler_identity`. -/
theorem phi_identity (F G : Real → Real) (Fp Gp x : Real) (hG_ne : G x ≠ 0) :
    (Fp * (1 / G x) + F x * (-Gp / (G x * G x))) * (G x * G x)
      = Fp * G x - F x * Gp := by
  have hvv_ne : G x * G x ≠ 0 := mul_ne_zero hG_ne hG_ne
  have h1 : (1 / G x) * (G x * G x) = G x := by
    rw [← mul_assoc, mul_comm (1 / G x) (G x), mul_inv (G x) hG_ne, one_mul_thm]
  have h2 : (-Gp / (G x * G x)) * (G x * G x) = -Gp := by
    rw [div_def (-Gp) (G x * G x) hvv_ne, mul_assoc,
        mul_comm (1 / (G x * G x)) (G x * G x), mul_inv (G x * G x) hvv_ne, mul_one_ax]
  rw [mul_distrib_right, mul_assoc Fp, mul_assoc (F x), h1, h2, mul_neg, ← sub_def]

/-- When the Wronskian `F'·G − F·G'` vanishes at `x` (with `G x ≠ 0`), the
quotient `φ = F·(1/G)` has derivative `0` there. -/
theorem phi_deriv_zero (F G : Real → Real) (Fp Gp x : Real)
    (hG_ne : G x ≠ 0) (hF : HasDerivAt F Fp x) (hG : HasDerivAt G Gp x)
    (hW : Fp * G x - F x * Gp = 0) :
    HasDerivAt (fun y => F y * (1 / G y)) 0 x := by
  have hd := phi_deriv F G Fp Gp x hG_ne hF hG
  have hvv_ne : G x * G x ≠ 0 := mul_ne_zero hG_ne hG_ne
  have hz : (Fp * (1 / G x) + F x * (-Gp / (G x * G x))) * (G x * G x) = 0 :=
    (phi_identity F G Fp Gp x hG_ne).trans hW
  have hval : Fp * (1 / G x) + F x * (-Gp / (G x * G x)) = 0 :=
    eq_zero_of_mul_right' hvv_ne hz
  rwa [hval] at hd

/-! ## Nonzero neighborhood (honest analytic axiom) -/

/-- **`analytic_ne_zero_nbhd`.** An analytic function nonzero at an interior
point is nonzero on an open neighborhood of it (contained in `[a,b]`). This is
the continuity consequence "nonzero at a point ⇒ nonzero nearby"; axiomatized
in the same honest spirit as `analytic_finite_zeros_compact` (NOT the retired
`zero_count_bound_classical`). -/
axiom analytic_ne_zero_nbhd (G : Real → Real) (a b x : Real) :
    IsAnalyticOnReals G (Icc a b) → a < x → x < b → G x ≠ 0 →
    ∃ a' b' : Real, a ≤ a' ∧ b' ≤ b ∧ a' < x ∧ x < b' ∧
      ∀ y, a' < y → y < b' → G y ≠ 0

/-! ## The payoff: `W ≡ 0 ⇒ zeros(F) ⊆ zeros(G)` -/

/-- **Wronskian proportionality (zero-set form).** If the Wronskian
`F'·G − F·G'` vanishes throughout `(a,b)`, `F` and `G` are analytic on
`[a,b]`, and `F` is not identically zero, then **every zero of `F` is a zero
of `G`**. Consequently `#zeros(F) ≤ #zeros(G)` — a UNIFORM reduction of the
degenerate `g ≡ 0` leaf to the leading coefficient's (lower-degree) count.

Proof: at a zero `x₀` of `F` with `G x₀ ≠ 0`, the quotient `φ = F·(1/G)` has
`φ' = 0` on a neighborhood where `G ≠ 0` (`phi_deriv_zero`), hence `φ` is
constant `= φ(x₀) = F(x₀)/G(x₀) = 0` there, so `F ≡ 0` on that neighborhood.
The identity theorem then forces `F ≡ 0` on all of `(a,b)`, contradicting
`hFne`. Therefore `G x₀ = 0`. -/
theorem wronskian_zero_zeros_subset
    (F G Fp Gp : Real → Real) (a b : Real) (hab : a < b)
    (hFanalytic : IsAnalyticOnReals F (Icc a b))
    (hGanalytic : IsAnalyticOnReals G (Icc a b))
    (hFderiv : ∀ x, a < x → x < b → HasDerivAt F (Fp x) x)
    (hGderiv : ∀ x, a < x → x < b → HasDerivAt G (Gp x) x)
    (hW : ∀ x, a < x → x < b → Fp x * G x - F x * Gp x = 0)
    (hFne : ∃ x, Ioo a b x ∧ F x ≠ 0) :
    ∀ x, a < x → x < b → F x = 0 → G x = 0 := by
  intro x0 hx0a hx0b hFx0
  refine Classical.byContradiction (fun hGx0 => ?_)
  obtain ⟨a', b', ha_le, hb_le, ha'x, hxb', hGnbhd⟩ :=
    analytic_ne_zero_nbhd G a b x0 hGanalytic hx0a hx0b hGx0
  -- φ = F·(1/G) has derivative 0 at every point of (a', b')
  have hphi0 : ∀ y, a' < y → y < b' → HasDerivAt (fun z => F z * (1 / G z)) 0 y := by
    intro y hy1 hy2
    have hya : a < y := lt_of_le_of_lt ha_le hy1
    have hyb : y < b := lt_of_lt_of_le hy2 hb_le
    exact phi_deriv_zero F G (Fp y) (Gp y) y (hGnbhd y hy1 hy2)
      (hFderiv y hya hyb) (hGderiv y hya hyb) (hW y hya hyb)
  -- φ is constant on (a', b'); its value is φ(x₀) = F(x₀)·(1/G(x₀)) = 0
  have hFzero : ∀ y, a' < y → y < b' → F y = 0 := by
    intro y hy1 hy2
    have hphi_eq : F x0 * (1 / G x0) = F y * (1 / G y) := by
      rcases lt_total x0 y with h | h | h
      · exact eq_endpoints_of_deriv_zero (fun z => F z * (1 / G z)) x0 y h
          (fun c hc1 hc2 => hphi0 c (lt_of_lt_of_le_r ha'x hc1) (lt_of_le_of_lt_r hc2 hy2))
      · rw [h]
      · exact (eq_endpoints_of_deriv_zero (fun z => F z * (1 / G z)) y x0 h
          (fun c hc1 hc2 => hphi0 c (lt_of_lt_of_le_r hy1 hc1) (lt_of_le_of_lt_r hc2 hxb'))).symm
    rw [hFx0, zero_mul] at hphi_eq          -- 0 = F y * (1 / G y)
    have hGy_ne : G y ≠ 0 := hGnbhd y hy1 hy2
    have hinv_ne : (1 / G y) ≠ 0 := by
      intro hc
      have hmi := mul_inv (G y) hGy_ne
      rw [hc, mul_zero] at hmi              -- hmi : (0 : Real) = 1
      exact absurd hmi (ne_of_lt zero_lt_one_ax)
    exact eq_zero_of_mul_right' hinv_ne hphi_eq.symm
  -- identity theorem: F ≡ 0 on (a', b') ⊆ [a,b] ⇒ F ≡ 0 on (a,b) ⇒ ⊥
  have hFall : ∀ z, Ioo a b z → F z = 0 :=
    analytic_zero_on_subinterval_imp_zero F a b a' b' ha_le hb_le
      (lt_trans_ax ha'x hxb') hab hFanalytic (fun x hx => hFzero x hx.1 hx.2)
  obtain ⟨w, hw, hFw⟩ := hFne
  exact hFw (hFall w hw)

/-- **g≡0 leaf discharge (analytic form).** Assembles
`wronskian_zero_zeros_subset` into the exact `hDegen` conclusion shape:
given a bound `N` on `G`'s zero lists and a vanishing Wronskian, `F`'s zero
lists are bounded by the SAME `N`. Since `G = pfaffianChainFn c c_D` has
`degreeY_top = 0` (leading coefficient), `N` is furnished by the descent's
depth IH — so the degenerate log leaf costs nothing beyond the leading
coefficient's own count. The concrete descent supplies `F,G` (via
`hasDerivAt_eval_natural` + `eml_tree_analytic_on_pos`) and reads `hW` off
the `g ≡ 0` hypothesis through the `pfaffianChainFn` eval homomorphism. -/
theorem wronskian_zero_bounded_zeros
    (F G Fp Gp : Real → Real) (a b : Real) (hab : a < b)
    (hFanalytic : IsAnalyticOnReals F (Icc a b))
    (hGanalytic : IsAnalyticOnReals G (Icc a b))
    (hFderiv : ∀ x, a < x → x < b → HasDerivAt F (Fp x) x)
    (hGderiv : ∀ x, a < x → x < b → HasDerivAt G (Gp x) x)
    (hW : ∀ x, a < x → x < b → Fp x * G x - F x * Gp x = 0)
    (hFne : ∃ x, Ioo a b x ∧ F x ≠ 0)
    (N : Nat)
    (hGbound : ∀ zeros : List Real, zeros.Nodup →
       (∀ z ∈ zeros, a < z ∧ z < b ∧ G z = 0) → zeros.length ≤ N) :
    ∃ M : Nat, ∀ zeros : List Real, zeros.Nodup →
       (∀ z ∈ zeros, a < z ∧ z < b ∧ F z = 0) → zeros.length ≤ M := by
  refine ⟨N, fun zeros hnd hz => hGbound zeros hnd (fun z hzm => ?_)⟩
  obtain ⟨hza, hzb, hFz⟩ := hz z hzm
  exact ⟨hza, hzb,
    wronskian_zero_zeros_subset F G Fp Gp a b hab hFanalytic hGanalytic
      hFderiv hGderiv hW hFne z hza hzb hFz⟩

end MachLib
