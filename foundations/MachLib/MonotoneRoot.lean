import MachLib.MonotoneFromDeriv
import MachLib.IntermediateValue
import MachLib.Differentiation
import MachLib.Ring

/-!
# The monotonic implicit function, pointwise: a monotonic function has exactly one root
(Gate 2d, IFT gate — brick 1.b.3)

Assembles the two halves already built — IVT existence (`intermediate_value_of_hasDerivAt`) and strict
monotonicity uniqueness (`strictMono_of_deriv_pos`) — into: a function with everywhere-positive derivative
on `[a,b]` and a sign change `f a < 0 < f b` has EXACTLY ONE root in `(a,b)`. This is the pointwise
monotonic implicit function — `yc(x)` is this unique root of the slice `f(x,·)`. (Differentiability of `yc`
as a function of `x` — the inverse-derivative — is the remaining piece.) `rolle_ct` + `sup_exists` +
`hasDerivAt_continuousAt`, no `sorryAx`.
-/

namespace MachLib
namespace Real

private theorem mr_le_trans {a b c : Real} (h1 : a ≤ b) (h2 : b ≤ c) : a ≤ c := by
  rcases (le_iff_lt_or_eq a b).mp h1 with h | h
  · exact le_of_lt_r (lt_of_lt_of_le_r h h2)
  · rw [h]; exact h2

/-- **Strict monotonicity on a subinterval of `[a,b]`.** -/
theorem lt_of_deriv_pos_on {f : Real → Real} {a b : Real}
    (hdiff : ∀ c : Real, a ≤ c → c ≤ b → ∃ f' : Real, HasDerivAt f f' c)
    (hpos : ∀ c f' : Real, a ≤ c → c ≤ b → HasDerivAt f f' c → 0 < f')
    {x y : Real} (hax : a ≤ x) (hxy : x < y) (hyb : y ≤ b) : f x < f y :=
  strictMono_of_deriv_pos f x y hxy
    (fun c hc1 hc2 => hdiff c (mr_le_trans hax hc1) (mr_le_trans hc2 hyb))
    (fun c f' hc1 hc2 hd => hpos c f' (mr_le_trans hax hc1) (mr_le_trans hc2 hyb) hd)

/-- **A monotonic function has EXACTLY ONE root** in `(a,b)` given a sign change: existence from IVT,
uniqueness from strict monotonicity. The pointwise monotonic implicit function. -/
theorem exists_unique_root_of_deriv_pos (f : Real → Real) (a b : Real) (hab : a < b)
    (hdiff : ∀ c : Real, a ≤ c → c ≤ b → ∃ f' : Real, HasDerivAt f f' c)
    (hpos : ∀ c f' : Real, a ≤ c → c ≤ b → HasDerivAt f f' c → 0 < f')
    (hfa : f a < 0) (hfb : 0 < f b) :
    ∃ c : Real, a < c ∧ c < b ∧ f c = 0 ∧ (∀ d : Real, a < d → d < b → f d = 0 → d = c) := by
  obtain ⟨c, hac, hcb, hfc⟩ := intermediate_value_of_hasDerivAt f a b hab hdiff hfa hfb
  refine ⟨c, hac, hcb, hfc, fun d had hdb hfd => ?_⟩
  rcases lt_total d c with h | h | h
  · exfalso
    have hlt := lt_of_deriv_pos_on hdiff hpos (le_of_lt_r had) h (le_of_lt_r hcb)
    rw [hfd, hfc] at hlt; exact lt_irrefl_ax 0 hlt
  · exact h
  · exfalso
    have hlt := lt_of_deriv_pos_on hdiff hpos (le_of_lt_r hac) h (le_of_lt_r hdb)
    rw [hfc, hfd] at hlt; exact lt_irrefl_ax 0 hlt

private theorem mr_eq_of_sub_zero {x y : Real} (h : x - y = 0) : x = y := by
  have h2 : x - y + y = 0 + y := by rw [h]
  rw [show x - y + y = x from by mach_mpoly [x, y], zero_add] at h2
  exact h2

private theorem mr_sub_neg {x y : Real} (h : x < y) : x - y < 0 := by
  have h2 := add_lt_add_left (sub_pos_of_lt h) (-(y - x))
  rw [add_zero, show -(y - x) + (y - x) = 0 from by mach_mpoly [x, y],
    show -(y - x) = x - y from by mach_mpoly [x, y]] at h2
  exact h2

/-- **Inverse-function value existence.** A strictly-increasing (positive-derivative) function `f` on
`[a,b]` hits every intermediate value `y ∈ (f a, f b)` at exactly one point — the inverse-function value
`f⁻¹(y)`. Reuses `exists_unique_root` on `f − y`. This completes the in-model monotonic-analysis toolkit
(continuity, IVT, unique root, and now the inverse value); the inverse/implicit-function DERIVATIVE
(`yc' = −fₓ/fᵧ`) is the bridge-axiom boundary — the opaque `HasDerivAt` gives no ε-δ handle to derive it,
so it needs a witnessable axiom like `hasDerivAt_continuousAt`, plus a bivariate-derivative framework. -/
theorem exists_unique_preimage_of_deriv_pos (f : Real → Real) (a b : Real) (hab : a < b)
    (hdiff : ∀ c : Real, a ≤ c → c ≤ b → ∃ f' : Real, HasDerivAt f f' c)
    (hpos : ∀ c f' : Real, a ≤ c → c ≤ b → HasDerivAt f f' c → 0 < f')
    (y : Real) (hya : f a < y) (hyb : y < f b) :
    ∃ c : Real, a < c ∧ c < b ∧ f c = y ∧ (∀ d : Real, a < d → d < b → f d = y → d = c) := by
  have hdiff' : ∀ c : Real, a ≤ c → c ≤ b → ∃ f' : Real, HasDerivAt (fun t => f t - y) f' c := by
    intro c hca hcb
    obtain ⟨f', hf'⟩ := hdiff c hca hcb
    refine ⟨f', ?_⟩
    rw [show f' = f' - 0 from by mach_ring]
    exact HasDerivAt_sub f (fun _ => y) f' 0 c hf' (HasDerivAt_const y c)
  have hpos' : ∀ c f' : Real, a ≤ c → c ≤ b → HasDerivAt (fun t => f t - y) f' c → 0 < f' := by
    intro c f' hca hcb hd
    obtain ⟨f0, hf0⟩ := hdiff c hca hcb
    have hd0 : HasDerivAt (fun t => f t - y) (f0 - 0) c :=
      HasDerivAt_sub f (fun _ => y) f0 0 c hf0 (HasDerivAt_const y c)
    rw [show f0 - 0 = f0 from by mach_ring] at hd0
    rw [HasDerivAt_unique (fun t => f t - y) f' f0 c hd hd0]
    exact hpos c f0 hca hcb hf0
  obtain ⟨c, hac, hcb, hfc, huniq⟩ :=
    exists_unique_root_of_deriv_pos (fun t => f t - y) a b hab hdiff' hpos'
      (mr_sub_neg hya) (sub_pos_of_lt hyb)
  exact ⟨c, hac, hcb, mr_eq_of_sub_zero hfc, fun d had hdb hfd => huniq d had hdb (by
    show f d - y = 0; rw [hfd]; mach_ring)⟩

end Real
end MachLib
