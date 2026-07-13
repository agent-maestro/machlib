import MachLib.MonotoneFromDeriv
import MachLib.IntermediateValue

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

end Real
end MachLib
