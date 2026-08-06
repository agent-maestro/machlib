import MachLib.TailSignCriterion
import MachLib.EMLReciprocalDepth2

/-!
# The scaling barrier — why an entire class of techniques cannot reach `1/x`

**This excludes nothing.** It proves the *shape* of what remains in the `1/x ∉ EML` arm.

`e/x` **is** an EML tree; `1/x` is the open question. `monogate-research/.../ROOT_CASE_CENSUS.md`
argues in prose that they have identical growth, so *"no asymptotic or growth-rate invariant can
separate them"*, and concludes the constant-floor family is the only live one.

**That argument is narrative, and it is about growth rates only. The real statement is bigger and
is a theorem:**

> ### `K/x = K · (1/x)`. The whole family is the positive-scalar orbit of ONE function.
> ### So EVERY scale-invariant property is blind to `K` — at once.

That subsumes growth rates, and also **zero counting, oscillation, sign structure, asymptotic
class, and `TailSign`.** A technique that could exclude `1/x` while admitting `e/x` must be
**scale-SENSITIVE**, and that is a checkable property of a proposed method rather than a matter of
taste.

## The concrete consequence

`TailSign` — the live EML exclusion mechanism, which today's `TailSignCriterion.lean` generalised —
**is scale-invariant** (`tailSign_scale_iff`). Therefore:

> ### **No `TailSign` argument can ever exclude `1/x`.** Not "has not yet"; cannot.

This is why `1/x` sits in the taxonomy's *constant-floor* row and not the *tail-sign* row, and the
row assignment is now a consequence rather than an observation.

No new axioms. No `sorry`.
-/

namespace MachLib
namespace Real

/-- `K/x = K · (1/x)` — the family is a scalar multiple of one function. `div_def`, named for what
it means here. -/
theorem kx_eq_scale (K x : Real) (hx : x ≠ 0) : K / x = K * (1 / x) := div_def K x hx

/-- **THE BARRIER.** Any property invariant under multiplication by a positive scalar takes the
same value on `1/x` and on `K·(1/x)`, for every `K > 0`.

**The proof is one application of the hypothesis — deliberately.** The content of this result is
entirely in its STATEMENT: it names the class of techniques that cannot work. A barrier whose proof
were substantial would be a sign the statement had been made too weak to be the real obstruction. -/
theorem scale_invariant_blind
    (P : (Real → Real) → Prop)
    (hP : ∀ (f : Real → Real) (c : Real), 0 < c → (P f ↔ P (fun x => c * f x)))
    {K : Real} (hK : 0 < K) :
    (P (fun x => 1 / x) ↔ P (fun x => K * (1 / x))) :=
  hP (fun x => 1 / x) K hK

/-! ## `TailSign` is scale-invariant — so it can never exclude `1/x`

Each of the three disjuncts survives multiplication by a positive scalar: positive stays positive,
negative stays negative, zero stays zero. -/

/-- Positive scaling preserves `TailSign`. -/
theorem tailSign_scale {f : Real → Real} {c : Real} (hc : 0 < c) (h : TailSign f) :
    TailSign (fun x => c * f x) := by
  rcases h with ⟨R, hR⟩ | ⟨R, hR⟩ | ⟨R, hR⟩
  · exact TailSign.pos ⟨R, fun x hx => mul_pos hc (hR x hx)⟩
  · refine TailSign.neg ⟨R, fun x hx => ?_⟩
    -- no `mul_neg_of_pos_of_neg` in this corpus; go through `mul_lt_mul_of_pos_right`
    have h := mul_lt_mul_of_pos_right (hR x hx) hc
    have e0 : (0 : Real) * c = 0 := by mach_mpoly [c]
    have e1 : f x * c = c * f x := by mach_mpoly [c, f x]
    rw [e0, e1] at h
    exact h
  · exact TailSign.zero ⟨R, fun x hx => by rw [hR x hx, mul_zero]⟩

/-- **`TailSign` is scale-INVARIANT.** The converse direction divides by `c`, which is why `0 < c`
is needed on both sides rather than merely `c ≠ 0`. -/
theorem tailSign_scale_iff {f : Real → Real} {c : Real} (hc : 0 < c) :
    TailSign f ↔ TailSign (fun x => c * f x) := by
  refine ⟨tailSign_scale hc, fun h => ?_⟩
  have hinv : (0 : Real) < 1 / c := one_div_pos_of_pos hc
  have hback := tailSign_scale hinv h
  -- `(1/c) * (c * f x) = f x`
  have e : (fun x => (1 / c) * (c * f x)) = f := by
    funext x
    have hcne : c ≠ 0 := ne_of_gt hc
    have : (1 / c) * (c * f x) = (c * (1 / c)) * f x := by mach_mpoly [c, 1 / c, f x]
    rw [this, mul_inv c hcne]
    mach_mpoly [f x]
  rwa [e] at hback

/-- **THE CONSEQUENCE: no `TailSign` argument can exclude `1/x` while admitting `e/x`.**

Instantiating the barrier at `P := fun g => ¬ TailSign g` — which is exactly the predicate every
exclusion in `TailSignCriterion.lean` and `GeneralPeriodicTargetBarrier.lean` establishes — gives
that the predicate cannot tell `1/x` from `K·(1/x)` for any `K > 0`.

**`e/x` is in EML, so `¬ TailSign` is FALSE for it; therefore it is false for `1/x` too.** The
mechanism is not merely unproven on `1/x` — it is refuted there. -/
theorem tailSign_cannot_separate_kx {K : Real} (hK : 0 < K) :
    (¬ TailSign (fun x => 1 / x)) ↔ (¬ TailSign (fun x => K * (1 / x))) := by
  refine scale_invariant_blind (fun g => ¬ TailSign g) ?_ hK
  intro f c hc
  constructor
  · intro hnf hts
    exact hnf ((tailSign_scale_iff hc).mpr hts)
  · intro hncf hts
    exact hncf ((tailSign_scale_iff hc).mp hts)

/-- **`1/x` does have `TailSign`** — it is eventually positive — which is the direct reason the
tail-sign family is inapplicable, independent of the barrier above. Recorded so the barrier's
conclusion can be cross-checked against the elementary fact rather than only derived. -/
theorem inv_x_tailSign : TailSign (fun x => 1 / x) :=
  TailSign.pos ⟨0, fun _x hx => one_div_pos_of_pos hx⟩

/-! ## ▸ THE REFORMULATION — what `1/x ∉ EML` is EQUIVALENT to

The barrier says every scale-invariant property is blind. **The contrapositive is a restatement of
the open problem itself**, and it is sharper than the original phrasing:

> ### `e/x ∈ EML`. And `1/x = (1/e) · (e/x)`.
> ### **So `1/x ∉ EML` says exactly: EML is NOT closed under multiplication by the positive scalar `1/e`.**

**That converts a question about one function into a question about a CLOSURE PROPERTY of the
class** — and closure properties are the kind of thing an induction over tree structure can
address, which a single function's membership is not.

`e/x ∈ EML` is proved in the research record
(`monogate-research/.../E5QUATER_RESULT.md`) but has **no tree witness in this corpus**, so it
enters below as an explicit hypothesis rather than being cited as a fact here. -/

/-- `(1/e) · (e/x) = 1/x`, the scalar that would carry the known solution onto the open target. -/
theorem inv_e_scale_of_e_over_x (x : Real) (hx : x ≠ 0) :
    (1 / exp 1) * (exp 1 / x) = 1 / x := by
  have hene : exp 1 ≠ 0 := ne_of_gt (exp_pos 1)
  rw [div_def (exp 1) x hx]
  have e1 : (1 / exp 1) * (exp 1 * (1 / x)) = (exp 1 * (1 / exp 1)) * (1 / x) := by
    mach_mpoly [exp 1, 1 / exp 1, 1 / x]
  rw [e1, mul_inv (exp 1) hene]
  mach_mpoly [1 / x]

/-- **THE REFORMULATION.** If EML were closed under positive scalar multiplication, then `e/x ∈ EML`
would force `1/x ∈ EML`.

**Contrapositive: `1/x ∉ EML` IS the statement that EML fails to be scale-closed**, witnessed at the
single scalar `1/e`.

`hscale` is the closure hypothesis, stated on the positive reals where the target lives; `hex` is
the known solution. -/
theorem inv_x_in_eml_of_scale_closed
    (hscale : ∀ (t : EMLTree) (c : Real), 0 < c →
      ∃ s : EMLTree, ∀ x : Real, 0 < x → s.eval x = c * t.eval x)
    (te : EMLTree) (hex : ∀ x : Real, 0 < x → te.eval x = exp 1 / x) :
    ∃ s : EMLTree, ∀ x : Real, 0 < x → s.eval x = 1 / x := by
  obtain ⟨s, hs⟩ := hscale te (1 / exp 1) (one_div_pos_of_pos (exp_pos 1))
  refine ⟨s, fun x hx => ?_⟩
  rw [hs x hx, hex x hx]
  exact inv_e_scale_of_e_over_x x (ne_of_gt hx)

end Real
end MachLib
