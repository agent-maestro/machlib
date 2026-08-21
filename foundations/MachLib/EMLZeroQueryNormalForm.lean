import MachLib.PevRoots

/-!
# `C₀`, globally: rational outside a finite exceptional set

`ratGerm_of_zero_query` says a zero-query term equals `P/Q` **eventually** — from some `X` on, with
`Q` nonvanishing there. That form was forced by totalisation: with `a/0 = 0` a *global* `P/Q`
identity is false at the denominator's zeros, and pushing those zeros behind a threshold was the
cheapest way to make the statement true.

Cheapest, but not strongest, and the difference matters as soon as the countertarget is global.
`floor` and `mod` are discontinuous at infinitely many points **everywhere**, not at infinity, and an
eventual theorem cannot see the bounded part of the line. Concluding "a `C₀` function has finitely
many discontinuities" from `RatGerm` is a global conclusion drawn from an eventual hypothesis.

This file removes the threshold. The zeros do not have to be pushed away — they have to be
**named**, and there are only finitely many of them:

```
fOcc T = 0  ⟹  ∃ finite E, ∃ P Q,  ∀ x ∉ E,  pev Q x ≠ 0  ∧  T(x) = pev P x / pev Q x
```

## Where it is paid for

The division case, and `PevRoots` is what makes it affordable. At `a / b`, with `b` represented as
`P₂/Q₂` off the exceptional set so far:

* if `pev P₂` vanishes **identically**, then `b` is zero off that set and `div_zero` makes the whole
  quotient `0` there — the totalised branch, handled by naming it rather than avoiding it;
* otherwise `pev P₂` has finitely many roots (`pev_zero_or_finite_roots`, proved by synthetic
  division with no analysis at all), those roots join the exceptional set, and ordinary fraction
  algebra is valid everywhere else.

Cancellation under `+` and `−` still happens inside `padd`/`pmul`, never predicted from leading-order
data — the same reason the eventual version needed an exact representation rather than a better
envelope.

## What it is for

Three consumers, in increasing order of interest:

1. **`C₀` is continuous off a finite set** — a corollary, deliberately kept *downstream* so the
   analytic notion never enters the load-bearing theorem. The normal form is the durable object.
2. **`floor`, `mod` ∉ `C₀`** — the first exclusion that respects the totalised semantics instead of
   pretending they are absent. Not *"modulo is discrete, and continuous primitives compose to
   continuous functions"* — that argument is unavailable here, since `x/x` is a finite term equal to
   `1` off zero and `0` at zero. The honest form: **a finite field expression with totalised division
   has only finitely many exceptional points, and `mod` has infinitely many discontinuities.**
3. **Level 1.** The argument feeding a single `F` occurrence is now globally rational off finitely
   many explicitly controlled points, which is the shape `OneQueryDichotomy` needs.
-/

namespace MachLib

open Real

private theorem pev_one_ne' (x : Real) : pev [(1 : Real)] x ≠ 0 := by
  show (1 : Real) + x * 0 ≠ 0
  have e : (1 : Real) + x * 0 = 1 := by mach_ring
  rw [e]; exact ne_of_gt zero_lt_one_ax

private theorem pev_single (c x : Real) : pev [c] x = c := by
  show c + x * 0 = c; mach_ring

private theorem pev_one_eq_one (x : Real) : pev [(1 : Real)] x = 1 := pev_single 1 x

private theorem pev_varlist (x : Real) : pev [(0 : Real), 1] x = x := by
  show (0 : Real) + x * (1 + x * 0) = x; mach_ring

private theorem not_mem_left {x : Real} {E F : List Real} (h : x ∉ E ++ F) : x ∉ E :=
  fun hm => h (List.mem_append_left F hm)

private theorem not_mem_right {x : Real} {E F : List Real} (h : x ∉ E ++ F) : x ∉ F :=
  fun hm => h (List.mem_append_right E hm)

/-- **The global normal form for zero-query terms.**

Every `F`-free term is a quotient of polynomials with nonvanishing denominator *outside an explicit
finite exceptional set* — no threshold, no tail. The exceptional set is a `List Real`, which in this
corpus is what a finiteness witness looks like.

Compare `ratGerm_of_zero_query`, which gives the same conclusion only for `x ≥ X`. That form suffices
for growth arguments, where everything happens at infinity; it is useless against a countertarget
that misbehaves on a bounded interval. -/
theorem zero_query_finite_exception_normal_form : ∀ T : FTerm, fOcc T = 0 →
    ∃ (E P Q : List Real), ∀ x : Real, x ∉ E →
      pev Q x ≠ 0 ∧ FTerm.eval T x = pev P x / pev Q x := by
  intro T
  induction T with
  | const c =>
      intro _
      refine ⟨[], [c], [1], fun x _ => ⟨pev_one_ne' x, ?_⟩⟩
      show c = pev [c] x / pev [(1 : Real)] x
      rw [pev_single c x, pev_one_eq_one x, div_one_eq]
  | var =>
      intro _
      refine ⟨[], [0, 1], [1], fun x _ => ⟨pev_one_ne' x, ?_⟩⟩
      show x = pev [(0 : Real), 1] x / pev [(1 : Real)] x
      rw [pev_varlist x, pev_one_eq_one x, div_one_eq]
  | add a b iha ihb =>
      intro h
      simp only [fOcc] at h
      obtain ⟨ha0, hb0⟩ : fOcc a = 0 ∧ fOcc b = 0 := by omega
      obtain ⟨E₁, P₁, Q₁, h₁⟩ := iha ha0
      obtain ⟨E₂, P₂, Q₂, h₂⟩ := ihb hb0
      refine ⟨E₁ ++ E₂, padd (pmul P₁ Q₂) (pmul P₂ Q₁), pmul Q₁ Q₂, fun x hx => ?_⟩
      obtain ⟨hq₁, he₁⟩ := h₁ x (not_mem_left hx)
      obtain ⟨hq₂, he₂⟩ := h₂ x (not_mem_right hx)
      refine ⟨by rw [pev_pmul]; exact mul_ne_zero hq₁ hq₂, ?_⟩
      show FTerm.eval a x + FTerm.eval b x
          = pev (padd (pmul P₁ Q₂) (pmul P₂ Q₁)) x / pev (pmul Q₁ Q₂) x
      rw [he₁, he₂, pev_padd, pev_pmul, pev_pmul, pev_pmul]
      exact div_add_div_eq _ _ _ _ hq₁ hq₂
  | sub a b iha ihb =>
      intro h
      simp only [fOcc] at h
      obtain ⟨ha0, hb0⟩ : fOcc a = 0 ∧ fOcc b = 0 := by omega
      obtain ⟨E₁, P₁, Q₁, h₁⟩ := iha ha0
      obtain ⟨E₂, P₂, Q₂, h₂⟩ := ihb hb0
      refine ⟨E₁ ++ E₂, psub (pmul P₁ Q₂) (pmul P₂ Q₁), pmul Q₁ Q₂, fun x hx => ?_⟩
      obtain ⟨hq₁, he₁⟩ := h₁ x (not_mem_left hx)
      obtain ⟨hq₂, he₂⟩ := h₂ x (not_mem_right hx)
      refine ⟨by rw [pev_pmul]; exact mul_ne_zero hq₁ hq₂, ?_⟩
      show FTerm.eval a x - FTerm.eval b x
          = pev (psub (pmul P₁ Q₂) (pmul P₂ Q₁)) x / pev (pmul Q₁ Q₂) x
      rw [he₁, he₂, pev_psub, pev_pmul, pev_pmul, pev_pmul]
      exact div_sub_div_eq _ _ _ _ hq₁ hq₂
  | mul a b iha ihb =>
      intro h
      simp only [fOcc] at h
      obtain ⟨ha0, hb0⟩ : fOcc a = 0 ∧ fOcc b = 0 := by omega
      obtain ⟨E₁, P₁, Q₁, h₁⟩ := iha ha0
      obtain ⟨E₂, P₂, Q₂, h₂⟩ := ihb hb0
      refine ⟨E₁ ++ E₂, pmul P₁ P₂, pmul Q₁ Q₂, fun x hx => ?_⟩
      obtain ⟨hq₁, he₁⟩ := h₁ x (not_mem_left hx)
      obtain ⟨hq₂, he₂⟩ := h₂ x (not_mem_right hx)
      refine ⟨by rw [pev_pmul]; exact mul_ne_zero hq₁ hq₂, ?_⟩
      show FTerm.eval a x * FTerm.eval b x
          = pev (pmul P₁ P₂) x / pev (pmul Q₁ Q₂) x
      rw [he₁, he₂, pev_pmul, pev_pmul]
      exact div_mul_div_eq _ _ _ _ hq₁ hq₂
  | div a b iha ihb =>
      intro h
      simp only [fOcc] at h
      obtain ⟨ha0, hb0⟩ : fOcc a = 0 ∧ fOcc b = 0 := by omega
      obtain ⟨E₁, P₁, Q₁, h₁⟩ := iha ha0
      obtain ⟨E₂, P₂, Q₂, h₂⟩ := ihb hb0
      rcases pev_zero_or_finite_roots P₂ with hz | ⟨R, hR⟩
      · -- the divisor's numerator dies identically: the totalised branch, named not avoided
        refine ⟨E₁ ++ E₂, [0], [1], fun x hx => ⟨pev_one_ne' x, ?_⟩⟩
        obtain ⟨_, he₂⟩ := h₂ x (not_mem_right hx)
        show FTerm.eval a x / FTerm.eval b x = pev [(0 : Real)] x / pev [(1 : Real)] x
        rw [pev_single 0 x, pev_one_eq_one x, div_one_eq, he₂, hz x,
            zero_div_eq (h₂ x (not_mem_right hx)).1, div_zero]
      · -- otherwise adjoin its finitely many roots
        refine ⟨(E₁ ++ E₂) ++ R, pmul P₁ Q₂, pmul Q₁ P₂, fun x hx => ?_⟩
        obtain ⟨hq₁, he₁⟩ := h₁ x (not_mem_left (not_mem_left hx))
        obtain ⟨hq₂, he₂⟩ := h₂ x (not_mem_right (not_mem_left hx))
        have hp₂ : pev P₂ x ≠ 0 := fun hzero => not_mem_right hx (hR x hzero)
        refine ⟨by rw [pev_pmul]; exact mul_ne_zero hq₁ hp₂, ?_⟩
        show FTerm.eval a x / FTerm.eval b x = pev (pmul P₁ Q₂) x / pev (pmul Q₁ P₂) x
        rw [he₁, he₂, pev_pmul, pev_pmul]
        exact div_div_div_eq _ _ _ _ hq₁ hq₂ hp₂
  | F a _ => intro h; simp only [fOcc] at h; omega

/-! ## The exclusion, algebraically — level sets, not continuity -/

/-- **Every level set of a zero-query function is finite, or everything off the exceptional set.**

This is the algebraic content that the continuity argument was reaching for, and it needs no
continuity at all: `T(x) = c` off the exceptional set says the polynomial `P − c·Q` vanishes, and
`pev_zero_or_finite_roots` gives the dichotomy. -/
theorem zero_query_level_set (T : FTerm) (h0 : fOcc T = 0) (c : Real) :
    ∃ E : List Real,
      (∀ x : Real, x ∉ E → FTerm.eval T x = c) ∨ (∀ x : Real, FTerm.eval T x = c → x ∈ E) := by
  obtain ⟨E, P, Q, hE⟩ := zero_query_finite_exception_normal_form T h0
  rcases pev_zero_or_finite_roots (psub P (pscale c Q)) with hz | ⟨R, hR⟩
  · refine ⟨E, Or.inl (fun x hx => ?_)⟩
    obtain ⟨hq, he⟩ := hE x hx
    have h := hz x
    rw [pev_psub, pev_pscale] at h
    have hpc : pev P x = c * pev Q x := by
      have e : pev P x = pev P x - c * pev Q x + c * pev Q x := by
        mach_mpoly [pev P x, c, pev Q x]
      rw [h] at e
      have e0 : (0 : Real) + c * pev Q x = c * pev Q x := by mach_ring
      rw [e0] at e; exact e
    rw [he, hpc]
    have ec : c * pev Q x = pev Q x * c := by mach_mpoly [c, pev Q x]
    rw [ec]; exact mul_div_cancel_left' hq
  · refine ⟨E ++ R, Or.inr (fun x hxc => ?_)⟩
    rcases Classical.em (x ∈ E) with hin | hout
    · exact List.mem_append_left R hin
    · obtain ⟨hq, he⟩ := hE x hout
      refine List.mem_append_right E (hR x ?_)
      rw [pev_psub, pev_pscale]
      have hd : pev P x / pev Q x = c := by rw [← he]; exact hxc
      have hm : pev P x = c * pev Q x := by
        have e := div_mul_self' (a := pev P x) hq
        rw [hd] at e; exact e.symm
      rw [hm]
      mach_mpoly [c, pev Q x]

/-- **Two infinite level sets are impossible at query level zero.**

The countertarget shape, stated without cardinality: a level is "infinite" when no finite list
exhausts it. `floor` and `mod` are of exactly this shape — `floor` is `0` throughout `[0,1)` and `1`
throughout `[1,2)`, and neither is exhausted by any finite list.

Instantiating it at *this corpus's* `floor` is **not** possible today, and that is worth recording:
`MachLib/Forge.lean` axiomatises `floor` by bracketing only (`floor_le`, `lt_floor_add_one`,
`floor_zero`), which does not pin `floor` to be constant on `[0,1)` — its own docstring notes the
integer-valued facts are not derivable. So the corpus cannot presently show `floor` has even one
infinite level set. The exclusion is ready; the countertarget is under-specified. -/
theorem not_zero_query_of_two_infinite_levels
    (f : Real → Real) (c₁ c₂ : Real) (hne : c₁ ≠ c₂)
    (h₁ : ∀ L : List Real, ∃ x : Real, x ∉ L ∧ f x = c₁)
    (h₂ : ∀ L : List Real, ∃ x : Real, x ∉ L ∧ f x = c₂) :
    ¬ ∃ T : FTerm, fOcc T = 0 ∧ ∀ x : Real, FTerm.eval T x = f x := by
  rintro ⟨T, h0, hT⟩
  obtain ⟨E, hcase⟩ := zero_query_level_set T h0 c₁
  rcases hcase with hall | hfin
  · -- T = c₁ off E, but c₂ is attained off E too
    obtain ⟨x, hxE, hx2⟩ := h₂ E
    have : c₁ = c₂ := by rw [← hall x hxE, hT x, hx2]
    exact hne this
  · -- the c₁-level is inside the finite list E, yet c₁ is attained off it
    obtain ⟨x, hxE, hx1⟩ := h₁ E
    exact hxE (hfin x (by rw [hT x]; exact hx1))

end MachLib
