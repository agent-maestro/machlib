import MachLib.PevEvEq
import MachLib.PolyLogDeriv
import MachLib.EMLRationalGerm

/-!
# Leg 2 of the route to `not RatGerm (log ∘ S)` — clearing denominators

## Where this sits

`(fm)` mapped three legs from *"`log ∘ S` agrees with a rational function on a ray"* to the
contradiction `no_rational_logarithm` already delivers:

  1. **differentiate the germ identity** — `deriv_eq_of_eq_on_ray` (`GermDerivFbasis`), with the
     chain rule for `log ∘ S` and the quotient rule for `N/D` composing from `HasDerivAt_log_pos`,
     `HasDerivAt_mul`, `HasDerivAt_inv`. **THEOREM.**
  2. **clear denominators** — this file. Was UNTOUCHED.
  3. **promote a pointwise identity to `PEq`** — `peq_of_ev_eq` (`PevEvEq`). **THEOREM.**

Leg 1 leaves a pointwise identity between two QUOTIENTS on a ray; `no_rational_logarithm` consumes a
`PEq` between two POLYNOMIALS. Leg 2 is the step between, and the arithmetic is forced:

    S = P/Q  ⟹  S'/S = (P'Q − PQ')/(P·Q)          (quotient rule, then divide by P/Q)
    (N/D)'  = (N'D − ND')/D²

so `S'/S = (N/D)'` cross-multiplies to `(N'D − ND')·(P·Q) = (P'Q − PQ')·D²`, which is exactly
`no_rational_logarithm`'s `hident` at `k = 1`. Nothing here is specific to `log`: the content is that
two rational functions agreeing on a ray have equal cross-products **as polynomials**, and the `log`
shape only fixes what `A`, `B`, `C`, `E` are.

## Why the general form, and why it is stated over `pev` rather than over germs

`peq_of_quot_eq_on_ray` is the whole of leg 2 and mentions neither `log` nor `S`. Stating it that way
is not generality for its own sake — the same cross-multiplication is what `BipevRatFn`'s
`ratFn_deriv_cleared` does by hand for one shape, and the corpus has already paid for the habit of
generalising at the SECOND instance rather than the fifth (`abs_sub_comm` has five private re-proofs
of an exported lemma; `a < a + 1` has seven).

**It does not close the obligation.** Leg 2 standing means all three legs stand, and three legs are
still an assembly, not a theorem: the composite needs the caller to supply `S`'s non-vanishing on the
ray and to produce leg 1's derivative identity at the right point. That assembly is deliberately not
claimed here — `(fm)`'s own note applies, *"two green legs do not imply a third"*, and it applies to
three as well.
-/

namespace MachLib
open Real

/-- **Cross-multiplication, pointwise.** `a/b = c/e` with `b, e ≠ 0` gives `a·e = c·b`.

Stated separately from the ray version because it is pure field arithmetic and the ray version is
about polynomials; keeping them apart is what lets `mach_ring` do the work here without seeing a
`pev`. -/
theorem cross_of_div_eq {a b c e : Real} (hb : b ≠ 0) (he : e ≠ 0)
    (h : a / b = c / e) : a * e = c * b := by
  rw [div_def a b hb, div_def c e he] at h
  have h2 : (a * (1 / b)) * (b * e) = (c * (1 / e)) * (b * e) := by rw [h]
  have l : (a * (1 / b)) * (b * e) = (a * e) * (b * (1 / b)) := by mach_ring
  have r : (c * (1 / e)) * (b * e) = (c * b) * (e * (1 / e)) := by mach_ring
  rw [l, r, mul_inv b hb, mul_inv e he, mul_one_ax, mul_one_ax] at h2
  exact h2

/-- **Leg 2.** Two rational functions agreeing on a ray have equal cross-products *as polynomials*.

The denominators are only required non-zero ON THE RAY, which is what a germ hypothesis supplies;
`peq_of_ev_eq` then upgrades the pointwise identity to `PEq`, and that upgrade is what makes the
conclusion usable by the `q`-adic count, which is syntactic. -/
theorem peq_of_quot_eq_on_ray {A B C E : List Real} {X : Real} (hX : 1 ≤ X)
    (hB : ∀ x : Real, X ≤ x → pev B x ≠ 0)
    (hE : ∀ x : Real, X ≤ x → pev E x ≠ 0)
    (h : ∀ x : Real, X ≤ x → pev A x / pev B x = pev C x / pev E x) :
    PEq (pmul A E) (pmul C B) := by
  refine peq_of_ev_eq hX (fun x hx => ?_)
  rw [pev_pmul, pev_pmul]
  exact cross_of_div_eq (hB x hx) (hE x hx) (h x hx)

/-- **Leg 2 at the log-derivative shape** — the exact `hident` of `no_rational_logarithm`.

`A = P'Q − PQ'` over `B = P·Q` is `S'/S`; `C = N'D − ND'` over `E = D·D` is `(N/D)'`. The hypothesis
is leg 1's output and the conclusion is the count's input, so this is the whole of the join. -/
theorem logderiv_cleared {P Q N D : List Real} {X : Real} (hX : 1 ≤ X)
    (hPQ : ∀ x : Real, X ≤ x → pev (pmul P Q) x ≠ 0)
    (hDD : ∀ x : Real, X ≤ x → pev (pmul D D) x ≠ 0)
    (h : ∀ x : Real, X ≤ x →
        pev (psub (pmul (pderiv P) Q) (pmul P (pderiv Q))) x / pev (pmul P Q) x
          = pev (psub (pmul (pderiv N) D) (pmul N (pderiv D))) x / pev (pmul D D) x) :
    PEq (pmul (psub (pmul (pderiv N) D) (pmul N (pderiv D))) (pmul P Q))
        (pmul (psub (pmul (pderiv P) Q) (pmul P (pderiv Q))) (pmul D D)) :=
  (peq_of_quot_eq_on_ray hX hPQ hDD h).symm

/-- **Leg 2 joined to the count, by instantiation.** From the pointwise identity
`S'/S = (N/D)'` on a ray — with `S = P/Q` having a genuine pole at the irreducible `q` — `False`.

This exists because a shape agreeing with a hypothesis is not the same as a proof that it composes,
and this corpus has paid for the difference: `(fk)`'s duplication audit was "a reading of two files"
until it was turned into two typechecked instantiations. `logderiv_cleared`'s conclusion is
syntactically `no_rational_logarithm`'s `hident`, and this theorem is the machine's word for that
rather than mine.

**What it is not.** It is not `not RatGerm (log ∘ S)`. The caller still has to produce the pointwise
hypothesis from a germ identity — leg 1 — and supply `S`'s non-vanishing on the ray. Legs 1 and 3
are theorems and leg 2 is now one too, but three legs are an assembly, and `(fm)`'s warning that
"two green legs do not imply a third" applies just as well to the third. -/
theorem logderiv_count_composes {q P Q Qt N D : List Real} {X : Real} (hX : 1 ≤ X)
    (hq : PIrred q) (hchar : ∀ r : Nat, DerivCoprime q (r + 1))
    (hPd : ¬ Pdvd q P) (hPn : PNormal P) (hNn : PNormal N)
    {r : Nat} (hQ : PEq Q (pmul (ppow q (r + 1)) Qt)) (hQtd : ¬ Pdvd q Qt)
    (hDne : pnorm D ≠ []) (hlow : Pdvd q D → ¬ Pdvd q N)
    (hPQ : ∀ x : Real, X ≤ x → pev (pmul P Q) x ≠ 0)
    (hDD : ∀ x : Real, X ≤ x → pev (pmul D D) x ≠ 0)
    (h : ∀ x : Real, X ≤ x →
        pev (psub (pmul (pderiv P) Q) (pmul P (pderiv Q))) x / pev (pmul P Q) x
          = pev (psub (pmul (pderiv N) D) (pmul N (pderiv D))) x / pev (pmul D D) x) :
    False :=
  no_rational_logarithm hq hchar hPd hPn hNn hQ hQtd hDne hlow
    (logderiv_cleared hX hPQ hDD h)

end MachLib
