import MachLib.Differentiation

/-!
# The differentiation rules are not independent either

Second pass of the axiom-minimality sweep. `MachLib.Real` declares **21** `HasDerivAt*` axioms, which
is a lot for a calculus whose usual primitive set is four or five rules plus the seed derivatives.

`HasDerivAt` itself is an opaque `Prop`. Giving it a *definition* — the ε–δ limit of the difference
quotient — would turn every rule into a theorem at a stroke, but it needs a limit notion for
**functions**, and `Limits.lean` currently supplies one only for **sequences**. That is a real piece
of work and is recorded as the standing opportunity rather than attempted here.

What can be done now is ask which rules follow **from the other rules**, treating `HasDerivAt` as
uninterpreted. Two do:

* **`HasDerivAt_neg`** — `−f` is `f · (−1)`, so the product rule with a constant gives it:
  `a·(−1) + f(x)·0 = −a`.
* **`HasDerivAt_sub`** — `f − g` is `f + (−g)`, so the sum rule plus the above gives it.

## And this is where the gate earns its keep

`sub`'s natural derivation goes **through `neg`** — but `neg` is itself declared derivable, so that
derivation would live in `(declared − itself)` and *not* in `(declared − all derivable)`. Each entry
would be true while the joint claim "the base minus {neg, sub} suffices" is false, and the effective
count would double-discount by one.

`check_derivable.py` requires the retained base, so it catches exactly that. The fix is not to weaken
the check: `hasDerivAt_sub_derivable` below routes through the **derived** `neg` theorem rather than
the axiom, so its footprint contains `mul`, `const`, `of_eq`, `add` — and no declared-derivable
axiom. **The first real test of the acyclicity check, and it was constructed before the sweep was
run rather than after it bit.**

`sorryAx`-free.
-/

namespace MachLib.Real

/-- **`HasDerivAt_neg` is derivable.** `−f = f · (−1)`; the product rule supplies the rest, and
`a·(−1) + f(x)·0 = −a`. -/
theorem hasDerivAt_neg_derivable (f : Real → Real) (a x : Real) (hf : HasDerivAt f a x) :
    HasDerivAt (fun y => -f y) (-a) x := by
  have hm := HasDerivAt_mul f (fun _ => -1) a 0 x hf (HasDerivAt_const (-1) x)
  have hval : a * (-1 : Real) + f x * 0 = -a := by mach_ring
  rw [hval] at hm
  exact HasDerivAt_of_eq (fun y => f y * (-1)) (fun y => -f y) (-a) x
    (fun y => by mach_ring) hm

/-- **`HasDerivAt_sub` is derivable.** `f − g = f + (−g)`.

Routed through `hasDerivAt_neg_derivable` — the **theorem**, not the axiom — deliberately. Using the
axiom would put a declared-derivable name in this footprint, and the joint claim would be false while
each entry looked true. -/
theorem hasDerivAt_sub_derivable (f g : Real → Real) (a b x : Real)
    (hf : HasDerivAt f a x) (hg : HasDerivAt g b x) :
    HasDerivAt (fun y => f y - g y) (a - b) x := by
  have hn := hasDerivAt_neg_derivable g b x hg
  have ha := HasDerivAt_add f (fun y => -g y) a (-b) x hf hn
  have hval : a + -b = a - b := by mach_ring
  rw [hval] at ha
  exact HasDerivAt_of_eq (fun y => f y + -g y) (fun y => f y - g y) (a - b) x
    (fun y => by mach_ring) ha

end MachLib.Real
