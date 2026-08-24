import MachLib.PositiveBranch

/-!
# What `hmin` actually says — the arc runs at `m = 0` and nowhere else

`minimal_grel_identity`, and therefore everything above it, carries

```
hmin : ∀ ns : List (Real → Real), GProperRel u ns → cs.length ≤ ns.length
```

with `ns` ranging over **arbitrary** germ-coefficient lists. That quantifier is much stronger than it
looks, because **every germ has a proper relation of length two**: `−u + 1·u = 0`, whose leading
coefficient is the constant `1`.

So `hmin` forces `cs.length ≤ 2`. In `minimal_expRel_identity`'s setting `cs.length = m + 2`, hence
`m = 0`, and the whole `m`-indexed development — `natMul (m+1) 1`, `relK Q D m`, the `(m+1)` in the
identity — is only ever instantiated at `m = 0`.

## This narrows the scope, and does not weaken the result

Nothing proved becomes false. At `m = 0` the relation is `c₁·L + c₀ = 0` with `c₁` not eventually
zero, i.e. **`log S ∉ R(x)(e^S)`** — which is exactly what the branch needed. Steps 2 and 3 of the
`bf` decomposition are delivered together, in one theorem.

What is *not* delivered is the generality the `m` suggests. A reader of `positive_branch_impossible`
would take it to cover relations of every degree; it covers degree one, because no hypothesis set
containing that `hmin` admits anything else. Better to measure that here than to let a future caller
discover it by failing to discharge the hypothesis.

## Why the theorem is stated with `m` anyway

Removing `m` would mean restating `minimal_grel_identity` and four modules above it. The generality
is *free* — it costs nothing to carry and the proofs are no harder — and if `hmin` is ever weakened
to range over relations with coefficients in a fixed class, the `m` becomes live without a rewrite.
Carrying it is cheap; **claiming it is not**, which is what this module exists to prevent.
-/

namespace MachLib

open Real

/-- **Every germ satisfies a proper relation of length two.** `−u + 1·u = 0`, with the constant `1`
as leading coefficient. -/
theorem gProperRel_witness (u : Real → Real) :
    GProperRel u [fun x => 0 - u x, fun _ => 1] := by
  refine ⟨⟨1, le_refl 1, fun x _ => ?_⟩, [fun x => 0 - u x], (fun _ => 1), rfl, ?_⟩
  · show (0 - u x) + u x * ((1 : Real) + u x * 0) = 0
    mach_ring
  · intro ⟨X, _, h⟩
    exact zero_ne_one_ax (h X (le_refl X)).symm

/-- **`hmin` forces length two.** The quantifier over arbitrary germ-coefficient lists is what does
it: the witness above is always available, so no minimal relation can be longer. -/
theorem minimality_forces_length_two {u : Real → Real} {cs : List (Real → Real)}
    (hmin : ∀ ns : List (Real → Real), GProperRel u ns → cs.length ≤ ns.length) :
    cs.length ≤ 2 := by
  have h := hmin [fun x => 0 - u x, fun _ => 1] (gProperRel_witness u)
  simpa using h

/-- **So the `S > 0` arc runs at `m = 0`.** In `minimal_expRel_identity`'s shape `cs.length = m + 2`,
and `hmin` caps that at two. -/
theorem expRel_minimality_forces_m_zero {u : Real → Real}
    {cs cs₀ : List (Real → Real)} {cd : Real → Real} {m : Nat}
    (hmin : ∀ ns : List (Real → Real), GProperRel u ns → cs.length ≤ ns.length)
    (hcs : cs = cs₀ ++ [cd]) (hlen0 : cs₀.length = m + 1) : m = 0 := by
  have hlen : cs.length = m + 2 := by rw [hcs]; simp [hlen0]
  have h := minimality_forces_length_two hmin
  omega

end MachLib
