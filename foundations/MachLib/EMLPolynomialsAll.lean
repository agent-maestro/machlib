import MachLib.EMLCharacterisation
import MachLib.EMLDepthCost

set_option maxRecDepth 8000

/-!
# Every polynomial is in EML — on all of `ℝ`

Three earlier write-ups deferred this as *"route, not result"*. The datatype is a coefficient list,
and the route sketched in `RESULT_POLY.md` was **weaker than what is now available**: it went through
`subTree`/`mulPos`, which need positivity, so it only covered `(0,∞)`.

**`addGen` and `mulGen` need nothing.** So Horner form works everywhere:

```
polyTree []        = const 0
polyTree (c :: cs) = addGen (const c) (mulGen var (polyTree cs))
```

**The cost is grotesque** and is recorded rather than waved at: each coefficient adds an `addGen`
(34 levels at leaf arguments) around a `mulGen` (54). See `EMLDepthCost`.
-/

namespace MachLib

open Real

/-- Horner evaluation: `evalPoly [a₀, a₁, a₂] x = a₀ + x·(a₁ + x·(a₂ + x·0))`. -/
noncomputable def evalPoly : List Real → Real → Real
  | [], _ => 0
  | c :: cs, x => c + x * evalPoly cs x

noncomputable def polyTree : List Real → EMLTree
  | [] => .const 0
  | c :: cs => addGen (.const c) (mulGen .var (polyTree cs))

/-- **Every polynomial is an EML tree** — unconditionally in `x`. -/
theorem polyTree_eval : ∀ (p : List Real) (x : Real), (polyTree p).eval x = evalPoly p x
  | [], x => rfl
  | c :: cs, x => by
      have ih : (polyTree cs).eval x = evalPoly cs x := polyTree_eval cs x
      have hc : (EMLTree.const c).eval x = c := rfl
      have hv : (EMLTree.var).eval x = x := rfl
      show (addGen (.const c) (mulGen .var (polyTree cs))).eval x = c + x * evalPoly cs x
      rw [addGen_eval, mulGen_eval, hc, hv, ih]

/-- **`InEML` for every polynomial**, in the sense of the characterisation. -/
theorem polynomial_mem_EML (p : List Real) : InEML (evalPoly p) :=
  ⟨polyTree p, fun x => polyTree_eval p x⟩

/-- Sanity: `x²` as a coefficient list, and its cost through this encoding. -/
theorem polyTree_x_sq_eval (x : Real) :
    (polyTree [0, 0, 1]).eval x = 0 + x * (0 + x * (1 + x * 0)) :=
  polyTree_eval [0, 0, 1] x

/-- **The bill, machine-checked at one coefficient: depth 77.**

The per-coefficient increment is **exactly 77** (verified by the depth recurrence, which reproduces
every `rfl`-checked value in `EMLDepthCost`), so `x²` as `polyTree [0,0,1]` is **depth 231** —
against **24** through `mulPos` and **54** through `mulGen` directly.

**That larger figure is NOT stated as a theorem here, for an honest reason:** `mulGen` duplicates its
arguments, so the tree's NODE COUNT grows exponentially even though its depth grows linearly. The
three-coefficient term is too large to build, let alone `rfl`-check. **Generic encodings are not
cheap encodings, and this one is worse in size than in depth.** -/
theorem polyTree_one_coeff_depth : (polyTree [1]).depth = 77 := by rfl

end MachLib
