import MachLib.AbsoluteFoldNest
import MachLib.TrigLipschitz
import MachLib.HyperbolicLipschitz
import MachLib.InverseTrig

/-!
# `pipeline_nested_glob` — the globally-Lipschitz transcendental fold, hypotheses pre-discharged

`pipeline_nested` (in `AbsoluteFoldNest`) takes a `globLip` predicate + a `realOf1` map + the Lipschitz
hypotheses as parameters. This file fixes them to the globally-Lipschitz primitive set
`{sin, cos, tanh, atan}` — each `1`-Lipschitz (`sin_lipschitz`, …) — and discharges the `hLnn`/`hLip`
hypotheses, so an emitted per-kernel certificate only has to supply the `IsFold` proof (generated from
the AST) and the primitive rounding facts (`hround`). This is the transcendental analog of instantiating
`pipeline_arith` directly for an arithmetic kernel: the certifier's `lean_certificate` emits a call to
`pipeline_nested_glob` for a kernel whose transcendental core uses only these primitives.
-/

namespace Certcom

open MachLib.Real

/-- Real semantics of the globally-Lipschitz primitives; anything else maps to `id` (never used, since
`GlobLip` excludes it). -/
noncomputable def realOfGlob : Trans1 → MachLib.Real → MachLib.Real
  | .sin => sin
  | .cos => cos
  | .tanh => tanh
  | .atan => atan
  | _ => id

/-- The globally-`1`-Lipschitz primitive set. -/
def GlobLip (t : Trans1) : Prop := t = .sin ∨ t = .cos ∨ t = .tanh ∨ t = .atan

/-- Each primitive in `GlobLip` is `1`-Lipschitz (its `*_lipschitz` lemma). -/
theorem globLip_lipschitz (t : Trans1) (h : GlobLip t) (p q : MachLib.Real) :
    abs (realOfGlob t p - realOfGlob t q) ≤ 1 * abs (p - q) := by
  rw [one_mul_thm]
  rcases h with rfl | rfl | rfl | rfl
  · exact sin_lipschitz p q
  · exact cos_lipschitz p q
  · exact tanh_lipschitz p q
  · exact atan_lipschitz p q

/-- **The globally-Lipschitz transcendental pipeline, hypotheses pre-discharged.** For any `IsFold
GlobLip e` (arithmetic + `sin`/`cos`/`tanh`/`atan` nodes, any depth), the emitted C's value through
`toR` is within some absolute bound of `exactRn … realOfGlob … e`, given only the primitive rounding
`hround`. -/
theorem pipeline_nested_glob {toR : Float → MachLib.Real} (br : FPBridge toR)
    (i1 : Trans1 → Float → Float) (i2 : Trans2 → Float → Float → Float)
    (r1 : String → Float → Float) (r2 : String → Float → Float → Float)
    (hrt1 : ∀ (t : Trans1) (v : Float), r1 t.cName v = i1 t v)
    (hrt2 : ∀ (t : Trans2) (u v : Float), r2 t.cName u v = i2 t u v) (env : Env)
    (hround : ∀ (t : Trans1) (a : Float),
        abs (toR (i1 t a) - realOfGlob t (toR a)) ≤ u * abs (realOfGlob t (toR a)))
    (e : EML) (he : IsFold GlobLip e) :
    ∃ E, AbsEnc E (toR (evalC r1 r2 env (emitC e)).toF) (exactRn toR realOfGlob env e) :=
  pipeline_nested br realOfGlob (fun _ => 1) i1 i2 r1 r2 hrt1 hrt2 env
    (fun _ _ => le_of_lt zero_lt_one_ax) globLip_lipschitz hround e he

end Certcom
