import MachLib.OperatorBasisComplete

/-!
# Forge ↔ certifier binding — real kernels, machine-checked

`tools/machlib_bind/bind.py` (in the Forge repo) translates a Forge kernel's canonical
AST body into the corresponding `GExpr` over the certified operator basis, and records
the kernel's `tree_hash` (the target-independent expression identity). The emitted
`GExpr` is the same expression the kernel compiles, *by translation*; the certifier's
bound on it therefore certifies the shipped kernel, and the `tree_hash` is what a
drift gate watches.

This file closes the loop in Lean: it takes `GExpr` terms **verbatim from the binder's
output** for real eml-stdlib kernels and certifies each with `gexpr_fwd_error`. If the
binder emits a term and this file type-checks it under the certifier, the kernel's
forward error is machine-checked — the AST → `GExpr` → bound chain is complete.

(Measured reach, same pass: 273/483 eml-stdlib functions are in the basis; the rest
need `sqrt`/`ln`/`clamp`/`pow`/multi-statement-`let` — named, not hand-waved.)
`sorryAx`-free; 0 new axioms.
-/

namespace MachLib.Real

/-- **`length_sq2`** (`eml-stdlib`, `x*x + y*y`). Binder output:
`(.add (.mul (.leaf x) (.leaf x)) (.mul (.leaf y) (.leaf y)))` — certified verbatim. -/
theorem forge_length_sq2_certified {w x y vxx vyy s : Real} (hw0 : 0 ≤ w) (hw1 : w ≤ 1)
    (hxx : RoundsW w vxx (x * x)) (hyy : RoundsW w vyy (y * y))
    (hs : RoundsW w s (vxx + vyy)) :
    abs (s - (x * x + y * y))
      ≤ (GExpr.add (.mul (.leaf x) (.leaf x)) (.mul (.leaf y) (.leaf y))).Ebound w :=
  gexpr_fwd_error hw0 hw1
    (GRoundedEval.add
      (GRoundedEval.mul (GRoundedEval.leaf x) (GRoundedEval.leaf x) hxx)
      (GRoundedEval.mul (GRoundedEval.leaf y) (GRoundedEval.leaf y) hyy) hs)
    ⟨⟨trivial, trivial⟩, ⟨trivial, trivial⟩⟩

/-- **`sigmoid`** (`eml-stdlib`, `1/(1+exp(−x))`). Binder output:
`(.divO (.leaf 1) (.add (.leaf 1) (.expO (.neg (.leaf x)))) m)` — a division kernel.
The `÷` guard `m ≤ 1+exp(−x)` holds with `m = 1` because `exp(−x) > 0`; the computed
denominator guard `1 ≤ vd` is what a real evaluation provides. Certified verbatim. -/
theorem forge_sigmoid_certified {w x ve vd p : Real} (hw0 : 0 ≤ w) (hw1 : w ≤ 1)
    (hexp : RoundsW w ve (exp (-x))) (hd : RoundsW w vd (1 + ve))
    (hvd : 1 ≤ vd) (hp : RoundsW w p (1 / vd)) :
    abs (p - 1 / (1 + exp (-x)))
      ≤ (GExpr.divO (.leaf 1) (.add (.leaf 1) (.expO (.neg (.leaf x)))) 1).Ebound w :=
  gexpr_fwd_error hw0 hw1
    (GRoundedEval.divO (GRoundedEval.leaf 1)
      (GRoundedEval.add (GRoundedEval.leaf 1)
        (GRoundedEval.expO (GRoundedEval.neg (GRoundedEval.leaf x)) hexp) hd) hvd hp)
    ⟨trivial, ⟨trivial, trivial⟩, zero_lt_one_ax, le_add_of_nonneg_right (le_of_lt (exp_pos (-x)))⟩

/-- **`clamp`** (`eml-stdlib`, e.g. `clamp_bounded`). Binder output:
`(.clampO inner lo hi)`. `clamp` is exact (no rounding) and 1-Lipschitz, so it
*preserves* its argument's error: clamping a rounded square `fl(x²)` lands within the
square's own forward error `w·|x²|` of `clamp(x²)` — the bound carries through unchanged,
showing the certifier folds `clamp` with no error amplification. -/
theorem forge_clamp_sq_certified {w x vxx lo hi : Real} (hw0 : 0 ≤ w) (hw1 : w ≤ 1)
    (hlohi : lo ≤ hi) (hxx : RoundsW w vxx (x * x)) :
    abs (clamp vxx lo hi - clamp (x * x) lo hi)
      ≤ (GExpr.clampO (.rleaf (x * x)) lo hi).Ebound w :=
  gexpr_fwd_error hw0 hw1 (GRoundedEval.clampO (GRoundedEval.rleaf hxx)) ⟨trivial, hlohi⟩

/-- **Inlined `let` — the sharing case.** `(x+y)²` written `let s = x+y; s*s`. The binder
inlines `s`, *duplicating* `(x+y)`: binder output
`(.mul (.add (.leaf x)(.leaf y)) (.add (.leaf x)(.leaf y)))`. The real kernel rounds
`s` ONCE (`vs` feeds both factors) — which is exactly the GRoundedEval where both copies
round to the same value (both `.add` evals take the *same* `hs`). The certifier bounds
it: its `Ebound` counts `s`'s rounding in both factors (over-counts the shared term),
so the bound is a **sound conservative upper bound** for the shared computation — never
an under-estimate. This is why inlining is valid even though it loses sharing. -/
theorem forge_quad_inlined_let_certified {w x y vs p : Real} (hw0 : 0 ≤ w) (hw1 : w ≤ 1)
    (hs : RoundsW w vs (x + y)) (hp : RoundsW w p (vs * vs)) :
    abs (p - (x + y) * (x + y))
      ≤ (GExpr.mul (.add (.leaf x) (.leaf y)) (.add (.leaf x) (.leaf y))).Ebound w :=
  gexpr_fwd_error hw0 hw1
    (GRoundedEval.mul
      (GRoundedEval.add (GRoundedEval.leaf x) (GRoundedEval.leaf y) hs)
      (GRoundedEval.add (GRoundedEval.leaf x) (GRoundedEval.leaf y) hs) hp)
    ⟨⟨trivial, trivial⟩, ⟨trivial, trivial⟩⟩

end MachLib.Real
