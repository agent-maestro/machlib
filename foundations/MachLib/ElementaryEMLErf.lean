import MachLib.ElementaryEML

/-!
# `ElementaryEMLErf` — the erf-extended AST, and the Feynman-Kac gate

`ElementaryEML` (in `MachLib.ElementaryEML`) wraps the pure `EMLTree` grammar
(`const`, `var`, `eml`) with `add`/`mul`, because `+` and `*` are not
expressible inside `eml` itself. This file takes the same non-invasive
approach one layer further: `Real.erf` (axiomatized opaquely in
`MachLib.Trig`, no defining integral) is not expressible via `exp`/`log`
composition either, so it gets its own wrapper constructor rather than a
change to `EMLTree` or `ElementaryEML`.

Both `EMLTree` and `ElementaryEML` are load-bearing for ~130 files across
this library via exhaustive pattern matches on their constructors; adding a
constructor to either directly would be a breaking change of a scale no
result in this file justifies. `ElementaryEMLErf` embeds `ElementaryEML` via
`pure` instead, so this file adds strictly new surface area and changes
nothing upstream.

Motivation: `monogate-research/exploration/feynmankac_eml_depth_2026_06_25/FINDINGS.md`
computed (SymPy, not Lean) that the Feynman-Kac indicator expectation
`E[1_{W_T<x}] = ½(1+erf(x/√2T))` is "one gate (EML-3)" — i.e., a single erf
application on top of an EML-finite argument. `depth` below makes that count
precise (arithmetic is free, matching the informal gate-counting convention;
only `eml` and `erf` nodes cost a level), and `feynman_kac_indicator_in_elementary_erf`
proves the concrete instance is representable at depth exactly 1, as a
corollary of the fully general closure theorem `erf_comp_in_elementary_erf`:
erf applied to *any* `ElementaryEML`-representable argument of depth `k` is
`ElementaryEMLErf`-representable at depth `≤ 1 + k`.

This is the tree/discrete-representability reading of "EML-∞ paths → EML-3
expectations": it formalizes the kernel side (erf composed with an
EML-finite argument lands EML-finite) for an arbitrary EML-finite argument,
not just the one Gaussian instance. It does **not** touch the other half of
that target theorem — the actual expectation/convolution operator
`E[f(W_T)]` over an EML-∞ Brownian path — since that needs measure and
integration theory, which does not exist anywhere in MachLib
(see `MachLib.ProbabilisticBound`'s header for the established "probability
as stated hypothesis" precedent). That remains open.
-/

namespace MachLib

/-! ### AST -/

/-- AST for `ElementaryEML` expressions extended with an `erf` gate.
`pure` embeds any `ElementaryEML` expression (hence transitively any pure
`EMLTree`); `erf` is the one new primitive; `add`/`mul` carry over. -/
inductive ElementaryEMLErf : Type where
  | pure : ElementaryEML → ElementaryEMLErf
  | erf  : ElementaryEMLErf → ElementaryEMLErf
  | add  : ElementaryEMLErf → ElementaryEMLErf → ElementaryEMLErf
  | mul  : ElementaryEMLErf → ElementaryEMLErf → ElementaryEMLErf

namespace ElementaryEMLErf

/-- Real evaluation: `pure` delegates to `ElementaryEML.eval`; `erf` applies
`Real.erf`; `add`/`mul` distribute pointwise, as in `ElementaryEML`. -/
noncomputable def eval (e : ElementaryEMLErf) (x : Real) : Real :=
  match e with
  | pure t   => t.eval x
  | erf t    => Real.erf (t.eval x)
  | add a b  => a.eval x + b.eval x
  | mul a b  => a.eval x * b.eval x

end ElementaryEMLErf

/-- Depth of an `ElementaryEML` expression. Matches the informal
gate-counting convention used across this program's exploration notes:
arithmetic (`add`/`mul`) is free (contributes no level, only takes the max
of its branches, mirroring `EMLTree.depth`'s treatment of `eml`'s
children); only the underlying `eml` gate costs a level. -/
def ElementaryEML.depth : ElementaryEML → Nat
  | pure t  => t.depth
  | add a b => max a.depth b.depth
  | mul a b => max a.depth b.depth

namespace ElementaryEMLErf

/-- Depth of an `ElementaryEMLErf` expression: `erf` costs one level on top
of its argument's depth; `add`/`mul` are free, as above. -/
def depth : ElementaryEMLErf → Nat
  | pure e  => e.depth
  | erf t   => 1 + t.depth
  | add a b => max a.depth b.depth
  | mul a b => max a.depth b.depth

end ElementaryEMLErf

/-- `InElementaryEMLErf f k` says `f : Real → Real` is realized by some
`ElementaryEMLErf` expression of depth at most `k`. The `ElementaryEMLErf`
analogue of `InEMLDepth` (`MachLib.EMLHierarchy`). -/
def InElementaryEMLErf (f : Real → Real) (k : Nat) : Prop :=
  ∃ e : ElementaryEMLErf, e.depth ≤ k ∧ ∀ x : Real, f x = e.eval x

-- ===================================================================
-- The general erf-composition closure theorem
-- ===================================================================

/-- **erf-gate closure.** `erf` applied to any `ElementaryEML`-representable
argument of depth `k` is `ElementaryEMLErf`-representable at depth `≤ 1+k`.
This is the general "arbitrary EML-finite kernel argument under erf lands
EML-finite" statement: the Feynman-Kac indicator expectation below is the
`k = 0` instance (argument `c * x`), but this holds for any EML-finite
argument, not just that one. -/
theorem erf_comp_in_elementary_erf {g : Real → Real} {k : Nat}
    (h : ∃ e : ElementaryEML, e.depth ≤ k ∧ ∀ x : Real, g x = e.eval x) :
    InElementaryEMLErf (fun x => Real.erf (g x)) (1 + k) := by
  obtain ⟨e, hd, hev⟩ := h
  refine ⟨ElementaryEMLErf.erf (ElementaryEMLErf.pure e), ?_, ?_⟩
  · show 1 + e.depth ≤ 1 + k
    omega
  · intro x
    show Real.erf (g x) = Real.erf (e.eval x)
    rw [hev x]

-- ===================================================================
-- The concrete Feynman-Kac instance
-- ===================================================================

/-- `c * x` is `ElementaryEML`-representable at depth 0 (pure arithmetic,
no `eml` gate), for any scale constant `c`. -/
theorem scaled_var_in_elementary (c : Real) :
    ∃ e : ElementaryEML, e.depth ≤ 0 ∧ ∀ x : Real, c * x = e.eval x := by
  refine ⟨ElementaryEML.mul (.pure (.const c)) (.pure .var), ?_, ?_⟩
  · show max (EMLTree.depth (.const c)) (EMLTree.depth .var) ≤ 0
    simp [EMLTree.depth]
  · intro x
    rfl

/-- **The Feynman-Kac indicator expectation is EML-3 (one erf gate).**
`E[1_{W_T<x}] = ½(1+erf(x/√2T))` — stated here for an arbitrary scale
constant `c` (specializing to `c = 1/√(2T)` for any `T > 0` recovers the
Brownian case; see FINDINGS.md) — is `ElementaryEMLErf`-representable at
depth exactly 1: one erf gate over a depth-0 argument. This is
`erf_comp_in_elementary_erf` at `k = 0`, matching FINDINGS.md's informal
"one gate (EML-3)" count on formal footing. -/
theorem feynman_kac_indicator_in_elementary_erf (c : Real) :
    InElementaryEMLErf (fun x => (1 / (1 + 1)) * (1 + Real.erf (c * x))) 1 := by
  obtain ⟨e0, hd0, hev0⟩ := erf_comp_in_elementary_erf (scaled_var_in_elementary c)
  refine ⟨ElementaryEMLErf.mul (.pure (.pure (.const (1 / (1 + 1)))))
    (ElementaryEMLErf.add (.pure (.pure (.const 1))) e0), ?_, ?_⟩
  · show max 0 (max 0 e0.depth) ≤ 1
    omega
  · intro x
    have h : Real.erf (c * x) = e0.eval x := hev0 x
    show (1 / (1 + 1)) * (1 + Real.erf (c * x))
      = (1 / (1 + 1)) * (1 + e0.eval x)
    rw [h]

end MachLib
