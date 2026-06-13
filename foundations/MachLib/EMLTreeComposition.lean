import MachLib.SinNotInEML
import MachLib.EMLHierarchy

/-!
# EMLTree composition (substitution) infrastructure

Defines `EMLTree.subst : EMLTree → EMLTree → EMLTree` and the two core
structural lemmas used throughout downstream proofs:

  - `eval_subst : (t.subst s).eval x = t.eval (s.eval x)`
  - `depth_subst : (t.subst s).depth ≤ t.depth + s.depth`

These were almost-needed for the 2026-06-13 cos any-depth proof
(via a composition argument using `cos x = sin(π/2 - x)`) but were
side-stepped by a direct Pfaffian-zero-counting proof instead.
The substrate is now lifted explicitly because the same pattern is
load-bearing for downstream barriers (Lambert-W, arctan/arccot
positioning, gamma-function scoping) where a composition argument
is the cleanest path.

## What this DOES

- Defines `EMLTree.subst` as a pure structural recursion
  (no clamped-log discontinuity issues at the subst-definition level;
  any such issues are deferred to the consumer's specific use case).
- Proves `eval_subst` and `depth_subst` constructively.
- Adds two small corollaries: `subst_const` (substituting into a
  constant tree is identity) and `subst_var` (substituting into a
  `var` tree just becomes the substituted tree).

## What this does NOT do

- Does not introduce any new axiom.
- Does not introduce any new sorry.
- Does not modify any pre-existing file outside MachLib.lean (registry).
- Does not make a claim about composition closure in any specific
  o-minimal structure; it's purely a structural operation on the
  EMLTree AST.

The user of this file is responsible for:
  - Verifying that `s.eval x` lands in a domain where the consumer
    function (cos, log, etc.) behaves classically — MachLib's
    clamped log means `s.eval x` outside (0,∞) can produce
    non-classical values.
  - Reasoning about the depth bound `t.depth + s.depth` rather than
    the naive `t.depth + s.depth - 1` — the bound is tight when t
    has a `var` leaf, off by 1 when t is a constant tree.
-/

namespace MachLib
namespace EMLTree

/-- Substitute the EMLTree `s` for every occurrence of `var` in `t`.

This is a structural recursion: `const c` becomes `const c` regardless,
`var` becomes `s`, and `eml t1 t2` becomes `eml (t1.subst s) (t2.subst s)`.

Note the argument order: `t.subst s` substitutes `s` for `var` in `t`. -/
def subst : EMLTree → EMLTree → EMLTree
  | const c, _ => const c
  | var, s => s
  | eml t1 t2, s => eml (t1.subst s) (t2.subst s)

/-- Substituting into a constant tree leaves it unchanged. -/
@[simp] theorem subst_const (c : Real) (s : EMLTree) :
    (const c).subst s = const c := rfl

/-- Substituting `s` for `var` in `var` gives `s`. -/
@[simp] theorem subst_var (s : EMLTree) : var.subst s = s := rfl

/-- Substituting distributes through the `eml` constructor. -/
@[simp] theorem subst_eml (t1 t2 s : EMLTree) :
    (eml t1 t2).subst s = eml (t1.subst s) (t2.subst s) := rfl

/-- **Key structural lemma:** evaluating a substituted tree at `x`
is the same as evaluating the original tree at `s.eval x`.

Proof: structural induction on `t`. Each constructor handles the
substitution by pure rewriting:

  - `const c`: `(const c).eval _ = c` regardless of input.
  - `var`: `s.eval x = s.eval x` trivially.
  - `eml t1 t2`: distribute via the IH on each subtree, then unfold
    eval to recover the same `exp - log` shape. -/
theorem eval_subst (t s : EMLTree) (x : Real) :
    (t.subst s).eval x = t.eval (s.eval x) := by
  induction t with
  | const c =>
    -- (const c).subst s = const c; eval = c on both sides.
    show (const c).eval x = (const c).eval (s.eval x)
    rfl
  | var =>
    -- var.subst s = s; eval at x gives s.eval x; eval var at s.eval x = s.eval x.
    show s.eval x = (var : EMLTree).eval (s.eval x)
    rfl
  | eml t1 t2 ih1 ih2 =>
    -- (eml t1 t2).subst s = eml (t1.subst s) (t2.subst s).
    -- Eval at x: exp((t1.subst s).eval x) - log((t2.subst s).eval x).
    -- By IH: = exp(t1.eval (s.eval x)) - log(t2.eval (s.eval x))
    --      = (eml t1 t2).eval (s.eval x).
    show (eml (t1.subst s) (t2.subst s)).eval x
       = (eml t1 t2).eval (s.eval x)
    show Real.exp ((t1.subst s).eval x) - Real.log ((t2.subst s).eval x)
       = Real.exp (t1.eval (s.eval x)) - Real.log (t2.eval (s.eval x))
    rw [ih1, ih2]

/-- **Depth bound for substitution:** the depth of `t.subst s` is at
most `t.depth + s.depth`.

Tightness: when `t` has at least one `var` leaf, the bound is tight
(equality). When `t` is a pure constant tree (no `var`), the bound is
loose — the substituted tree has depth `t.depth`, not `t.depth + s.depth`.

For downstream consumers reasoning about "if `f ∈ EML_k`, then
`(f composed with g) ∈ EML_{k + depth(g)}`", this bound is what
they want. -/
theorem depth_subst (t s : EMLTree) :
    (t.subst s).depth ≤ t.depth + s.depth := by
  induction t with
  | const c =>
    -- subst_const reduces to const c; depth = 0 ≤ 0 + s.depth.
    show (const c).depth ≤ (const c).depth + s.depth
    simp [depth]
  | var =>
    -- subst_var reduces to s; depth = s.depth ≤ 0 + s.depth = s.depth.
    show s.depth ≤ var.depth + s.depth
    simp [depth]
  | eml t1 t2 ih1 ih2 =>
    -- (eml t1 t2).subst s = eml (t1.subst s) (t2.subst s).
    -- Depth of LHS = 1 + max (t1.subst s).depth (t2.subst s).depth.
    -- By IH: ≤ 1 + max (t1.depth + s.depth) (t2.depth + s.depth)
    --       = 1 + max t1.depth t2.depth + s.depth
    --       = (eml t1 t2).depth + s.depth.
    show (eml (t1.subst s) (t2.subst s)).depth
       ≤ (eml t1 t2).depth + s.depth
    show 1 + max (t1.subst s).depth (t2.subst s).depth
       ≤ 1 + max t1.depth t2.depth + s.depth
    have hmax : max (t1.subst s).depth (t2.subst s).depth
              ≤ max t1.depth t2.depth + s.depth := by
      have h1 := ih1
      have h2 := ih2
      -- max a b ≤ c when a ≤ c and b ≤ c.
      apply Nat.max_le.mpr
      refine ⟨?_, ?_⟩
      · -- (t1.subst s).depth ≤ max t1.depth t2.depth + s.depth.
        -- Use h1 : (t1.subst s).depth ≤ t1.depth + s.depth and
        -- t1.depth ≤ max t1.depth t2.depth.
        have hle : t1.depth ≤ max t1.depth t2.depth := Nat.le_max_left _ _
        omega
      · have hle : t2.depth ≤ max t1.depth t2.depth := Nat.le_max_right _ _
        omega
    omega

/-! ## Corollary: composition preserves InEMLDepth with additive depth -/

/-- If `f ∈ EML_k` (via tree `t`) and `g ∈ EML_m` (via tree `s`), then
`f ∘ g ∈ EML_{k+m}` (via tree `t.subst s`).

This is the substantive consequence of `eval_subst` + `depth_subst`:
EML is closed under composition with additive-depth cost. -/
theorem InEMLDepth_comp (f g : Real → Real) (k m : Nat)
    (hf : InEMLDepth f k) (hg : InEMLDepth g m) :
    InEMLDepth (fun x => f (g x)) (k + m) := by
  obtain ⟨t, htd, hft⟩ := hf
  obtain ⟨s, hsd, hgs⟩ := hg
  refine ⟨t.subst s, ?_, ?_⟩
  · -- Depth bound: (t.subst s).depth ≤ t.depth + s.depth ≤ k + m.
    have := depth_subst t s
    omega
  · -- Eval: f (g x) = f (s.eval x) = t.eval (s.eval x) = (t.subst s).eval x.
    intro x
    -- Goal: (fun x => f (g x)) x = (t.subst s).eval x
    show f (g x) = (t.subst s).eval x
    rw [eval_subst]
    -- Goal: f (g x) = t.eval (s.eval x)
    rw [hgs x]
    -- Goal: f (s.eval x) = t.eval (s.eval x)
    exact hft (s.eval x)

end EMLTree
end MachLib
