-- MonogateEML/Universality.lean
-- The EML universality theorem: every EML-elementary function
-- admits a finite EML routing tree witness.
--
-- E-128 evening session, 2026-04-25.
-- Authored by Claude per feedback_lean_writing_protocol_2026_04_25;
-- pending user verification in VS Code lean4 extension before any
-- public-surface claims of "Lean-verified" status.

import MonogateEML.EMLDepth
import MonogateEML.UpperBounds

open Complex

-- ============================================================
-- 1. Tree substitution (every .var in t replaced by g)
-- ============================================================

/-- Substitute `g` for every `.var` occurrence in `t`. -/
def EMLTree.subst (t : EMLTree) (g : EMLTree) : EMLTree :=
  match t with
  | .const c => .const c
  | .var => g
  | .ceml t1 t2 => .ceml (t1.subst g) (t2.subst g)

/-- Depth of a substituted tree is bounded by the sum of input depths. -/
lemma EMLTree.subst_depth (t g : EMLTree) :
    (t.subst g).depth ≤ t.depth + g.depth := by
  induction t with
  | const c => simp [EMLTree.subst, EMLTree.depth]
  | var => simp [EMLTree.subst, EMLTree.depth]
  | ceml t1 t2 ih1 ih2 =>
    simp only [EMLTree.subst, EMLTree.depth]
    omega

/-- Evaluating a substituted tree composes evaluations. -/
lemma EMLTree.subst_eval (t g : EMLTree) (x : ℂ) :
    (t.subst g).eval x = t.eval (g.eval x) := by
  induction t with
  | const c => simp [EMLTree.subst, EMLTree.eval]
  | var => simp [EMLTree.subst, EMLTree.eval]
  | ceml t1 t2 ih1 ih2 =>
    simp [EMLTree.subst, EMLTree.eval, ih1, ih2]

-- ============================================================
-- 2. EML-elementary predicate + closure under composition
-- ============================================================

/-- A function `f : ℂ → ℂ` is **EML-elementary** when it lies in some
    finite-depth EML class. Equivalently: there exists an EML routing
    tree that evaluates to `f` everywhere. -/
def IsEMLElementary (f : ℂ → ℂ) : Prop :=
  ∃ k, f ∈ EML_k k

/-- The set of EML-elementary functions is closed under composition,
    with depth bound `k + m` for inputs `(k, m)`. -/
theorem EML_k_closed_comp (k m : ℕ) (f g : ℂ → ℂ)
    (hf : f ∈ EML_k k) (hg : g ∈ EML_k m) : (f ∘ g) ∈ EML_k (k + m) := by
  obtain ⟨tf, hdf, hef⟩ := hf
  obtain ⟨tg, hdg, heg⟩ := hg
  refine ⟨tf.subst tg, ?_, ?_⟩
  · have hsub : (tf.subst tg).depth ≤ tf.depth + tg.depth :=
      EMLTree.subst_depth tf tg
    -- depth of subst ≤ tf.depth + tg.depth ≤ k + m
    omega
  · intro x
    -- (f ∘ g) x = f (g x) = tf.eval (g x) = tf.eval (tg.eval x) = (tf.subst tg).eval x
    show f (g x) = (tf.subst tg).eval x
    rw [hef (g x), heg x]
    exact (EMLTree.subst_eval tf tg x).symm

/-- Closure under composition lifted to the predicate. -/
theorem IsEMLElementary.comp {f g : ℂ → ℂ}
    (hf : IsEMLElementary f) (hg : IsEMLElementary g) :
    IsEMLElementary (f ∘ g) := by
  obtain ⟨kf, hkf⟩ := hf
  obtain ⟨kg, hkg⟩ := hg
  exact ⟨kf + kg, EML_k_closed_comp kf kg f g hkf hkg⟩

-- ============================================================
-- 3. Universality — by definition unfolding
-- ============================================================

/-- **EML universality (statement form).** Every EML-elementary function
    admits an EML routing tree witness whose evaluation matches the
    function pointwise.

    The proof is one line by unfolding the definition; the mathematical
    content of universality is in *which* functions are EML-elementary,
    captured by the witness theorems below + closure under composition. -/
theorem eml_universality :
    ∀ f : ℂ → ℂ, IsEMLElementary f → ∃ t : EMLTree, ∀ x, f x = t.eval x := by
  intro f hf
  obtain ⟨_, t, _hd, ht⟩ := hf
  exact ⟨t, ht⟩

-- ============================================================
-- 4. Concrete EML-elementary witnesses
-- ============================================================

/-- The constant function is EML-elementary at depth 0. -/
theorem const_isEMLElementary (c : ℂ) :
    IsEMLElementary (fun _ : ℂ => c) :=
  ⟨0, const_in_EML_k c 0⟩

/-- The identity function is EML-elementary at depth 0. -/
theorem id_isEMLElementary : IsEMLElementary (fun x : ℂ => x) :=
  ⟨0, id_in_EML_k 0⟩

/-- Complex exponential is EML-elementary at depth 1. -/
theorem exp_isEMLElementary :
    IsEMLElementary (fun x : ℂ => Complex.exp x) :=
  ⟨1, exp_in_EML_one⟩

-- ============================================================
-- 5. Compositional witnesses (built via comp closure)
-- ============================================================

/-- exp(exp(x)) is EML-elementary at depth ≤ 2. -/
theorem exp_exp_isEMLElementary :
    IsEMLElementary (fun x : ℂ => Complex.exp (Complex.exp x)) := by
  have h := IsEMLElementary.comp exp_isEMLElementary exp_isEMLElementary
  -- h : IsEMLElementary ((fun x => exp x) ∘ (fun x => exp x))
  --     = IsEMLElementary (fun x => exp (exp x)) by comp definition
  exact h

/-- exp(c) for any constant c is EML-elementary (composition of
    exp with the constant function c). The reduced form is the
    constant function `fun _ => Complex.exp c`. -/
theorem exp_const_isEMLElementary (c : ℂ) :
    IsEMLElementary (fun _ : ℂ => Complex.exp c) := by
  -- Direct — the function is constant, depth 0.
  exact const_isEMLElementary (Complex.exp c)
