import MachLib.EMLDeclampEncoder
import MachLib.EMLZeroBoundRay

/-!
# The declamped tree varies, but only over finitely many shapes

`(cx)` left one gap on this route: `declamp t a b` is a **different tree per interval**, so a zero
count obtained through it is per-interval and does not by itself feed
`eventually_nonzero_of_uniformZeroBoundFrom`, which needs one `N` for every interval at or beyond a
ray.

The variation is bounded. `declamp` only ever replaces a right child by `const 1`, so every tree it
can produce lies in a finite list computed from `t` alone:

```
declampVariants (.eml t1 t2) =
  (declampVariants t1).flatMap fun v1 =>
    (declampVariants t2).map (fun v2 => .eml v1 v2) ++ [.eml v1 (.const 1)]
```

`declamp_mem_variants` proves membership for every `(a,b)`. So a bound **per variant** gives a bound
for `t`, by taking the maximum over a finite list — `uniformZeroBoundFrom_of_variantBounds`. The
interval-dependence is real but harmless: the tree changes, the maximum does not.

## This is a reduction, not a new obligation

Deliberately no `Prop` is registered here, and the per-variant demand is **not** promoted to an
obligation. The reason is the failure this arc already paid for once.

The naive form — *every* variant of *every* node admits a bound — is **false**, and the same witness
kills it: for `B := expExpTree A` the node `eml A B` has value identically `0`, it is its own
variant, and an identically-zero function admits no bound on any interval. Node-level `¬ EvZeroF`
conditioning (as `SignHardUniformZeroBound` already carries) excludes exactly that witness.

What is **not** settled is whether some *other* variant can be eventually zero while the node itself
is not. A variant is a genuinely different function from `t` — they agree only on the interval whose
clamping pattern selected it — so the node's non-vanishing does not transfer to its variants for
free. Until that is decided, promoting the per-variant demand to an obligation would be stating
something that might be vacuous, which is precisely the step `(cv)` had to retract.

So this module ships the **reduction** and stops there: given the bounds, the uniform conclusion
follows. Supplying them, and conditioning the supply correctly, is the open work.
-/

namespace MachLib

open Real

/-! ## §1 — the finite variant list -/

/-- Every tree `declamp` can produce from `t`, over all intervals. -/
noncomputable def declampVariants : EMLTree → List EMLTree
  | .const c => [.const c]
  | .var     => [EMLTree.var]
  | .eml t1 t2 =>
      (declampVariants t1).flatMap (fun v1 =>
        (declampVariants t2).map (fun v2 => EMLTree.eml v1 v2)
          ++ [EMLTree.eml v1 (EMLTree.const 1)])

/-- **The variation is finite.** Whatever the interval, the declamped tree is one of them. -/
theorem declamp_mem_variants (t : EMLTree) (a b : Real) :
    declamp t a b ∈ declampVariants t := by
  induction t with
  | const c => simp [declamp, declampVariants]
  | var => simp [declamp, declampVariants]
  | eml t1 t2 ih1 ih2 =>
      by_cases hpos : (∀ x, a < x → x < b → 0 < t2.eval x)
      · rw [show declamp (EMLTree.eml t1 t2) a b
              = EMLTree.eml (declamp t1 a b) (declamp t2 a b) from by
            simp only [declamp, if_pos hpos]]
        refine List.mem_flatMap.mpr ⟨declamp t1 a b, ih1, ?_⟩
        exact List.mem_append.mpr
          (Or.inl (List.mem_map.mpr ⟨declamp t2 a b, ih2, rfl⟩))
      · rw [show declamp (EMLTree.eml t1 t2) a b
              = EMLTree.eml (declamp t1 a b) (EMLTree.const 1) from by
            simp only [declamp, if_neg hpos]]
        refine List.mem_flatMap.mpr ⟨declamp t1 a b, ih1, ?_⟩
        exact List.mem_append.mpr (Or.inr (by simp))

/-! ## §2 — maximum over a finite list -/

private def listMaxF (F : EMLTree → Nat) : List EMLTree → Nat
  | []      => 0
  | v :: vs => Nat.max (F v) (listMaxF F vs)

private theorem le_listMaxF (F : EMLTree → Nat) :
    ∀ (L : List EMLTree) (v : EMLTree), v ∈ L → F v ≤ listMaxF F L := by
  intro L
  induction L with
  | nil => intro v hv; exact absurd hv (List.not_mem_nil)
  | cons w ws ih =>
      intro v hv
      rcases List.mem_cons.mp hv with h | h
      · rw [h]; exact Nat.le_max_left _ _
      · exact Nat.le_trans (ih v h) (Nat.le_max_right _ _)

/-! ## §3 — the ray weakens -/

/-- Raising the base only removes intervals, so a bound from `R` is a bound from any `R' ≥ R`. -/
theorem uniformZeroBoundFrom_mono {f : Real → Real} {N : Nat} {R R' : Real} (hRR : R ≤ R')
    (h : UniformZeroBoundFrom f R N) : UniformZeroBoundFrom f R' N :=
  fun a b hR'a hab zeros hnd hz => h a b (le_trans hRR hR'a) hab zeros hnd hz

/-! ## §4 — the reduction

The tree changes with the interval; the maximum does not. -/

/-- **A bound for each variant that actually occurs gives a bound for the tree.** On each interval
the zeros of `t` are the zeros of `declamp t a b` — they agree there — and that tree is one of
finitely many, so the maximum over the variant list serves every interval at or beyond `X₀`.

The hypothesis asks for bounds only on trees `declamp` really produces. §6 shows that matters: some
variants in the list are unreachable, and one of those can be identically zero. -/
theorem uniformZeroBoundFrom_of_reachableBounds (t : EMLTree) (X₀ : Real)
    (hst : ∀ a b : Real, X₀ ≤ a → a < b → LogArgStable t a b)
    (F : EMLTree → Nat)
    (hF : ∀ a b : Real, X₀ ≤ a → a < b →
            UniformZeroBoundFrom (declamp t a b).eval X₀ (F (declamp t a b))) :
    ∃ N : Nat, UniformZeroBoundFrom t.eval X₀ N := by
  refine ⟨listMaxF F (declampVariants t), fun a b hRa hab zeros hnd hz => ?_⟩
  have hmem := declamp_mem_variants t a b
  have heval := declamp_eval t a b (hst a b hRa hab)
  have hzv : ∀ z ∈ zeros, a < z ∧ z < b ∧ (declamp t a b).eval z = 0 := by
    intro z hzm
    obtain ⟨ha, hb, h0⟩ := hz z hzm
    exact ⟨ha, hb, by rw [heval z ha hb]; exact h0⟩
  exact Nat.le_trans (hF a b hRa hab a b hRa hab zeros hnd hzv) (le_listMaxF F _ _ hmem)

/-- Bounds for *every* variant are more than enough — a corollary, since every reachable variant is
in the list. Kept because it is the shape a producer that ignores reachability would supply, but §6
shows its hypothesis can be unsatisfiable, so prefer the reachable form. -/
theorem uniformZeroBoundFrom_of_variantBounds (t : EMLTree) (X₀ : Real)
    (hst : ∀ a b : Real, X₀ ≤ a → a < b → LogArgStable t a b)
    (F : EMLTree → Nat)
    (hF : ∀ v ∈ declampVariants t, UniformZeroBoundFrom v.eval X₀ (F v)) :
    ∃ N : Nat, UniformZeroBoundFrom t.eval X₀ N :=
  uniformZeroBoundFrom_of_reachableBounds t X₀ hst F
    (fun a b _ _ => hF _ (declamp_mem_variants t a b))

/-- The same with the stability hypothesis discharged from sign-definiteness at every node — the
form the depth induction already supplies. The ray is the one `logArgStable_of_evSign` produces, and
the per-variant bounds are weakened onto it by `uniformZeroBoundFrom_mono`. -/
theorem uniformZeroBoundFrom_of_evSign_variantBounds (t : EMLTree)
    (hs : ∀ s : EMLTree, EvSign s.eval) (R : Real) (hR : 1 ≤ R)
    (F : EMLTree → Nat)
    (hF : ∀ v ∈ declampVariants t, UniformZeroBoundFrom v.eval R (F v)) :
    ∃ (X₀ : Real) (N : Nat), 1 ≤ X₀ ∧ UniformZeroBoundFrom t.eval X₀ N := by
  obtain ⟨X₁, hX11, hst⟩ := logArgStable_of_evSign hs t
  obtain ⟨X₀, hX01, hX0R, hX0X1⟩ : ∃ X : Real, 1 ≤ X ∧ R ≤ X ∧ X₁ ≤ X := by
    rcases lt_total R X₁ with h | h | h
    · exact ⟨X₁, hX11, le_of_lt h, le_refl X₁⟩
    · exact ⟨X₁, hX11, le_of_eq h, le_refl X₁⟩
    · exact ⟨R, hR, le_refl R, le_of_lt h⟩
  obtain ⟨N, hN⟩ :=
    uniformZeroBoundFrom_of_variantBounds t X₀
      (fun a b ha hab => hst a b (le_trans hX0X1 ha) hab)
      F (fun v hv => uniformZeroBoundFrom_mono hX0R (hF v hv))
  exact ⟨X₀, N, hX01, hN⟩


/-! ## §6 — a variant *can* be eventually zero while the node is not

§5 left this open. It is settled, **negatively**, by an explicit tree — and the consequence lands on
§4's convenience corollary.

```
witInner = eml (const 0) (const 1)          value  exp 0 − log 1     = 1
witB     = eml witInner (const (exp 1))     value  exp 1 − log(e)    = exp 1 − 1
witT     = eml (const 0) witB               value  1 − log (exp 1 − 1)   ≠ 0
witV     = eml (const 0) (eml witInner (const 1))
                                            value  1 − log (exp 1)   = 0
```

`witV` is `witT` with `witB`'s right child clamped to `const 1`, so it is a variant. Its value is
identically `0`; `witT`'s never is, because `log (exp 1 − 1) = 1` would force `exp 1 − 1 = exp 1`.

**Reachability is what separates them.** `witV` arises only by clamping at a node whose log argument
is the constant `exp 1 > 0` — a node `declamp` never clamps. So the identically-zero variant is in
the list but is never produced, which is exactly why
`uniformZeroBoundFrom_of_reachableBounds` is the right form and the all-variants corollary is not. -/

/-- `exp 0 − log 1 = 1`. -/
noncomputable def witInner : EMLTree := EMLTree.eml (EMLTree.const 0) (EMLTree.const 1)

/-- `exp 1 − log (exp 1) = exp 1 − 1`. -/
noncomputable def witB : EMLTree := EMLTree.eml witInner (EMLTree.const (exp 1))

/-- The node: value `1 − log (exp 1 − 1)`, never zero. -/
noncomputable def witT : EMLTree := EMLTree.eml (EMLTree.const 0) witB

/-- The variant: value identically `0`. -/
noncomputable def witV : EMLTree :=
  EMLTree.eml (EMLTree.const 0) (EMLTree.eml witInner (EMLTree.const 1))

private theorem witInner_eval (x : Real) : witInner.eval x = 1 := by
  show exp (0 : Real) - log (1 : Real) = 1
  rw [log_one, exp_zero]; mach_ring

private theorem exp_one_sub_one_pos : (0 : Real) < exp 1 - 1 := by
  have h := one_lt_exp_one_wit
  have v := add_lt_add_left h (-(1 : Real))
  have l : -(1 : Real) + 1 = 0 := by mach_ring
  have r : -(1 : Real) + exp 1 = exp 1 - 1 := by mach_ring
  rw [l, r] at v; exact v

private theorem witB_eval (x : Real) : witB.eval x = exp 1 - 1 := by
  show exp (witInner.eval x) - log (exp 1) = exp 1 - 1
  rw [witInner_eval x, log_exp]

/-- **The variant is identically zero.** -/
theorem witV_eval_zero (x : Real) : witV.eval x = 0 := by
  show exp (0 : Real) - log (exp (witInner.eval x) - log (1 : Real)) = 0
  rw [witInner_eval x, log_one, exp_zero,
    show exp (1 : Real) - (0 : Real) = exp 1 from by mach_ring, log_exp]
  mach_ring

/-- **The node never is.** `log (exp 1 − 1) = 1` would force `exp 1 − 1 = exp 1`. -/
theorem witT_eval_ne_zero (x : Real) : witT.eval x ≠ 0 := by
  intro h
  have h' : exp (0 : Real) - log (witB.eval x) = 0 := h
  rw [witB_eval x, exp_zero] at h'
  have hlog : log (exp 1 - 1) = 1 := by
    have e : (1 : Real) - log (exp 1 - 1) + log (exp 1 - 1) = 1 := by mach_ring
    rw [h'] at e
    have e2 : (0 : Real) + log (exp 1 - 1) = log (exp 1 - 1) := by mach_ring
    rw [e2] at e
    exact e
  have hel := exp_log exp_one_sub_one_pos
  rw [hlog] at hel
  -- hel : exp 1 = exp 1 - 1
  have e3 : exp (1 : Real) - (exp 1 - 1) = 1 := by mach_ring
  rw [← hel] at e3
  have e4 : exp (1 : Real) - exp 1 = 0 := by mach_ring
  rw [e4] at e3
  exact zero_ne_one_ax e3

/-- `witV` really is a variant of `witT`: clamp `witB`'s right child, keep everything else. -/
theorem witV_mem_variants : witV ∈ declampVariants witT := by
  have hinner : witInner ∈ declampVariants witInner := by
    simp [declampVariants, witInner]
  have hB : EMLTree.eml witInner (EMLTree.const 1) ∈ declampVariants witB := by
    rw [show declampVariants witB
          = (declampVariants witInner).flatMap (fun v1 =>
              (declampVariants (EMLTree.const (exp 1))).map (fun v2 => EMLTree.eml v1 v2)
                ++ [EMLTree.eml v1 (EMLTree.const 1)]) from rfl]
    exact List.mem_flatMap.mpr ⟨witInner, hinner, List.mem_append.mpr (Or.inr (by simp))⟩
  rw [show declampVariants witT
        = (declampVariants (EMLTree.const 0)).flatMap (fun v1 =>
            (declampVariants witB).map (fun v2 => EMLTree.eml v1 v2)
              ++ [EMLTree.eml v1 (EMLTree.const 1)]) from rfl]
  refine List.mem_flatMap.mpr ⟨EMLTree.const 0, by simp [declampVariants], ?_⟩
  exact List.mem_append.mpr
    (Or.inl (List.mem_map.mpr ⟨EMLTree.eml witInner (EMLTree.const 1), hB, rfl⟩))

/-- **The question §5 left open, settled negatively.** A variant can be eventually zero — indeed
identically zero — while the node it came from never vanishes. So a node's non-vanishing does **not**
transfer to its variants, and per-variant demands cannot be conditioned on the node alone. -/
theorem variant_can_be_evZero :
    ∃ t v : EMLTree, v ∈ declampVariants t ∧ EvZeroF v.eval ∧ ¬ EvZeroF t.eval := by
  refine ⟨witT, witV, witV_mem_variants, ⟨1, le_refl 1, fun x _ => witV_eval_zero x⟩, ?_⟩
  rintro ⟨Y, _, hz⟩
  exact witT_eval_ne_zero Y (hz Y (le_refl Y))

/-- **And therefore the all-variants hypothesis is unsatisfiable for `witT`.** It demands a bound for
`witV`, which is identically zero and so is not eventually non-vanishing. The reachable form
(`uniformZeroBoundFrom_of_reachableBounds`) never asks for it: `witV` arises only by clamping at a
node whose log argument is the constant `exp 1 > 0`, which `declamp` never clamps. -/
theorem variantBounds_hypothesis_unsatisfiable :
    ¬ ∃ F : EMLTree → Nat, ∀ v ∈ declampVariants witT, UniformZeroBoundFrom v.eval 1 (F v) := by
  rintro ⟨F, hF⟩
  obtain ⟨Y, hY1, hne⟩ := eventually_nonzero_of_uniformZeroBoundFrom (hF witV witV_mem_variants)
  exact hne Y (le_refl Y) (witV_eval_zero Y)

/-! ## §5 — discrimination

Two checks: the reduction fires on something, and the naive unconditioned demand is false. -/

/-- **It fires.** `var` has a single variant, itself, and `x` has no zeros at or beyond `1`, so the
reduction returns a bound for `var` — a tree with a genuine value, not a degenerate one. -/
theorem variantBounds_specimen :
    ∃ N : Nat, UniformZeroBoundFrom (EMLTree.var).eval 1 N := by
  refine uniformZeroBoundFrom_of_variantBounds EMLTree.var 1
    (fun _ _ _ _ => True.intro) (fun _ => 0) (fun v hv => ?_)
  have hv' : v = EMLTree.var := by simpa [declampVariants] using hv
  subst hv'
  intro a b hRa _ zeros _ hmem
  cases zeros with
  | nil => exact Nat.le_refl 0
  | cons z _ =>
      exfalso
      obtain ⟨haz, _, hz0⟩ := hmem z List.mem_cons_self
      have h1 : (1 : Real) < z := lt_of_le_of_lt hRa haz
      have : (0 : Real) < z := lt_trans_ax zero_lt_one_ax h1
      rw [show (EMLTree.var).eval z = z from rfl] at hz0
      rw [hz0] at this
      exact lt_irrefl_ax 0 this

/-- If nothing is clamped, `declamp` is the identity. -/
theorem declamp_eq_self_of_logArgPos (t : EMLTree) (a b : Real) (h : LogArgPos t a b) :
    declamp t a b = t := by
  induction t with
  | const c => rfl
  | var => rfl
  | eml t1 t2 ih1 ih2 =>
      obtain ⟨h1, h2, hpos⟩ := h
      rw [show declamp (EMLTree.eml t1 t2) a b
            = EMLTree.eml (declamp t1 a b) (declamp t2 a b) from by
          simp only [declamp, if_pos hpos]]
      rw [ih1 h1, ih2 h2]

/-- `exp ∘ exp ∘ t`'s log arguments are the constant `1` and its own subtree's, all positive. -/
theorem logArgPos_expExpTree (t : EMLTree) (a b : Real) (h : LogArgPos t a b) :
    LogArgPos (expExpTree t) a b :=
  ⟨⟨h, True.intro, fun _ _ _ => zero_lt_one_ax⟩, True.intro, fun _ _ _ => zero_lt_one_ax⟩

/-- **And the naive demand is false.** `expExpTree A` makes the node identically zero, that node is
its own variant (nothing in it is clamped), and an identically-zero function is not eventually
non-vanishing — so by `eventually_nonzero_of_uniformZeroBoundFrom` it admits no bound on any ray.

A per-variant demand must therefore be conditioned, which is why §4 is a reduction and not an
obligation. -/
theorem not_all_variants_bounded :
    ¬ (∀ t : EMLTree, ∀ v ∈ declampVariants t, ∃ (R : Real) (N : Nat),
        1 ≤ R ∧ UniformZeroBoundFrom v.eval R N) := by
  intro h
  have hlap : LogArgPos (EMLTree.eml (EMLTree.const 0) (expExpTree (EMLTree.const 0))) 1 (1 + 1) :=
    ⟨True.intro, logArgPos_expExpTree (EMLTree.const 0) 1 (1 + 1) True.intro,
      fun x _ _ => expExpTree_pos (EMLTree.const 0) x⟩
  have hmem : EMLTree.eml (EMLTree.const 0) (expExpTree (EMLTree.const 0))
      ∈ declampVariants (EMLTree.eml (EMLTree.const 0) (expExpTree (EMLTree.const 0))) := by
    have hd := declamp_mem_variants
      (EMLTree.eml (EMLTree.const 0) (expExpTree (EMLTree.const 0))) 1 (1 + 1)
    rwa [declamp_eq_self_of_logArgPos _ 1 (1 + 1) hlap] at hd
  obtain ⟨R, N, hR1, hb⟩ := h _ _ hmem
  obtain ⟨Y, hY1, hne⟩ := eventually_nonzero_of_uniformZeroBoundFrom hb
  exact hne Y (le_refl Y) (expExpTree_node_eq_zero (EMLTree.const 0) Y)

end MachLib
