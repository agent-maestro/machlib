import MachLib.EMLBasisEquivalence

/-!
# `F`-query complexity, and a two-query global decoder

Saying the decoder "costs three `F` evaluations" was never well defined. A syntax tree counts
`F(u)` twice in `EF u`; an evaluator with common-subexpression sharing queries it once. The two
measures do not differ by a constant — they differ **exponentially** in the depth of the term — so
the count has to be pinned down before anything is called minimal.

Two measures, both defined here:

* `fOcc T` — occurrences of `F` in the **syntax tree**.
* `fDepth T` — maximum **nesting** depth of `F`.
* `FQueriesLe T n` — the arguments at which `T` applies `F` are covered by a list of length `≤ n`:
  an upper bound on the number of **distinct** queries, i.e. the evaluation-DAG count.

## The two-query decoder

`EFall` (the first global decoder) queries `F` at six distinct arguments, because it routes through
`EF`, which needs its argument **positive** and spends three queries on the dilation identity.

That was the wrong instrument again. Query `F` at a **negative** argument and the totalised
logarithm is `0`, so `F` reports the exponential alone:

```
F(y) = exp y      for every y ≤ 0
```

Both `p(u) = u + u² + 1` and `q(u) = u² + 1` are positive for every real `u`, so `−p` and `−q` are
negative for every real `u`, and `p − q = u`. Hence

```
exp u = F(−q(u)) / F(−p(u))
```

for every real `u`: **two queries, no dilation identity, no positivity hypothesis, and no case
split.** `log₀ u = F(u) − exp u` costs one more.

The totalisation is not being worked around here — it is being *used*. `F` is a mixed signal, and
evaluating it where one component vanishes is a cheaper demixing than the dilation calculus.
-/

namespace MachLib

open Real

/-! ## The measures -/

/-- Occurrences of `F` in the syntax tree. -/
def fOcc : FTerm → Nat
  | .const _ => 0
  | .var     => 0
  | .add a b => fOcc a + fOcc b
  | .sub a b => fOcc a + fOcc b
  | .mul a b => fOcc a + fOcc b
  | .div a b => fOcc a + fOcc b
  | .F a     => 1 + fOcc a

/-- Maximum nesting depth of `F`. -/
def fDepth : FTerm → Nat
  | .const _ => 0
  | .var     => 0
  | .add a b => max (fDepth a) (fDepth b)
  | .sub a b => max (fDepth a) (fDepth b)
  | .mul a b => max (fDepth a) (fDepth b)
  | .div a b => max (fDepth a) (fDepth b)
  | .F a     => 1 + fDepth a

/-- Every argument at which `T` applies `F`, with multiplicity. -/
def fArgs : FTerm → List FTerm
  | .const _ => []
  | .var     => []
  | .add a b => fArgs a ++ fArgs b
  | .sub a b => fArgs a ++ fArgs b
  | .mul a b => fArgs a ++ fArgs b
  | .div a b => fArgs a ++ fArgs b
  | .F a     => a :: fArgs a

/-- **The evaluation-DAG measure.** `T` needs at most `n` distinct `F`-queries: some list of length
at most `n` contains every argument at which `T` applies `F`. Stated as a cover rather than as
`dedup.length` so that no decidable equality on `Real` is needed. -/
def FQueriesLe (T : FTerm) (n : Nat) : Prop :=
  ∃ L : List FTerm, L.length ≤ n ∧ ∀ a ∈ fArgs T, a ∈ L

/-! ## The two-query global decoder -/

/-- `F` reports the exponential alone wherever its argument is non-positive. -/
theorem Fbasis_of_nonpos {y : Real} (hy : y ≤ 0) : Fbasis y = exp y := by
  unfold Fbasis; rw [log_nonpos hy]; mach_ring

private theorem sub_nonpos_of_pos {z : Real} (hz : 0 < z) : (0 : Real) - z ≤ 0 := by
  have v := add_lt_add_left hz (-z)
  have l : -z + 0 = -z := by mach_ring
  have r : -z + z = 0 := by mach_ring
  rw [l, r] at v
  have e : (0 : Real) - z = -z := by mach_ring
  rw [e]; exact le_of_lt v

/-- `−(u² + 1)`, negative for every real `u`. -/
noncomputable def FTerm.negQ (u : FTerm) : FTerm :=
  FTerm.sub (FTerm.const 0) (FTerm.add (FTerm.mul u u) (FTerm.const 1))

/-- `−(u + u² + 1)`, negative for every real `u`. -/
noncomputable def FTerm.negP (u : FTerm) : FTerm :=
  FTerm.sub (FTerm.const 0) (FTerm.add (FTerm.add u (FTerm.mul u u)) (FTerm.const 1))

/-- **The two-query global exponential decoder**: `exp u = F(−q(u)) / F(−p(u))`. -/
noncomputable def FTerm.EFneg (u : FTerm) : FTerm :=
  FTerm.div (FTerm.F (FTerm.negQ u)) (FTerm.F (FTerm.negP u))

theorem FTerm.EFneg_eval (u : FTerm) (x : Real) :
    FTerm.eval (FTerm.EFneg u) x = exp (FTerm.eval u x) := by
  have hq : (0 : Real) < FTerm.eval u x * FTerm.eval u x + 1 :=
    add_pos_of_nonneg_of_pos (sq_nonneg _) zero_lt_one_ax
  have hp : (0 : Real) < FTerm.eval u x + FTerm.eval u x * FTerm.eval u x + 1 := by
    have hq2 := quad_pos (FTerm.eval u x)
    have e : FTerm.eval u x * FTerm.eval u x + FTerm.eval u x + 1
        = FTerm.eval u x + FTerm.eval u x * FTerm.eval u x + 1 := by mach_ring
    rw [e] at hq2; exact hq2
  show Fbasis (0 - (FTerm.eval u x * FTerm.eval u x + 1))
      / Fbasis (0 - (FTerm.eval u x + FTerm.eval u x * FTerm.eval u x + 1))
      = exp (FTerm.eval u x)
  rw [Fbasis_of_nonpos (sub_nonpos_of_pos hq), Fbasis_of_nonpos (sub_nonpos_of_pos hp)]
  refine div_of_eq_mul (ne_of_gt (exp_pos _)) ?_
  rw [← exp_add]
  have e : 0 - (FTerm.eval u x + FTerm.eval u x * FTerm.eval u x + 1) + FTerm.eval u x
      = 0 - (FTerm.eval u x * FTerm.eval u x + 1) := by mach_ring
  rw [e]

/-- **The three-query global logarithm decoder.** -/
noncomputable def FTerm.LFneg (u : FTerm) : FTerm := FTerm.sub (FTerm.F u) (FTerm.EFneg u)

theorem FTerm.LFneg_eval (u : FTerm) (x : Real) :
    FTerm.eval (FTerm.LFneg u) x = log (FTerm.eval u x) := by
  show Fbasis (FTerm.eval u x) - FTerm.eval (FTerm.EFneg u) x = log (FTerm.eval u x)
  rw [FTerm.EFneg_eval u x]
  exact decoder_log (FTerm.eval u x)

/-- The cheap compiler: the same translation, with the two-query decoder in place of the six-query
one. -/
noncomputable def toFTermFast : EMLTree → FTerm
  | .const c => FTerm.const c
  | .var     => FTerm.var
  | .eml a b => FTerm.sub (FTerm.EFneg (toFTermFast a)) (FTerm.LFneg (toFTermFast b))

theorem toFTermFast_eval : ∀ (t : EMLTree) (x : Real),
    FTerm.eval (toFTermFast t) x = t.eval x := by
  intro t
  induction t with
  | const c => intro _; rfl
  | var => intro _; rfl
  | eml a b iha ihb =>
      intro x
      show FTerm.eval (FTerm.EFneg (toFTermFast a)) x
          - FTerm.eval (FTerm.LFneg (toFTermFast b)) x = exp (a.eval x) - log (b.eval x)
      rw [FTerm.EFneg_eval _ x, FTerm.LFneg_eval _ x, iha x, ihb x]

/-! ## Cost: the two measures diverge -/

theorem fOcc_EFneg (u : FTerm) : fOcc (FTerm.EFneg u) = 2 + 5 * fOcc u := by
  simp only [FTerm.EFneg, FTerm.negQ, FTerm.negP, fOcc]
  omega

/-- The first global decoder, for comparison. **Twenty** per level against five: in the tree measure
the two decoders differ by a factor that compounds with depth. -/
theorem fOcc_EFall (u : FTerm) : fOcc (FTerm.EFall u) = 8 + 20 * fOcc u := by
  simp only [FTerm.EFall, FTerm.EF, fOcc]
  omega

theorem fDepth_EFneg (u : FTerm) : fDepth (FTerm.EFneg u) = 1 + fDepth u := by
  simp only [FTerm.EFneg, FTerm.negQ, FTerm.negP, fDepth]
  omega

theorem fDepth_LFneg (u : FTerm) : fDepth (FTerm.LFneg u) = 1 + fDepth u := by
  simp only [FTerm.LFneg, fDepth, fDepth_EFneg]
  omega

/-- **The change of basis is depth-preserving.** `F`-nesting depth of the compiled term equals EML
depth of the source, exactly — no overhead, no constant factor.

So the entire cost of the translation sits in query *count*, not in query *depth*: the decoders
never nest `F` inside `F`. -/
theorem fDepth_toFTermFast : ∀ t : EMLTree, fDepth (toFTermFast t) = t.depth := by
  intro t
  induction t with
  | const c => rfl
  | var => rfl
  | eml a b iha ihb =>
      simp only [toFTermFast, fDepth, fDepth_EFneg, fDepth_LFneg, iha, ihb, EMLTree.depth]
      omega

/-! ## The DAG measure: how many *distinct* queries -/

theorem FQueriesLe_mono {T : FTerm} {m n : Nat} (h : FQueriesLe T m) (hmn : m ≤ n) :
    FQueriesLe T n := by
  obtain ⟨L, hL, hm⟩ := h
  exact ⟨L, Nat.le_trans hL hmn, hm⟩

private theorem FQueriesLe_sub {A B : FTerm} {m n : Nat}
    (hA : FQueriesLe A m) (hB : FQueriesLe B n) : FQueriesLe (FTerm.sub A B) (m + n) := by
  obtain ⟨LA, hLA, hA'⟩ := hA
  obtain ⟨LB, hLB, hB'⟩ := hB
  refine ⟨LA ++ LB, by rw [List.length_append]; omega, ?_⟩
  intro a ha
  simp only [fArgs, List.mem_append] at ha ⊢
  rcases ha with h | h
  · exact Or.inl (hA' a h)
  · exact Or.inr (hB' a h)

private theorem fArgs_negQ {u a : FTerm} (h : a ∈ fArgs (FTerm.negQ u)) : a ∈ fArgs u := by
  simp only [FTerm.negQ, fArgs, List.nil_append, List.append_nil, List.mem_append] at h
  rcases h with h | h <;> exact h

private theorem fArgs_negP {u a : FTerm} (h : a ∈ fArgs (FTerm.negP u)) : a ∈ fArgs u := by
  simp only [FTerm.negP, fArgs, List.nil_append, List.append_nil, List.mem_append] at h
  rcases h with h | h | h <;> exact h

private theorem fArgs_EFneg {u a : FTerm} (h : a ∈ fArgs (FTerm.EFneg u)) :
    a = FTerm.negQ u ∨ a = FTerm.negP u ∨ a ∈ fArgs u := by
  have h' : a ∈ (FTerm.negQ u :: fArgs (FTerm.negQ u))
      ++ (FTerm.negP u :: fArgs (FTerm.negP u)) := h
  rcases List.mem_append.mp h' with hx | hx
  · rcases List.mem_cons.mp hx with he | hm
    · exact Or.inl he
    · exact Or.inr (Or.inr (fArgs_negQ hm))
  · rcases List.mem_cons.mp hx with he | hm
    · exact Or.inr (Or.inl he)
    · exact Or.inr (Or.inr (fArgs_negP hm))

private theorem fArgs_LFneg {u a : FTerm} (h : a ∈ fArgs (FTerm.LFneg u)) :
    a = u ∨ a = FTerm.negQ u ∨ a = FTerm.negP u ∨ a ∈ fArgs u := by
  have h' : a ∈ (u :: fArgs u) ++ fArgs (FTerm.EFneg u) := h
  rcases List.mem_append.mp h' with hx | hx
  · rcases List.mem_cons.mp hx with he | hm
    · exact Or.inl he
    · exact Or.inr (Or.inr (Or.inr hm))
  · rcases fArgs_EFneg hx with he | he | hm
    · exact Or.inr (Or.inl he)
    · exact Or.inr (Or.inr (Or.inl he))
    · exact Or.inr (Or.inr (Or.inr hm))

/-- **Two distinct queries per exponential**, on top of whatever the argument already costs. -/
theorem FQueriesLe_EFneg {u : FTerm} {n : Nat} (h : FQueriesLe u n) :
    FQueriesLe (FTerm.EFneg u) (n + 2) := by
  obtain ⟨L, hL, hm⟩ := h
  refine ⟨FTerm.negQ u :: FTerm.negP u :: L, by simp only [List.length_cons]; omega, ?_⟩
  intro a ha
  rcases fArgs_EFneg ha with he | he | hx
  · exact List.mem_cons.mpr (Or.inl he)
  · exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl he)))
  · exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (hm a hx))))

/-- **Three per logarithm** — the argument itself, plus the exponential's two. -/
theorem FQueriesLe_LFneg {u : FTerm} {n : Nat} (h : FQueriesLe u n) :
    FQueriesLe (FTerm.LFneg u) (n + 3) := by
  obtain ⟨L, hL, hm⟩ := h
  refine ⟨u :: FTerm.negQ u :: FTerm.negP u :: L, by simp only [List.length_cons]; omega, ?_⟩
  intro a ha
  rcases fArgs_LFneg ha with he | he | he | hx
  · exact List.mem_cons.mpr (Or.inl he)
  · exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl he)))
  · exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr
      (List.mem_cons.mpr (Or.inl he)))))
  · exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr
      (List.mem_cons.mpr (Or.inr (hm a hx))))))

/-- `eml` nodes in an EML tree. -/
def emlNodes : EMLTree → Nat
  | .const _ => 0
  | .var     => 0
  | .eml a b => 1 + emlNodes a + emlNodes b

/-- **Linear simulation overhead in the DAG measure.** The compiled term needs at most `5` distinct
`F`-queries per `eml` node of the source — two for the node's exponential, three for its logarithm.

Contrast `fOcc`: in the *syntax-tree* measure the same translation multiplies by `5` at every level,
so the tree count is exponential in depth while the DAG count is linear in size. That is the whole
reason the measure had to be fixed before anything could be called minimal. -/
theorem FQueriesLe_toFTermFast : ∀ t : EMLTree, FQueriesLe (toFTermFast t) (5 * emlNodes t) := by
  intro t
  induction t with
  | const c => exact ⟨[], Nat.le_refl 0, fun a ha => absurd ha (by simp [toFTermFast, fArgs])⟩
  | var => exact ⟨[], Nat.le_refl 0, fun a ha => absurd ha (by simp [toFTermFast, fArgs])⟩
  | eml a b iha ihb =>
      refine FQueriesLe_mono (FQueriesLe_sub (FQueriesLe_EFneg iha) (FQueriesLe_LFneg ihb)) ?_
      simp only [emlNodes]
      omega

/-! ## What the change of basis does to a specific function

The translation is depth-preserving, so a depth-4 EML tree compiles to an `L_F` term of `F`-depth 4.
But the *minimum over representations* is a different quantity, and it is not preserved at all. -/

/-- **`x + 1`: minimum depth 4 in one basis, zero transcendental calls in the other.**

Three facts in one statement:

* the EML witness has depth `4`, and its compiled image has `F`-depth `4` — the translation adds
  nothing;
* **no** EML tree of depth `≤ 3` computes `x + 1` on `(0, ∞)` (`x_plus_one_not_depth_le_three`);
* in `L_F` the function is `x + 1`, with `F`-depth `0` and **zero** distinct `F`-queries — and on
  *all* of `Real`, not merely `(0, ∞)`.

So basis change preserves *compiled* depth exactly while collapsing *minimal* depth from 4 to 0.
"Exact depth is a property of the presentation" with the two presentations written side by side. -/
theorem x_plus_one_basis_gap :
    (∃ t : EMLTree, t.depth = 4 ∧ fDepth (toFTermFast t) = 4
        ∧ ∀ x : Real, 0 < x → t.eval x = x + 1)
    ∧ (∀ t : EMLTree, t.depth ≤ 3 → (∀ x : Real, 0 < x → t.eval x = x + 1) → False)
    ∧ (∃ T : FTerm, fDepth T = 0 ∧ FQueriesLe T 0 ∧ ∀ x : Real, FTerm.eval T x = x + 1) := by
  refine ⟨?_, x_plus_one_depth_exact_four.1, ?_⟩
  · obtain ⟨t, htd, hte⟩ := x_plus_one_depth_exact_four.2
    exact ⟨t, htd, by rw [fDepth_toFTermFast, htd], hte⟩
  · refine ⟨FTerm.add FTerm.var (FTerm.const 1), by simp [fDepth], ?_, fun _ => rfl⟩
    exact ⟨[], Nat.le_refl 0, fun a ha => absurd ha (by simp [fArgs])⟩

/-! ## Where minimality stands

Two queries decode `exp` globally. **One is open**, and deliberately left open.

The reason to look for a one-query decoder is that the argument of `F` is free: any rational
function of `u` may be used. The reason to expect none is narrower than it first appears. For
`exp u` to be a rational function of `F(w)` and `u`, the exponential parts must be rationally
related, which pushes `w` towards affine `a·u + b` — and no affine `w` is non-positive for *every*
`u`, so `F(w)` cannot report the exponential alone. Where `w` is positive, `F(w) = exp w + log w`
carries both components, and separating them is what the dilation calculus needed three queries for.

**That is a reason to look, not a proof.** It assumes the decoder is rational in `F(w)` and `u`, and
assumes rational relatedness forces affinity; neither is established here. This arc has produced
three impossibility guesses in one day and refuted all three, so the sharper statement — *one query
does not suffice* — is recorded as a conjecture with no supporting theorem.
-/

/-! ## ⚠ `C_k` is measure-dependent from `k = 1` onward

`fOcc` counts syntax-tree occurrences; `FQueriesLe` bounds distinct evaluation-DAG queries. They are
**not** interchangeable, and the divergence starts immediately, not at some large `k`.

`F(x)·F(x)` needs two `F` nodes in a tree — `FTerm` has no sharing — while an evaluator queries the
oracle once. So the tree-`C₁` and DAG-`C₁` **function classes differ**, and every `C_k` statement
must name its measure.

Everything in this development uses `fOcc`, the tree measure. Where the two agree the results
transfer: `fOcc T = 0 ↔ fArgs T = []` (`fOcc_zero_iff_fArgs_nil`), so `C₀` is the same class in both,
and the witnesses used for `q_F(exp) = 1` and `C₀ ⊊ C₁` have one `F` node each, hence the same count
either way. The general hierarchy does not transfer, and `fOcc_EFall` versus `FQueriesLe_toFTermFast`
already shows the gap is exponential in depth. -/

end MachLib
