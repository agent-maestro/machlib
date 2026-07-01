import MachLib.ChainExp2CdegInv
import MachLib.ChainExp2YPIT

/-!
# `cdegY1` arc, brick 1 — the nested canonical-zero test and its eval-invariance

The depth-3 termination needs a FULLY eval-invariant depth-2 measure (the depth-2 `chain2MeasureCanon`
has a *syntactic* `degreeY₁` first component — not eval-invariant). That measure's first component must
be a canonical `y₁`-degree `cdegY1`, whose canon-zero test on `y₁`-coefficients (polys in `x, y₀`) is
NESTED one level deeper than the depth-2 `coeffCanonZeroB` (which only tests the `x`-part at `y=0`):

  `coeffCanonZeroB1 c` = "every `y₀`-coefficient of `c` is `x`-canonically-zero"
                       = "`c` vanishes on the chain `(x, eˣ)` for all `x`".

This brick builds that test and proves it eval-invariant (via the `y`-PIT at index `⟨0⟩` + the depth-2
`coeffCanonZeroB` eval-invariance). It mirrors `ChainExp2CdegInv.coeffCanonZeroB_eq_of_eval_eq` one level
up. `ChainExp2*` untouched (Path B); no `sorry`.
-/

namespace MachLib.IterExpDepth3CdegY1

open MachLib.Real
open MachLib.MultiPolyMod
open MachLib.MultiPolyMod.MultiPoly
open MachLib.PolynomialCanonical
open MachLib.PfaffianChainMod.PfaffianFn
open MachLib.MultiPolyReconstruct
open MachLib.ChainExp2CanonMeasure
open MachLib.ChainExp2CdegInv
open MachLib.ChainExp2YPIT

/-- The `y=0` env with `y₀` set to `y0` (slot 0), everything else 0. -/
private noncomputable def env0 (y0 : Real) : Fin 2 → Real :=
  fun i => if i = (⟨0, by omega⟩ : Fin 2) then y0 else 0

/-- **Nested canon-zero test.** `c` is canonically zero as an `x, y₀`-poly iff all its `y₀`-coefficients
are `x`-canonically-zero (`coeffCanonZeroB`). -/
noncomputable def coeffCanonZeroB1 (c : MultiPoly 2) : Bool :=
  (yCoeffsAt (⟨0, by omega⟩ : Fin 2) c).all coeffCanonZeroB

/-- **Characterization.** `coeffCanonZeroB1 c = true` iff `c` vanishes at `(x, y₀, 0)` for all `x, y₀`
(i.e. `c`'s `y₁ = 0` slice is the zero `x, y₀`-poly). -/
theorem coeffCanonZeroB1_true_iff (c : MultiPoly 2) :
    coeffCanonZeroB1 c = true ↔ ∀ (x y0 : Real), MultiPoly.eval c x (env0 y0) = 0 := by
  unfold coeffCanonZeroB1
  rw [List.all_eq_true]
  constructor
  · -- all y₀-coeffs canon-zero ⇒ c vanishes at (x, y₀, 0).
    intro hall x y0
    have hmap : (yCoeffsAt (⟨0, by omega⟩ : Fin 2) c).map (fun c' => MultiPoly.eval c' x (env0 y0))
              = (yCoeffsAt (⟨0, by omega⟩ : Fin 2) c).map (fun _ => (0 : Real)) := by
      apply List.map_congr_left
      intro e he
      have hcz : coeffCanonZeroB e = true := hall e he
      have hz0 : ∀ w : Real, MultiPoly.eval e w (fun _ => 0) = 0 := by
        have := (canonZero_iff_eval_zero_at_0 e).mp
        unfold coeffCanonZeroB at hcz
        exact this (of_decide_eq_true hcz)
      -- e is y₀-free, so eval e at env0 = eval e at 0-env.
      have hyfree : MultiPoly.degreeY (⟨0, by omega⟩ : Fin 2) e = 0 :=
        yCoeffsAt_entries_degreeY_zero (⟨0, by omega⟩ : Fin 2) c e he
      have hoff : ∀ j : Fin 2, j ≠ (⟨0, by omega⟩ : Fin 2) → env0 y0 j = (fun _ => (0 : Real)) j := by
        intro j hj; show (if j = (⟨0, by omega⟩ : Fin 2) then y0 else 0) = 0; rw [if_neg hj]
      rw [eval_eq_of_env_agree_off (⟨0, by omega⟩ : Fin 2) e x (env0 y0) (fun _ => 0) hoff hyfree, hz0]
    have hz : ∀ (L : List (MultiPoly 2)) (w : Real),
        evalCoeffs (List.map (fun _ => (0 : Real)) L) w = 0 := by
      intro L w
      induction L with
      | nil => rw [List.map_nil, evalCoeffs_nil]
      | cons a as ih =>
        rw [List.map_cons, evalCoeffs_cons, ih, MachLib.Real.mul_zero, MachLib.Real.add_zero]
    have hbridge := listEvalN_eq_evalCoeffs_map (⟨0, by omega⟩ : Fin 2)
      (yCoeffsAt (⟨0, by omega⟩ : Fin 2) c) x (env0 y0)
    rw [eval_yCoeffsAt (⟨0, by omega⟩ : Fin 2) c x (env0 y0)] at hbridge
    rw [hbridge, hmap, hz]
  · -- c vanishes at (x, y₀, 0) ⇒ all y₀-coeffs canon-zero.
    intro hvanish e he
    have hyfree : MultiPoly.degreeY (⟨0, by omega⟩ : Fin 2) e = 0 :=
      yCoeffsAt_entries_degreeY_zero (⟨0, by omega⟩ : Fin 2) c e he
    -- coeffCanonZeroB e ⟺ ∀x, eval e x 0-env = 0.
    have hgoal : ∀ x : Real, MultiPoly.eval e x (fun _ => 0) = 0 := by
      intro x
      have hall : ∀ y : Real,
          evalCoeffs ((yCoeffsAt (⟨0, by omega⟩ : Fin 2) c).map
            (fun c' => MultiPoly.eval c' x (fun _ => 0))) y = 0 := by
        intro y
        have hmapy : (yCoeffsAt (⟨0, by omega⟩ : Fin 2) c).map
              (fun c' => MultiPoly.eval c' x (env0 y))
            = (yCoeffsAt (⟨0, by omega⟩ : Fin 2) c).map (fun c' => MultiPoly.eval c' x (fun _ => 0)) := by
          apply List.map_congr_left
          intro e' he'
          have hyf' : MultiPoly.degreeY (⟨0, by omega⟩ : Fin 2) e' = 0 :=
            yCoeffsAt_entries_degreeY_zero (⟨0, by omega⟩ : Fin 2) c e' he'
          have hoff : ∀ j : Fin 2, j ≠ (⟨0, by omega⟩ : Fin 2) → env0 y j = (fun _ => (0 : Real)) j := by
            intro j hj; show (if j = (⟨0, by omega⟩ : Fin 2) then y else 0) = 0; rw [if_neg hj]
          exact eval_eq_of_env_agree_off (⟨0, by omega⟩ : Fin 2) e' x (env0 y) (fun _ => 0) hoff hyf'
        have hbridge := listEvalN_eq_evalCoeffs_map (⟨0, by omega⟩ : Fin 2)
          (yCoeffsAt (⟨0, by omega⟩ : Fin 2) c) x (env0 y)
        rw [eval_yCoeffsAt (⟨0, by omega⟩ : Fin 2) c x (env0 y), hvanish x y] at hbridge
        rw [← hmapy]; exact hbridge.symm
      exact evalCoeffs_zero_iff_all_zero _ hall (MultiPoly.eval e x (fun _ => 0))
        (List.mem_map_of_mem _ he)
    unfold coeffCanonZeroB
    exact decide_eq_true ((canonZero_iff_eval_zero_at_0 e).mpr hgoal)

/-- **The nested canon-zero test is eval-invariant.** -/
theorem coeffCanonZeroB1_eq_of_eval_eq (c1 c2 : MultiPoly 2)
    (h : ∀ (x : Real) (env : Fin 2 → Real), MultiPoly.eval c1 x env = MultiPoly.eval c2 x env) :
    coeffCanonZeroB1 c1 = coeffCanonZeroB1 c2 := by
  have hiff : coeffCanonZeroB1 c1 = true ↔ coeffCanonZeroB1 c2 = true := by
    rw [coeffCanonZeroB1_true_iff, coeffCanonZeroB1_true_iff]
    constructor
    · intro h1 x y0; rw [← h x (env0 y0)]; exact h1 x y0
    · intro h2 x y0; rw [h x (env0 y0)]; exact h2 x y0
  cases hb1 : coeffCanonZeroB1 c1 <;> cases hb2 : coeffCanonZeroB1 c2 <;> simp_all

/-! ### `cdegY1` and its eval-invariance (mirror of the `cdegY0` list induction, one index up) -/

/-- Eval-zero polys pass the nested canon-zero test. -/
theorem coeffCanonZeroB1_true_of_eval_zero (c : MultiPoly 2)
    (h : ∀ (x : Real) (env : Fin 2 → Real), MultiPoly.eval c x env = 0) :
    coeffCanonZeroB1 c = true :=
  (coeffCanonZeroB1_true_iff c).mpr (fun x y0 => h x (env0 y0))

theorem coeffCanonZeroB1_const0 : coeffCanonZeroB1 (MultiPoly.const (0 : Real)) = true :=
  coeffCanonZeroB1_true_of_eval_zero _ (fun _ _ => rfl)

/-- From `sub p q` nested-canon-zero, `p` and `q` have equal nested canon-zero test (both determined by
their `y₁ = 0` slice). -/
theorem coeffCanonZeroB1_eq_of_sub_canonZero (p q : MultiPoly 2)
    (h : coeffCanonZeroB1 (MultiPoly.sub p q) = true) :
    coeffCanonZeroB1 p = coeffCanonZeroB1 q := by
  have hsub := (coeffCanonZeroB1_true_iff (MultiPoly.sub p q)).mp h
  have hpq : ∀ (x y0 : Real), MultiPoly.eval p x (env0 y0) = MultiPoly.eval q x (env0 y0) := by
    intro x y0
    have hz := hsub x y0
    rw [MultiPoly.eval_sub] at hz
    have hcalc : MultiPoly.eval p x (env0 y0)
        = (MultiPoly.eval p x (env0 y0) - MultiPoly.eval q x (env0 y0))
          + MultiPoly.eval q x (env0 y0) := by mach_ring
    rw [hcalc, hz]; mach_ring
  have hiff : coeffCanonZeroB1 p = true ↔ coeffCanonZeroB1 q = true := by
    rw [coeffCanonZeroB1_true_iff, coeffCanonZeroB1_true_iff]
    constructor
    · intro hp x y0; rw [← hpq x y0]; exact hp x y0
    · intro hq x y0; rw [hpq x y0]; exact hq x y0
  cases hb1 : coeffCanonZeroB1 p <;> cases hb2 : coeffCanonZeroB1 q <;> simp_all

theorem all_canonZero1_of_listSubN_nil :
    ∀ L : List (MultiPoly 2),
      (∀ c ∈ listSubN [] L, coeffCanonZeroB1 c = true) →
      ∀ c ∈ L, coeffCanonZeroB1 c = true
  | [], _ => by intro c hc; cases hc
  | q :: qs, h => by
    rw [listSubN_nil_cons] at h
    intro c hc
    rcases List.mem_cons.mp hc with hcq | hcqs
    · subst hcq
      have := coeffCanonZeroB1_eq_of_sub_canonZero (MultiPoly.const 0) c
                (h _ (List.mem_cons_self _ _))
      rw [coeffCanonZeroB1_const0] at this
      exact this.symm
    · exact all_canonZero1_of_listSubN_nil qs
        (fun d hd => h d (List.mem_cons_of_mem _ hd)) c hcqs

/-- **Main list induction** (mirror of `rdw_eq_of_listSubN`): if `listSubN L1 L2` is entrywise
nested-canon-zero, the trimmed lengths agree. -/
theorem rdw_eq_of_listSubN1 :
    ∀ (L1 L2 : List (MultiPoly 2)),
      (∀ c ∈ listSubN L1 L2, coeffCanonZeroB1 c = true) →
      (L1.reverse.dropWhile coeffCanonZeroB1).length
        = (L2.reverse.dropWhile coeffCanonZeroB1).length
  | [], L2, hsub => by
    rw [rdw_zero_of_all coeffCanonZeroB1 L2 (all_canonZero1_of_listSubN_nil L2 hsub)]
    rfl
  | p :: ps, [], hsub => by
    rw [listSubN_cons_nil] at hsub
    rw [rdw_zero_of_all coeffCanonZeroB1 (p :: ps) hsub]
    rfl
  | p :: ps, q :: qs, hsub => by
    rw [listSubN_cons_cons] at hsub
    have hpq : coeffCanonZeroB1 (MultiPoly.sub p q) = true := hsub _ (List.mem_cons_self _ _)
    have hcpq : coeffCanonZeroB1 p = coeffCanonZeroB1 q :=
      coeffCanonZeroB1_eq_of_sub_canonZero p q hpq
    have hih := rdw_eq_of_listSubN1 ps qs
      (fun c hc => hsub c (List.mem_cons_of_mem _ hc))
    rw [rdw_cons coeffCanonZeroB1 p ps, rdw_cons coeffCanonZeroB1 q qs, hcpq, hih]

/-- **Canonical `y₁`-degree.** Drop the trailing nested-canon-zero `y₁`-coefficients, `length − 1`.
The eval-invariant refinement of the syntactic `degreeY ⟨1⟩` (which counts phantom `y₁`-terms that only
cancel semantically — the source of the depth-3 recursion's eval-boundary problem). -/
noncomputable def cdegY1 (q : MultiPoly 2) : Nat :=
  ((yCoeffsAt (⟨1, by omega⟩ : Fin 2) q).reverse.dropWhile coeffCanonZeroB1).length - 1

/-- **`cdegY1` is eval-invariant** — eval-equal `MultiPoly 2`s have equal canonical `y₁`-degree. This is
what the depth-3 descent needs (the eval-equality of the dropped leading coefficient then transfers). -/
theorem cdegY1_eq_of_eval_eq (q1 q2 : MultiPoly 2)
    (h : ∀ (x : Real) (env : Fin 2 → Real), MultiPoly.eval q1 x env = MultiPoly.eval q2 x env) :
    cdegY1 q1 = cdegY1 q2 := by
  have hzero : ∀ (x : Real) (env : Fin 2 → Real),
      MultiPoly.eval (MultiPoly.sub q1 q2) x env = 0 := by
    intro x env; rw [MultiPoly.eval_sub, h x env]; mach_ring
  have hsub : ∀ c ∈ listSubN (yCoeffsAt (⟨1, by omega⟩ : Fin 2) q1)
                             (yCoeffsAt (⟨1, by omega⟩ : Fin 2) q2),
      coeffCanonZeroB1 c = true := by
    intro c hc
    apply coeffCanonZeroB1_true_of_eval_zero
    intro x env
    exact yCoeffsAt_entry_eval_zero_of_eval_zero (⟨1, by omega⟩ : Fin 2)
      (MultiPoly.sub q1 q2) hzero x env c hc
  show ((yCoeffsAt (⟨1, by omega⟩ : Fin 2) q1).reverse.dropWhile coeffCanonZeroB1).length - 1
     = ((yCoeffsAt (⟨1, by omega⟩ : Fin 2) q2).reverse.dropWhile coeffCanonZeroB1).length - 1
  rw [rdw_eq_of_listSubN1 _ _ hsub]

/-! ### `canonLcY1` (the canonical leading `y₁`-coefficient) and its eval-invariance -/

/-- From `sub p q` nested-canon-zero, `p` and `q` agree at `env0 y0` (all `x, y₀`). -/
theorem envEnv0_eq_of_sub_canonZero1 (p q : MultiPoly 2)
    (h : coeffCanonZeroB1 (MultiPoly.sub p q) = true) :
    ∀ (x y0 : Real), MultiPoly.eval p x (env0 y0) = MultiPoly.eval q x (env0 y0) := by
  have hsub := (coeffCanonZeroB1_true_iff (MultiPoly.sub p q)).mp h
  intro x y0
  have hz := hsub x y0
  rw [MultiPoly.eval_sub] at hz
  have hcalc : MultiPoly.eval p x (env0 y0)
      = (MultiPoly.eval p x (env0 y0) - MultiPoly.eval q x (env0 y0)) + MultiPoly.eval q x (env0 y0) := by
    mach_ring
  rw [hcalc, hz]; mach_ring

/-- **`canonLcY1` eval-invariance at `env0` (main headD induction, mirror of
`rdwHead_eval0_eq_of_listSubN`).** If `listSubN L1 L2` is entrywise nested-canon-zero, the `headD`s of
the two trimmed reversed lists agree at `env0 y0` for all `x, y₀`. -/
theorem rdwHead_envEnv0_eq_of_listSubN1 :
    ∀ (L1 L2 : List (MultiPoly 2)),
      (∀ c ∈ listSubN L1 L2, coeffCanonZeroB1 c = true) →
      ∀ (x y0 : Real),
        MultiPoly.eval ((L1.reverse.dropWhile coeffCanonZeroB1).headD (MultiPoly.const 0)) x (env0 y0)
        = MultiPoly.eval ((L2.reverse.dropWhile coeffCanonZeroB1).headD (MultiPoly.const 0)) x (env0 y0)
  | [], L2, hsub => by
    intro x y0
    rw [dropWhile_all coeffCanonZeroB1 L2.reverse
      (fun c hc => all_canonZero1_of_listSubN_nil L2 hsub c (List.mem_reverse.mp hc))]
    rfl
  | p :: ps, [], hsub => by
    intro x y0
    rw [listSubN_cons_nil] at hsub
    rw [dropWhile_all coeffCanonZeroB1 (p :: ps).reverse
      (fun c hc => hsub c (List.mem_reverse.mp hc))]
    rfl
  | p :: ps, q :: qs, hsub => by
    intro x y0
    rw [listSubN_cons_cons] at hsub
    have hpq : coeffCanonZeroB1 (MultiPoly.sub p q) = true := hsub _ (List.mem_cons_self _ _)
    have hcpq : coeffCanonZeroB1 p = coeffCanonZeroB1 q :=
      coeffCanonZeroB1_eq_of_sub_canonZero p q hpq
    have htail : ∀ c ∈ listSubN ps qs, coeffCanonZeroB1 c = true :=
      fun c hc => hsub c (List.mem_cons_of_mem _ hc)
    have hlen := rdw_eq_of_listSubN1 ps qs htail
    have hheadIH := rdwHead_envEnv0_eq_of_listSubN1 ps qs htail x y0
    have hpq0 := envEnv0_eq_of_sub_canonZero1 p q hpq x y0
    rw [rdwHead_cons coeffCanonZeroB1 p ps, rdwHead_cons coeffCanonZeroB1 q qs, hcpq, hlen]
    by_cases hc : 0 < (qs.reverse.dropWhile coeffCanonZeroB1).length
    · rw [if_pos hc, if_pos hc]; exact hheadIH
    · rw [if_neg hc, if_neg hc]
      by_cases hq1 : coeffCanonZeroB1 q = true
      · rw [if_pos hq1, if_pos hq1]
      · rw [if_neg hq1, if_neg hq1]; exact hpq0

private theorem mem_of_mem_dropWhile' {α : Type} (p : α → Bool) :
    ∀ (M : List α) (a : α), a ∈ M.dropWhile p → a ∈ M
  | [], a, h => h
  | b :: bs, a, h => by
    by_cases hb : p b = true
    · have hd : (b :: bs).dropWhile p = bs.dropWhile p := by simp [List.dropWhile, hb]
      rw [hd] at h
      exact List.mem_cons_of_mem _ (mem_of_mem_dropWhile' p bs a h)
    · have hd : (b :: bs).dropWhile p = b :: bs := by simp [List.dropWhile, hb]
      rw [hd] at h
      exact h

/-- The canonical leading `y₁`-coefficient: the last non-nested-canon-zero `y₁`-coefficient. -/
noncomputable def canonLcY1 (q : MultiPoly 2) : MultiPoly 2 :=
  ((yCoeffsAt (⟨1, by omega⟩ : Fin 2) q).reverse.dropWhile coeffCanonZeroB1).headD (MultiPoly.const 0)

/-- `canonLcY1 q` is `y₁`-free (a `y₁`-coefficient, or `const 0`). -/
theorem canonLcY1_degreeY1_zero (q : MultiPoly 2) :
    MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) (canonLcY1 q) = 0 := by
  unfold canonLcY1
  rcases hL : (yCoeffsAt (⟨1, by omega⟩ : Fin 2) q).reverse.dropWhile coeffCanonZeroB1 with _ | ⟨e, es⟩
  · show MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) (MultiPoly.const 0) = 0; rfl
  · show MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) e = 0
    have he : e ∈ yCoeffsAt (⟨1, by omega⟩ : Fin 2) q := by
      have hmem : e ∈ (yCoeffsAt (⟨1, by omega⟩ : Fin 2) q).reverse := by
        have hd : e ∈ (yCoeffsAt (⟨1, by omega⟩ : Fin 2) q).reverse.dropWhile coeffCanonZeroB1 := by
          rw [hL]; exact List.mem_cons_self _ _
        exact mem_of_mem_dropWhile' _ _ e hd
      exact List.mem_reverse.mp hmem
    exact yCoeffsAt_entries_degreeY_zero (⟨1, by omega⟩ : Fin 2) q e he

/-- **`canonLcY1` is (fully) eval-invariant.** Eval-equal `MultiPoly 2`s have eval-equal canonical
leading `y₁`-coefficients (full eval, via `env0`-agreement + `y₁`-freeness). This feeds the
(already eval-invariant) `singleExpMeasureCanon` for the measure's inner component. -/
theorem canonLcY1_eval_eq_of_eval_eq (q1 q2 : MultiPoly 2)
    (h : ∀ (x : Real) (env : Fin 2 → Real), MultiPoly.eval q1 x env = MultiPoly.eval q2 x env)
    (x : Real) (env : Fin 2 → Real) :
    MultiPoly.eval (canonLcY1 q1) x env = MultiPoly.eval (canonLcY1 q2) x env := by
  have hzero : ∀ (x' : Real) (env' : Fin 2 → Real),
      MultiPoly.eval (MultiPoly.sub q1 q2) x' env' = 0 := by
    intro x' env'; rw [MultiPoly.eval_sub, h x' env']; mach_ring
  have hsub : ∀ c ∈ listSubN (yCoeffsAt (⟨1, by omega⟩ : Fin 2) q1)
                             (yCoeffsAt (⟨1, by omega⟩ : Fin 2) q2),
      coeffCanonZeroB1 c = true := by
    intro c hc
    apply coeffCanonZeroB1_true_of_eval_zero
    intro x' env'
    exact yCoeffsAt_entry_eval_zero_of_eval_zero (⟨1, by omega⟩ : Fin 2)
      (MultiPoly.sub q1 q2) hzero x' env' c hc
  -- env0-agreement of the two canonLcY1 (from the headD induction).
  have henv0 := rdwHead_envEnv0_eq_of_listSubN1 _ _ hsub x (env (⟨0, by omega⟩ : Fin 2))
  -- both canonLcY1 are y₁-free: eval at `env` = eval at `env0 (env ⟨0⟩)`.
  have hoff : ∀ j : Fin 2, j ≠ (⟨1, by omega⟩ : Fin 2) → env j = env0 (env (⟨0, by omega⟩ : Fin 2)) j := by
    intro j hj
    have hj0 : j = (⟨0, by omega⟩ : Fin 2) := by
      rcases j with ⟨v, hv⟩
      have hv1 : v ≠ 1 := fun hveq => hj (Fin.ext hveq)
      exact Fin.ext (by show v = 0; omega)
    rw [hj0]
    show env (⟨0, by omega⟩ : Fin 2)
       = (if (⟨0, by omega⟩ : Fin 2) = (⟨0, by omega⟩ : Fin 2) then env (⟨0, by omega⟩ : Fin 2) else 0)
    rw [if_pos rfl]
  rw [eval_eq_of_env_agree_off (⟨1, by omega⟩ : Fin 2) (canonLcY1 q1) x env
        (env0 (env (⟨0, by omega⟩ : Fin 2))) hoff (canonLcY1_degreeY1_zero q1),
      eval_eq_of_env_agree_off (⟨1, by omega⟩ : Fin 2) (canonLcY1 q2) x env
        (env0 (env (⟨0, by omega⟩ : Fin 2))) hoff (canonLcY1_degreeY1_zero q2)]
  exact henv0

end MachLib.IterExpDepth3CdegY1
