import MachLib.InnerKhovanskiiExpWF
import MachLib.IterExpChain
import MachLib.ChainExp2PathC

/-!
# MachLib.ChainExp2WFInstance — Fix A: decompose-chain-extension WF measure

This file implements **Fix A** from the `InnerKhovanskiiExpWF.lean`
kickoff scaffolding: a lex-3 well-founded measure on `MultiPoly 2`
tracking `(degreeY 1, degreeY 0, polyTrueDegreeStrict (...))` —
the y_1-degree, the y_0-degree, and the canonical x-degree of the
y_1-leading coefficient.

## Why a three-component measure (Fix A)

Per the `InnerKhovanskiiExpWF` kickoff docstring, chain-2's
`chainTotalDeriv` over `IterExpChain 2` introduces a `y_0 · ∂f/∂y_0`
term that raises `degreeY 0` by 1 (because `relations 1 = y_0 · y_1`).
This breaks the naive single-component lex measure on `degreeY 0`.

Fix A: **decompose**. The outer y_1-degree is the most-significant
component. `chainTotalDeriv g`'s formal y_1-degree does not exceed
`degreeY 1 g` (the relation `prodVarYUpTo 1 = y_0 · y_1` has
`degreeY 1 = 1 ≤ 1 = degreeY 1 (varY 1)`, so the standard
`degreeY_chainTotalDeriv_le` applies). When degreeY 1 of two
multi-polys is equal, the inner y_0-degree breaks the tie. When
both y_1 and y_0 degrees are equal, the canonical x-degree of the
y_1-leading coefficient breaks the remaining tie.

## What this file ships (constructive)

- `chain2Measure : MultiPoly 2 → Nat × Nat × Nat` — the lex-3 measure.
- `chain2MeasureRel : MultiPoly 2 → MultiPoly 2 → Prop` — strict lex-3.
- `lex3LT_wf : WellFounded lex3LT` — lex-3 well-foundedness via three
  nested strong-induction layers on `Nat × Nat × Nat`.
- `chain2Measure_WF : WellFounded chain2MeasureRel` — pullback via
  `InvImage.wf`.
- `IterExpChain2_rel_degY1_bound` — structural fact that `IterExpChain 2`'s
  relations satisfy the per-index `degreeY 1` bound used by
  `degreeY_chainTotalDeriv_le`.
- `degreeY1_chainTotalDeriv_le_IterExpChain2` — direct corollary:
  `degreeY 1 (chainTotalDeriv (IterExpChain 2) g) ≤ degreeY 1 g`.
- `degreeY_chainTotalDeriv_zero_of_zero_IterExp2` — y-free preservation:
  when `degreeY 0 g = degreeY 1 g = 0`, the result of chainTotalDeriv is
  also y-free at every index.
- `chainExp2_innerKhovanskii_full : InnerKhovanskiiExp` — the algebraic
  instance `(T = MultiPoly 2, h = exp, h_deriv = exp,
  scalarMul k g = (k·y_0)·g)`.
- `coeffStep_chain2_le` — discharged via classical excluded middle
  because the WFR-kickoff predicate is `¬ measureRel ... ∨ measureRel ...`
  (the predicate as written is trivially true in classical logic).
- `chain2_to_WFR` — given a `length_one_bound` hypothesis and a
  `coeffStep_lt_hyp` hypothesis (the strict-descent disjunction at k=0),
  plugs into the WFR framework.

## What is open: `coeffStep_chain2_lt`

The WFR's `coeffStep_lt` signature asks for
`measureRel (step g) g ∨ step g = g` where
`step g = chainTotalDeriv g + (0 · y_0) · g`.

The right disjunct (AST equality) fails universally because the
`(0 · y_0) · g` AST sub-term is non-zero structurally even when it
evaluates to zero.

The left disjunct (genuine lex-3 strict descent at k=0) is the
genuine mathematical content. With the current lex-3 measure on the
raw AST it does NOT hold either: `(0 · y_0) · g`'s formal
`degreeY 0` equals `degreeY 0 g + 1` (a strict INCREASE), and the
`add` with `chainTotalDeriv g` propagates this increase to the
second component of the measure.

Establishing the strict descent therefore requires either:

1. **Canonicalize before measuring**: define
   `chain2Measure_canonical g := chain2Measure (multiSimplify g)`.
   With `multiSimplify`, `(0 · y_0) · g → const 0` and the `add`
   collapses to `chainTotalDeriv g`. Then the strict descent on the
   third component lifts directly from PathC's SingleExp infrastructure.

2. **Use the eval/Poly bridge**: measure based on
   `polyTrueDegreeStrict (polyCoeffs (mP2PFL ...))` which already
   absorbs eval-equal AST variation.

Either path is ~200-300 lines of follow-up work, branching from
PathC's existing strict-descent infrastructure. For this session
we parametrise `chain2_to_WFR` over the `coeffStep_lt_hyp` predicate,
matching the parametric-axioms pattern of
`chainExp2_bound_via_measured_axioms` in `ChainExp2Instance.lean`.

## Status

Structure + WF proof + classical-em `coeffStep_le` + algebraic instance
shipped clean. Constructive `coeffStep_chain2_lt` parametrised as a
hypothesis (next session's work).

Zero new axioms. Zero `sorry`. Self-contained on top of MachLib
infrastructure.
-/

namespace MachLib
namespace ChainExp2WFInstanceMod

open MachLib.Real
open MachLib.MultiPolyMod
open MachLib.PfaffianChainMod
open MachLib.PfaffianChainMod.PfaffianFn
open MachLib.IterExpChainMod
open MachLib.PolynomialCanonical
open MachLib.PolynomialEvidence
open MachLib.InnerKhovanskiiExpWFMod

/-! ## Fin 2 index helpers -/

/-- The inner chain index `y_0`. -/
def fin0_of_2 : Fin 2 := ⟨0, by omega⟩

/-- The outer chain index `y_1`. -/
def fin1_of_2 : Fin 2 := ⟨1, by omega⟩

/-! ## The chain-2 lex-3 measure -/

/-- The chain-2 lex-3 measure on `MultiPoly 2`.

Components in order of significance:
1. `MultiPoly.degreeY 1 g`  — outer y_1-degree.
2. `MultiPoly.degreeY 0 g`  — inner y_0-degree.
3. `polyTrueDegreeStrict (polyCoeffs (mP2PFL (leadingCoeffY 1 g)))`
   — canonical x-degree of the y_1-leading coefficient. -/
noncomputable def chain2Measure (g : MultiPoly 2) : Nat × Nat × Nat :=
  ( MultiPoly.degreeY fin1_of_2 g
  , MultiPoly.degreeY fin0_of_2 g
  , polyTrueDegreeStrict
      (polyCoeffs (multiPolyToPolyForLex
        (MultiPoly.leadingCoeffY fin1_of_2 g))) )

/-! ## Lex-3 strict order on `Nat × Nat × Nat` -/

/-- Strict lex on `Nat × Nat × Nat` (most-significant first). -/
def lex3LT (m m' : Nat × Nat × Nat) : Prop :=
  m.1 < m'.1
  ∨ (m.1 = m'.1
     ∧ (m.2.1 < m'.2.1
        ∨ (m.2.1 = m'.2.1 ∧ m.2.2 < m'.2.2)))

theorem lex3LT_irrefl (m : Nat × Nat × Nat) : ¬ lex3LT m m := by
  intro h
  rcases h with h1 | ⟨_, h2⟩
  · exact Nat.lt_irrefl _ h1
  · rcases h2 with h2a | ⟨_, h2b⟩
    · exact Nat.lt_irrefl _ h2a
    · exact Nat.lt_irrefl _ h2b

/-- Well-foundedness of lex-3 on `Nat × Nat × Nat`: three nested
strong inductions. -/
theorem lex3LT_wf : WellFounded lex3LT := by
  apply WellFounded.intro
  intro ⟨a, b, c⟩
  suffices h : ∀ a b c, Acc lex3LT (a, b, c) from h a b c
  intro a
  induction a using Nat.strongRecOn with
  | _ a iha =>
    intro b
    induction b using Nat.strongRecOn with
    | _ b ihb =>
      intro c
      induction c using Nat.strongRecOn with
      | _ c ihc =>
        constructor
        intro ⟨a', b', c'⟩ h
        rcases h with ha | ⟨haeq, h_rest⟩
        · exact iha a' ha b' c'
        · subst haeq
          rcases h_rest with hb | ⟨hbeq, hc⟩
          · exact ihb b' hb c'
          · subst hbeq
            exact ihc c' hc

/-- The chain-2 strict-descent relation: lex-3 on the chain-2 measure. -/
def chain2MeasureRel (g g' : MultiPoly 2) : Prop :=
  lex3LT (chain2Measure g) (chain2Measure g')

/-- Well-foundedness of `chain2MeasureRel` by pullback through
`chain2Measure`. -/
theorem chain2Measure_WF : WellFounded chain2MeasureRel :=
  InvImage.wf chain2Measure lex3LT_wf

/-! ## Structural lemmas: `IterExpChain 2`'s relations -/

theorem prodVarYUpTo_one_eq :
    (prodVarYUpTo 1 (by omega : (1 : Nat) < 2) : MultiPoly 2)
    = MultiPoly.mul (MultiPoly.varY ⟨0, by omega⟩)
                    (MultiPoly.varY ⟨1, by omega⟩) := by
  show MultiPoly.mul (prodVarYUpTo 0 (by omega))
                     (MultiPoly.varY ⟨0 + 1, by omega⟩)
       = MultiPoly.mul (MultiPoly.varY ⟨0, by omega⟩)
                       (MultiPoly.varY ⟨1, by omega⟩)
  rfl

theorem IterExpChain2_relations_0 :
    (IterExpChain 2).relations ⟨0, by omega⟩
    = (MultiPoly.varY ⟨0, by omega⟩ : MultiPoly 2) := rfl

theorem IterExpChain2_relations_1 :
    (IterExpChain 2).relations ⟨1, by omega⟩
    = MultiPoly.mul (MultiPoly.varY ⟨0, by omega⟩ : MultiPoly 2)
                    (MultiPoly.varY ⟨1, by omega⟩) := by
  show (prodVarYUpTo 1 _ : MultiPoly 2)
       = MultiPoly.mul (MultiPoly.varY ⟨0, by omega⟩)
                       (MultiPoly.varY ⟨1, by omega⟩)
  exact prodVarYUpTo_one_eq

/-- `IterExpChain 2`'s relations satisfy the per-index `degreeY 1`
bound: relation j's degreeY at index 1 does not exceed `varY j`'s.

- j = 0: relations 0 = varY 0, degreeY 1 = 0 ≤ 0.
- j = 1: relations 1 = varY 0 · varY 1, degreeY 1 = 0 + 1 = 1 ≤ 1. -/
theorem IterExpChain2_rel_degY1_bound (j : Fin 2) :
    MultiPoly.degreeY fin1_of_2 ((IterExpChain 2).relations j)
    ≤ MultiPoly.degreeY fin1_of_2 (MultiPoly.varY j : MultiPoly 2) := by
  match j with
  | ⟨0, _⟩ =>
    show MultiPoly.degreeY fin1_of_2
           ((IterExpChain 2).relations ⟨0, by omega⟩ : MultiPoly 2)
         ≤ MultiPoly.degreeY fin1_of_2
            (MultiPoly.varY ⟨0, by omega⟩ : MultiPoly 2)
    rw [IterExpChain2_relations_0]
    exact Nat.le_refl _
  | ⟨1, _⟩ =>
    show MultiPoly.degreeY fin1_of_2
           ((IterExpChain 2).relations ⟨1, by omega⟩ : MultiPoly 2)
         ≤ MultiPoly.degreeY fin1_of_2
            (MultiPoly.varY ⟨1, by omega⟩ : MultiPoly 2)
    rw [IterExpChain2_relations_1]
    show MultiPoly.degreeY fin1_of_2 (MultiPoly.varY ⟨0, by omega⟩ : MultiPoly 2)
       + MultiPoly.degreeY fin1_of_2 (MultiPoly.varY ⟨1, by omega⟩ : MultiPoly 2)
       ≤ MultiPoly.degreeY fin1_of_2 (MultiPoly.varY ⟨1, by omega⟩ : MultiPoly 2)
    have h0 : MultiPoly.degreeY fin1_of_2
                (MultiPoly.varY ⟨0, by omega⟩ : MultiPoly 2) = 0 := by
      show (if (fin1_of_2 : Fin 2) = ⟨0, by omega⟩ then 1 else 0) = 0
      have hne : (fin1_of_2 : Fin 2) ≠ ⟨0, by omega⟩ := by
        intro h
        have hval : (fin1_of_2 : Fin 2).val = (⟨0, by omega⟩ : Fin 2).val :=
          congrArg Fin.val h
        exact absurd hval (by decide)
      rw [if_neg hne]
    rw [h0, Nat.zero_add]
    exact Nat.le_refl _

/-- `chainTotalDeriv (IterExpChain 2)` preserves `degreeY 1` non-strictly. -/
theorem degreeY1_chainTotalDeriv_le_IterExpChain2 (p : MultiPoly 2) :
    MultiPoly.degreeY fin1_of_2
      (PfaffianFn.chainTotalDeriv (IterExpChain 2) p)
    ≤ MultiPoly.degreeY fin1_of_2 p :=
  PfaffianFn.degreeY_chainTotalDeriv_le (IterExpChain 2) fin1_of_2
    IterExpChain2_rel_degY1_bound p

/-! ## y-free preservation for chain-2

When `g : MultiPoly 2` has both `degreeY 0 g = 0` and `degreeY 1 g = 0`,
the AST contains no `varY` leaves. `chainTotalDeriv` then never fires
its varY-substitution case, so the result is y-free at every index. -/

theorem degreeY_chainTotalDeriv_zero_of_zero_IterExp2
    (p : MultiPoly 2)
    (h0 : MultiPoly.degreeY fin0_of_2 p = 0)
    (h1 : MultiPoly.degreeY fin1_of_2 p = 0) (i : Fin 2) :
    MultiPoly.degreeY i
      (PfaffianFn.chainTotalDeriv (IterExpChain 2) p) = 0 := by
  induction p with
  | const c =>
    show MultiPoly.degreeY i
           (PfaffianFn.chainTotalDeriv (IterExpChain 2) (MultiPoly.const c)) = 0
    show MultiPoly.degreeY i (MultiPoly.const (0 : Real) : MultiPoly 2) = 0
    rfl
  | varX =>
    show MultiPoly.degreeY i
           (PfaffianFn.chainTotalDeriv (IterExpChain 2) MultiPoly.varX) = 0
    show MultiPoly.degreeY i (MultiPoly.const (1 : Real) : MultiPoly 2) = 0
    rfl
  | varY j =>
    exfalso
    match j with
    | ⟨0, _⟩ =>
      have : MultiPoly.degreeY fin0_of_2
              (MultiPoly.varY ⟨0, by omega⟩ : MultiPoly 2) = 1 := by
        show (if (fin0_of_2 : Fin 2) = ⟨0, by omega⟩ then 1 else 0) = 1
        have heq : (fin0_of_2 : Fin 2) = ⟨0, by omega⟩ := rfl
        rw [heq]; simp
      rw [this] at h0; exact Nat.one_ne_zero h0
    | ⟨1, _⟩ =>
      have : MultiPoly.degreeY fin1_of_2
              (MultiPoly.varY ⟨1, by omega⟩ : MultiPoly 2) = 1 := by
        show (if (fin1_of_2 : Fin 2) = ⟨1, by omega⟩ then 1 else 0) = 1
        have heq : (fin1_of_2 : Fin 2) = ⟨1, by omega⟩ := rfl
        rw [heq]; simp
      rw [this] at h1; exact Nat.one_ne_zero h1
  | add p q ihp ihq =>
    have hmax0 : Nat.max (MultiPoly.degreeY fin0_of_2 p)
                          (MultiPoly.degreeY fin0_of_2 q) = 0 := h0
    have hmax1 : Nat.max (MultiPoly.degreeY fin1_of_2 p)
                          (MultiPoly.degreeY fin1_of_2 q) = 0 := h1
    have hp0 : MultiPoly.degreeY fin0_of_2 p = 0 :=
      Nat.le_zero.mp ((Nat.max_le.mp (Nat.le_of_eq hmax0)).1)
    have hq0 : MultiPoly.degreeY fin0_of_2 q = 0 :=
      Nat.le_zero.mp ((Nat.max_le.mp (Nat.le_of_eq hmax0)).2)
    have hp1 : MultiPoly.degreeY fin1_of_2 p = 0 :=
      Nat.le_zero.mp ((Nat.max_le.mp (Nat.le_of_eq hmax1)).1)
    have hq1 : MultiPoly.degreeY fin1_of_2 q = 0 :=
      Nat.le_zero.mp ((Nat.max_le.mp (Nat.le_of_eq hmax1)).2)
    show Nat.max (MultiPoly.degreeY i
                  (PfaffianFn.chainTotalDeriv (IterExpChain 2) p))
                  (MultiPoly.degreeY i
                  (PfaffianFn.chainTotalDeriv (IterExpChain 2) q)) = 0
    rw [ihp hp0 hp1, ihq hq0 hq1]; rfl
  | sub p q ihp ihq =>
    have hmax0 : Nat.max (MultiPoly.degreeY fin0_of_2 p)
                          (MultiPoly.degreeY fin0_of_2 q) = 0 := h0
    have hmax1 : Nat.max (MultiPoly.degreeY fin1_of_2 p)
                          (MultiPoly.degreeY fin1_of_2 q) = 0 := h1
    have hp0 : MultiPoly.degreeY fin0_of_2 p = 0 :=
      Nat.le_zero.mp ((Nat.max_le.mp (Nat.le_of_eq hmax0)).1)
    have hq0 : MultiPoly.degreeY fin0_of_2 q = 0 :=
      Nat.le_zero.mp ((Nat.max_le.mp (Nat.le_of_eq hmax0)).2)
    have hp1 : MultiPoly.degreeY fin1_of_2 p = 0 :=
      Nat.le_zero.mp ((Nat.max_le.mp (Nat.le_of_eq hmax1)).1)
    have hq1 : MultiPoly.degreeY fin1_of_2 q = 0 :=
      Nat.le_zero.mp ((Nat.max_le.mp (Nat.le_of_eq hmax1)).2)
    show Nat.max (MultiPoly.degreeY i
                  (PfaffianFn.chainTotalDeriv (IterExpChain 2) p))
                  (MultiPoly.degreeY i
                  (PfaffianFn.chainTotalDeriv (IterExpChain 2) q)) = 0
    rw [ihp hp0 hp1, ihq hq0 hq1]; rfl
  | mul p q ihp ihq =>
    have hsum0 : MultiPoly.degreeY fin0_of_2 p
               + MultiPoly.degreeY fin0_of_2 q = 0 := h0
    have hsum1 : MultiPoly.degreeY fin1_of_2 p
               + MultiPoly.degreeY fin1_of_2 q = 0 := h1
    have hp0 : MultiPoly.degreeY fin0_of_2 p = 0 := by omega
    have hq0 : MultiPoly.degreeY fin0_of_2 q = 0 := by omega
    have hp1 : MultiPoly.degreeY fin1_of_2 p = 0 := by omega
    have hq1 : MultiPoly.degreeY fin1_of_2 q = 0 := by omega
    show Nat.max
          (MultiPoly.degreeY i
             (PfaffianFn.chainTotalDeriv (IterExpChain 2) p)
           + MultiPoly.degreeY i q)
          (MultiPoly.degreeY i p
           + MultiPoly.degreeY i
              (PfaffianFn.chainTotalDeriv (IterExpChain 2) q)) = 0
    rw [ihp hp0 hp1, ihq hq0 hq1]
    match i with
    | ⟨0, _⟩ =>
      rw [show MultiPoly.degreeY (⟨0, by omega⟩ : Fin 2) p
            = MultiPoly.degreeY fin0_of_2 p from rfl,
          show MultiPoly.degreeY (⟨0, by omega⟩ : Fin 2) q
            = MultiPoly.degreeY fin0_of_2 q from rfl, hp0, hq0]
      rfl
    | ⟨1, _⟩ =>
      rw [show MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) p
            = MultiPoly.degreeY fin1_of_2 p from rfl,
          show MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) q
            = MultiPoly.degreeY fin1_of_2 q from rfl, hp1, hq1]
      rfl

/-! ## The chain-2 InnerKhovanskiiExp algebraic instance

The algebraic operations for chain-length-2 over IterExp 2 with
inner type `MultiPoly 2` over `IterExpChain 2`. The h-frame
choice (`h = exp`, `h_deriv = exp`) matches the kickoff's framing:
chain-2's scalarMul factor is `h_deriv x = y_0 = exp x`. -/

noncomputable def chainExp2_innerKhovanskii_full :
    MachLib.InnerKhovanskiiExpMod.InnerKhovanskiiExp where
  T := MultiPoly 2
  eval := fun g x => MultiPoly.eval g x ((IterExpChain 2).chainValues x)
  derivative := fun g => PfaffianFn.chainTotalDeriv (IterExpChain 2) g
  add := MultiPoly.add
  scalarMul := fun k g =>
    MultiPoly.mul (MultiPoly.mul (MultiPoly.const k)
                                  (MultiPoly.varY ⟨0, by omega⟩))
                  g
  h := Real.exp
  h_deriv := Real.exp
  eval_HasDerivAt := by
    intro g x
    show HasDerivAt
      (fun y => MultiPoly.eval g y ((IterExpChain 2).chainValues y))
      (MultiPoly.eval (PfaffianFn.chainTotalDeriv (IterExpChain 2) g)
        x ((IterExpChain 2).chainValues x)) x
    exact PfaffianFn.multiPolyHasDerivAt_eval_with_chain
            (IterExpChain 2) g x (IterExpChain_isCoherentAt 2 x)
  eval_add := by intro g1 g2 x; rfl
  eval_scalarMul := by
    intro k g x
    show MultiPoly.eval
           (MultiPoly.mul (MultiPoly.mul (MultiPoly.const k)
                                          (MultiPoly.varY ⟨0, by omega⟩))
                          g) x ((IterExpChain 2).chainValues x)
         = k * Real.exp x *
           MultiPoly.eval g x ((IterExpChain 2).chainValues x)
    show (k * (IterExpChain 2).chainValues x ⟨0, by omega⟩)
           * MultiPoly.eval g x ((IterExpChain 2).chainValues x)
         = k * Real.exp x *
           MultiPoly.eval g x ((IterExpChain 2).chainValues x)
    -- chainValues x ⟨0, _⟩ = iterExp 0 x = exp x.
    show (k * Real.exp x)
         * MultiPoly.eval g x ((IterExpChain 2).chainValues x)
         = k * Real.exp x *
           MultiPoly.eval g x ((IterExpChain 2).chainValues x)
    rfl
  h_HasDerivAt := HasDerivAt_exp

/-! ## `coeffStep_chain2_le` — classical em

The WFR-kickoff `coeffStep_le` signature is
`¬ measureRel (step g) g ∨ measureRel (step g) g`,
which is `¬P ∨ P` — trivially true via `Classical.em`.

The honest reading: the predicate as written admits any descent
relation (it's vacuous). Our `chain2MeasureRel` satisfies this
signature trivially, like every relation. -/

theorem coeffStep_chain2_le (k : Real) (g : MultiPoly 2) :
    ¬ chain2MeasureRel
        (MultiPoly.add
          (PfaffianFn.chainTotalDeriv (IterExpChain 2) g)
          (MultiPoly.mul (MultiPoly.mul (MultiPoly.const k)
                                         (MultiPoly.varY ⟨0, by omega⟩))
                          g)) g
    ∨ chain2MeasureRel
        (MultiPoly.add
          (PfaffianFn.chainTotalDeriv (IterExpChain 2) g)
          (MultiPoly.mul (MultiPoly.mul (MultiPoly.const k)
                                         (MultiPoly.varY ⟨0, by omega⟩))
                          g)) g := by
  exact (Classical.em _).symm

/-! ## Plug into `InnerKhovanskiiExpWFR`

The chain-2 algebraic instance + lex-3 WF descent gives an
`InnerKhovanskiiExpWFR` value, parametric over the two hypotheses:

- `length_one_bound` — same parametric shape as
  `chainExp2_bound_via_measured_axioms` in `ChainExp2Instance.lean`.
  The zero-count bound for a single chain-2 PfaffianFn requires
  its own zero-count argument (separate work).

- `coeffStep_lt_hyp` — the strict-descent disjunction at k=0.
  Discussed at length above; replacing this with a constructive
  proof is the next session's work.
-/

noncomputable def chain2_to_WFR
    (length_one_bound :
      ∀ g : MultiPoly 2, ∀ a b : Real, a < b →
      (∃ x : Real, MultiPoly.eval g x ((IterExpChain 2).chainValues x) ≠ 0) →
      ∃ N : Nat, ∀ zeros : List Real, zeros.Nodup →
        (∀ z ∈ zeros, a < z ∧ z < b ∧
          MultiPoly.eval g z ((IterExpChain 2).chainValues z) = 0) →
        zeros.length ≤ N)
    (coeffStep_lt_hyp :
      ∀ g : MultiPoly 2,
        chain2MeasureRel
          (MultiPoly.add
            (PfaffianFn.chainTotalDeriv (IterExpChain 2) g)
            (MultiPoly.mul (MultiPoly.mul (MultiPoly.const 0)
                                           (MultiPoly.varY ⟨0, by omega⟩))
                            g)) g
        ∨ MultiPoly.add
            (PfaffianFn.chainTotalDeriv (IterExpChain 2) g)
            (MultiPoly.mul (MultiPoly.mul (MultiPoly.const 0)
                                           (MultiPoly.varY ⟨0, by omega⟩))
                            g) = g) :
    InnerKhovanskiiExpWFR where
  toInnerKhovanskiiExp := chainExp2_innerKhovanskii_full
  measureRel := chain2MeasureRel
  measureWF := chain2Measure_WF
  length_one_bound := length_one_bound
  coeffStep_le := coeffStep_chain2_le
  coeffStep_lt := coeffStep_lt_hyp

/-! ## Path 1 (canonicalisation) follow-up: structural lemmas

This block is the EH-A9 follow-up: a partial attempt to discharge
`coeffStep_chain2_lt` via Path 1 (canonicalise the AST before
measuring) as sketched in the closing docstring above.

### What ships clean here

1. `chain2Measure_canonical` + `chain2MeasureRelCanonical` +
   `chain2Measure_canonical_WF` — the canonical lex-3 measure (pulled
   back through `multiSimplify`) and its WF proof via `InvImage.wf`.
   This is the lifting infrastructure that Path 1 needs even though
   the strict-descent step itself doesn't close (see obstacle below).
2. `coeffStep_chain2_le_canonical` — classical-em discharge of the
   non-strict descent for the canonical relation.
3. `chain2_to_WFR_canonical` — canonical-measure variant of
   `chain2_to_WFR`, still parametric over the strict-descent
   hypothesis (which the Reason 1/2 analysis below shows is
   structurally not closable with the current WFR signature).

### Absorption identities (claimed but not shipped, intentionally)

Two identities the canonical Path 1 strategy would build on:
  - `multiSimplify ((0·y_0)·g) = const 0`
  - `multiSimplify (add (chainTotalDeriv g) ((0·y_0)·g))
     = multiSimplify (chainTotalDeriv g)`

Both hold by direct computation on `multiSimplify`'s `mul`/`add`
rules: the inner `mul (const 0) (varY 0)` triggers the
`multiIsZeroConst (const 0) = true` branch returning `const 0`, the
outer `mul (const 0) g'` does the same, and the outer
`add (·) (const 0)` collapses via the `multiIsZeroConst q'` branch.
They are intentionally NOT shipped as Lean theorems here because the
chain-2 obstacle (Reasons 1 + 2 below) makes them dead-end work for
this scaffold: even with both absorptions, the resulting strict-
descent obligation `chain2MeasureRelCanonical (multiSimplify
(chainTotalDeriv g)) g` is FALSE at `g := varY 1`. Shipping them
without their downstream consumer would mislead a future reader into
thinking Path 1 is close to closure.

### Where Path 1 STOPS (the irreducible obstacle)

Path 1 was conjectured to enable lifting PathC's
`singleExp_polyTrueDegreeStrict_scaledReduction_lt` into a chain-2
strict-descent witness for `coeffStep_chain2_lt`. After working
through the structural reductions, this lift does NOT close the
WFR's `coeffStep_lt` disjunction. Two independent reasons:

**Reason 1 (step-shape mismatch).** PathC's SingleExp strict-decrease
is for the **scaledReduction** step `chainTotalDeriv p − c·p`
(subtracting `c·p`, where `c = degreeY 0 p`). The WFR's
`coeffStep_lt` at `k = 0` is for the step `chainTotalDeriv g + 0·g`
(eval-equivalent to just `chainTotalDeriv g`, no subtraction).
These are STRUCTURALLY different operations on the multi-polynomial.
The PathC theorem's RHS (`scaledReduction`) cannot be retargetted
to `chainTotalDeriv` alone: the strict-decrease relies on the
leading-coefficient cancellation that subtraction performs.
`chainTotalDeriv g` by itself does NOT strictly reduce
`polyTrueDegreeStrict` of the y_1-leading coefficient — it preserves
it (since `chainTotalDeriv` lowers `degreeY 0` of the leading
coefficient by 1 via SingleExp's `polyTrueDegreeStrict_polyDerivativeCoeffs_lt`
only when there's a `−c·p` term to absorb the constant-leading case).

**Reason 2 (chain-2 chainTotalDeriv increases lex-3 measure).**
Beyond the step-shape mismatch, `chainTotalDeriv` on `IterExpChain 2`
genuinely INCREASES the canonical lex-3 measure for natural inputs.
Concrete counterexample: take `g := varY 1 : MultiPoly 2`.
  - `multiSimplify g = varY 1` (already canonical).
  - `chainTotalDeriv (IterExpChain 2) (varY 1)
     = (IterExpChain 2).relations 1
     = varY 0 · varY 1` (per `IterExpChain2_relations_1`).
  - `multiSimplify (varY 0 · varY 1) = varY 0 · varY 1` (no zero/one
    factor to collapse).
  - `chain2Measure (varY 1) = (1, 0, 1)`:
      degreeY 1 = 1, degreeY 0 = 0,
      polyTrueDegreeStrict (polyCoeffs (mP2PFL (const 1))) = 1.
  - `chain2Measure (varY 0 · varY 1) = (1, 1, 0)`:
      degreeY 1 = 0 + 1 = 1, degreeY 0 = 1 + 0 = 1,
      polyTrueDegreeStrict (polyCoeffs (mP2PFL (mul (varY 0) (const 1))))
      = 0 (y-free reduction of `varY 0` is `Poly.const 0`, killing the
      product).
  - Lex-3 comparison: components (1, 1, 0) vs (1, 0, 1) — first equal,
    second strictly LARGER on the step result. So
    `chain2MeasureRelCanonical (chainTotalDeriv (varY 1)) (varY 1)` is
    FALSE. And `(chainTotalDeriv (varY 1) + (0·y_0)·varY 1) = varY 1`
    is structurally FALSE.
  - Both disjuncts of WFR's `coeffStep_lt` fail at this single witness.

The mathematical content: in `IterExpChain 2`, `relations 1 = y_0·y_1`
adds a `y_0` factor to the y_1-derivative chain rule. The chain-2
chainTotalDeriv's `y_1 ↦ y_0·y_1` substitution genuinely raises
`degreeY 0` by 1 without compensating reduction. The naive lex-3
measure cannot absorb this without precondition (analogue of
SingleExp Measured's `hpos : measure t > 0`) or a step that
SUBTRACTS the leading coefficient.

### What would unblock

Three honest paths forward:

(a) **Weaken `coeffStep_lt`** in `InnerKhovanskiiExpWFR` to add a
    minimality precondition (analogue of `InnerKhovanskiiExpMeasured`'s
    `measure t > 0`). The task forbids modifying `InnerKhovanskiiExpWF`,
    so this is out of scope here.

(b) **Change the step shape** in `chainExp2_innerKhovanskii_full` to
    `chainTotalDeriv g − degreeY·g` instead of just `chainTotalDeriv g`
    at `k = 0`. This breaks the inherited `scalarMul k g = (k·y_0)·g`
    invariant required by `eval_scalarMul`, so it requires a different
    `h_deriv` framing — a structural redesign rather than a strict
    follow-up on the current scaffold.

(c) **Wait for a list-level WF relation** (Fix B in
    `InnerKhovanskiiExpWF`'s closing docstring). Lifting the measure
    to `List T` lets neighbouring coefficients drag the global measure
    down even when a single coefficient's measure rises.

Per the project rule "no axiomatic shortcuts" and the task's explicit
permission to STOP at honest blockers, `coeffStep_chain2_lt` is NOT
shipped here as an unconditional theorem. The genuine partial
progress (canonical WF measure + canonical-measure variant of
`chain2_to_WFR`, still parametric over `coeffStep_lt_hyp_canonical`)
is below, gated on this honest analysis.
-/

/-! ### Path 1 canonical lex-3 measure (definition + WF) -/

/-- The canonical chain-2 lex-3 measure: pull back `chain2Measure`
through `multiSimplify`. The post-canonicalisation AST has the
`(0·y_0)·g` term absorbed (per `multiSimplify_scalarMul_zero`),
so the canonical measure agrees on the step argument and on
`multiSimplify (chainTotalDeriv g)` directly. -/
noncomputable def chain2Measure_canonical (g : MultiPoly 2) : Nat × Nat × Nat :=
  chain2Measure (MultiPoly.multiSimplify g)

/-- The canonical strict-descent relation: lex-3 on the canonical
chain-2 measure. -/
def chain2MeasureRelCanonical (g g' : MultiPoly 2) : Prop :=
  lex3LT (chain2Measure_canonical g) (chain2Measure_canonical g')

/-- Well-foundedness of `chain2MeasureRelCanonical` by pullback
through `chain2Measure_canonical`. -/
theorem chain2Measure_canonical_WF : WellFounded chain2MeasureRelCanonical :=
  InvImage.wf chain2Measure_canonical lex3LT_wf

/-! ### Classical-em `coeffStep_le` for the canonical relation

Same shape as `coeffStep_chain2_le` — the `¬ P ∨ P` predicate is
trivially true for any relation. -/

theorem coeffStep_chain2_le_canonical (k : Real) (g : MultiPoly 2) :
    ¬ chain2MeasureRelCanonical
        (MultiPoly.add
          (PfaffianFn.chainTotalDeriv (IterExpChain 2) g)
          (MultiPoly.mul (MultiPoly.mul (MultiPoly.const k)
                                         (MultiPoly.varY ⟨0, by omega⟩))
                          g)) g
    ∨ chain2MeasureRelCanonical
        (MultiPoly.add
          (PfaffianFn.chainTotalDeriv (IterExpChain 2) g)
          (MultiPoly.mul (MultiPoly.mul (MultiPoly.const k)
                                         (MultiPoly.varY ⟨0, by omega⟩))
                          g)) g := by
  exact (Classical.em _).symm

/-! ### Canonical-measure variant of `chain2_to_WFR`

Same parametric shape: still parametric over `length_one_bound`
AND `coeffStep_lt_hyp` (for the same reason — see the obstacle
documentation above). The CANONICAL variant differs only in using
`chain2MeasureRelCanonical` instead of `chain2MeasureRel`.

This is shipped so a future session attempting Path 1 has the
canonical-measure scaffolding ready; they only need to discharge
`coeffStep_lt_hyp` (or change framework). -/

noncomputable def chain2_to_WFR_canonical
    (length_one_bound :
      ∀ g : MultiPoly 2, ∀ a b : Real, a < b →
      (∃ x : Real, MultiPoly.eval g x ((IterExpChain 2).chainValues x) ≠ 0) →
      ∃ N : Nat, ∀ zeros : List Real, zeros.Nodup →
        (∀ z ∈ zeros, a < z ∧ z < b ∧
          MultiPoly.eval g z ((IterExpChain 2).chainValues z) = 0) →
        zeros.length ≤ N)
    (coeffStep_lt_hyp_canonical :
      ∀ g : MultiPoly 2,
        chain2MeasureRelCanonical
          (MultiPoly.add
            (PfaffianFn.chainTotalDeriv (IterExpChain 2) g)
            (MultiPoly.mul (MultiPoly.mul (MultiPoly.const 0)
                                           (MultiPoly.varY ⟨0, by omega⟩))
                            g)) g
        ∨ MultiPoly.add
            (PfaffianFn.chainTotalDeriv (IterExpChain 2) g)
            (MultiPoly.mul (MultiPoly.mul (MultiPoly.const 0)
                                           (MultiPoly.varY ⟨0, by omega⟩))
                            g) = g) :
    InnerKhovanskiiExpWFR where
  toInnerKhovanskiiExp := chainExp2_innerKhovanskii_full
  measureRel := chain2MeasureRelCanonical
  measureWF := chain2Measure_canonical_WF
  length_one_bound := length_one_bound
  coeffStep_le := coeffStep_chain2_le_canonical
  coeffStep_lt := coeffStep_lt_hyp_canonical

/-! ## Status / axiom audit

After this file compiles, the following commands should show only
Lean stdlib axioms (`Classical.choice`, `propext`, `Quot.sound`) —
no new axioms introduced by this file.

```
#print axioms chain2Measure_WF
#print axioms chainExp2_innerKhovanskii_full
#print axioms coeffStep_chain2_le
#print axioms chain2_to_WFR
#print axioms chain2Measure_canonical_WF
#print axioms coeffStep_chain2_le_canonical
#print axioms chain2_to_WFR_canonical
```

The strict-descent obligation (`coeffStep_lt_hyp` /
`coeffStep_lt_hyp_canonical`) is STILL parametric in both the raw
and canonical scaffolds. See the obstacle documentation above for
the witness (`g := varY 1`) showing the WFR's disjunctive
`coeffStep_lt` is structurally unsatisfiable under any lex-3-like
measure on `MultiPoly 2` for `IterExpChain 2`, given the current
step shape `chainTotalDeriv g + 0·y_0·g`. Closing the chain-2
Khovanskii bound requires one of: (a) weakening WFR's `coeffStep_lt`
to a precondition shape, (b) changing the chain-2 step to include
`−degreeY·g` subtraction, or (c) list-level WF (Fix B). -/

end ChainExp2WFInstanceMod
end MachLib
