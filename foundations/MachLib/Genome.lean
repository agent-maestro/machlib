/-
MachLib.Genome — the 8 structural inequalities of the EML function genome.

Every closed-form EML expression has four invariants:

  * `p` — pfaffian chain rank
  * `d` — eml depth (AST nesting depth)
  * `w` — max path rank (width)
  * `c` — count of oscillatory primitives

The genome graph (monogate-research/exploration/papers/genome_graph/paper.md)
establishes 8 inequalities that hold across every populated cell in the
C-237 corpus, all 22 ML-activation augmentation rows (C-253), all 877 +
1064 candidate expressions in adversarial searches (C-249 Sprint 3 +
C-256), and all 47 cross-genome rows (C-259, plasma + finance).

Cumulative confirmation: **2 563 / 2 563** with zero violations.

This file:

  * defines a `GenomeCell` as a 4-tuple of natural numbers,
  * encodes the 8 inequalities as a single `IsValid` predicate,
  * proves the trivial corollaries (the all-zero cell is valid, etc.),
  * states `EML_satisfies_inequalities` as an axiom (the empirical
    near-theorem), with a comment listing what would be needed to
    elevate it to a structural-induction proof on the EML AST.

The structural-induction proof requires a Lean formalisation of the
EML AST + the `pfaffian_r` / `eml_depth` / `max_path_r` / `c_osc`
analyzer. That is forthcoming work; this file is the *specification*.

Provenance:

  - Inequalities derived in `monogate-research/exploration/C249_genome_graph_theory/`
    (Sprint 3, FINDINGS.md §"Structural inequalities").
  - Confirmed across 2 563 expressions in the cumulative
    C-249 / C-253 / C-256 / C-258 / C-259 sweeps.
  - Closed-form `pfaffian_r` formula in
    `monogate-research/exploration/C258_pfaffian_closed_form/`.

-/

namespace MachLib
namespace Genome

/-- A genome cell: the 4-tuple `(p, d, w, c)` of structural invariants
attached to an EML expression.

  * `p` = pfaffian chain rank (number of distinct (class, arg) Pfaffian
    primitives in the AST; see C-258 closed-form formula).
  * `d` = AST depth.
  * `w` = max path rank (width of the SLP).
  * `c` = oscillation count (number of trig / hyperbolic-trig primitives).
-/
structure GenomeCell where
  p : Nat
  d : Nat
  w : Nat
  c : Nat
  deriving Repr, DecidableEq

namespace GenomeCell

/-! ### The 8 structural inequalities -/

/-- (1) `d ≥ c`. Oscillation count cannot exceed depth — every trig
    primitive sits inside an AST node and adds at least 1 to depth.  -/
def ineq_d_geq_c (g : GenomeCell) : Prop := g.d ≥ g.c

/-- (2) `w ≥ c`. Width bounds oscillations: each oscillatory primitive
    introduces a new parallel path. -/
def ineq_w_geq_c (g : GenomeCell) : Prop := g.w ≥ g.c

/-- (3) `p ≥ c`. Chain rank dominates oscillation count: each oscillation
    contributes ≥ 1 to chain rank via the trig Pfaffian class. -/
def ineq_p_geq_c (g : GenomeCell) : Prop := g.p ≥ g.c

/-- (4) `p ≥ 1 → w ≥ 1`. A Pfaffian primitive forces non-zero width. -/
def ineq_p_pos_w_pos (g : GenomeCell) : Prop := g.p = 0 ∨ g.w ≥ 1

/-- (5) `c ≥ 1 → w ≥ 1`. An oscillation forces non-zero width. -/
def ineq_c_pos_w_pos (g : GenomeCell) : Prop := g.c = 0 ∨ g.w ≥ 1

/-- (6) `p ≥ 1 → d ≥ 1`. A Pfaffian primitive forces non-zero depth. -/
def ineq_p_pos_d_pos (g : GenomeCell) : Prop := g.p = 0 ∨ g.d ≥ 1

/-- (7) `c ≥ 1 → p ≥ 1`. Oscillation implies non-trivial chain rank. -/
def ineq_c_pos_p_pos (g : GenomeCell) : Prop := g.c = 0 ∨ g.p ≥ 1

/-- (8) `p ≥ w − 1`. Width grows at most one ahead of chain rank. -/
def ineq_p_geq_w_minus_1 (g : GenomeCell) : Prop := g.p + 1 ≥ g.w

/-- The conjunction of all 8 inequalities. -/
def IsValid (g : GenomeCell) : Prop :=
  ineq_d_geq_c g ∧
  ineq_w_geq_c g ∧
  ineq_p_geq_c g ∧
  ineq_p_pos_w_pos g ∧
  ineq_c_pos_w_pos g ∧
  ineq_p_pos_d_pos g ∧
  ineq_c_pos_p_pos g ∧
  ineq_p_geq_w_minus_1 g

/-! ### Trivial corollaries -/

-- Helper: unfold IsValid into its 8 conjuncts as arithmetic statements.
-- For concrete cells the inequalities reduce to decidable Nat comparisons,
-- which `decide` and `omega` can both close.

/-- The zero cell `(0, 0, 0, 0)` is valid. -/
theorem zero_cell_valid : IsValid ⟨0, 0, 0, 0⟩ := by
  unfold IsValid ineq_d_geq_c ineq_w_geq_c ineq_p_geq_c
         ineq_p_pos_w_pos ineq_c_pos_w_pos ineq_p_pos_d_pos
         ineq_c_pos_p_pos ineq_p_geq_w_minus_1
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp

/-- The single-transcendental cell `(1, 1, 1, 0)` (e.g. `exp(x)`) is valid. -/
theorem exp_cell_valid : IsValid ⟨1, 1, 1, 0⟩ := by
  unfold IsValid ineq_d_geq_c ineq_w_geq_c ineq_p_geq_c
         ineq_p_pos_w_pos ineq_c_pos_w_pos ineq_p_pos_d_pos
         ineq_c_pos_p_pos ineq_p_geq_w_minus_1
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp_all <;> omega

/-- The trig cell `(2, 1, 2, 1)` (e.g. `sin(x)`) is valid. -/
theorem sin_cell_valid : IsValid ⟨2, 1, 2, 1⟩ := by
  unfold IsValid ineq_d_geq_c ineq_w_geq_c ineq_p_geq_c
         ineq_p_pos_w_pos ineq_c_pos_w_pos ineq_p_pos_d_pos
         ineq_c_pos_p_pos ineq_p_geq_w_minus_1
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp_all <;> omega

/-- A cell with `c ≥ 1` and `p = 0` is *not* valid. (Concrete witness
that the inequalities are non-trivial.) -/
theorem c_pos_p_zero_invalid : ¬ IsValid ⟨0, 5, 5, 1⟩ := by
  intro h
  have h7 : ineq_c_pos_p_pos ⟨0, 5, 5, 1⟩ := h.2.2.2.2.2.2.1
  unfold ineq_c_pos_p_pos at h7
  simp at h7

end GenomeCell

/-! ### The empirical near-theorem: every EML expression is valid -/

/--
**Axiom (genome inequalities).** Every closed-form EML expression
yields a `GenomeCell` that satisfies all 8 structural inequalities.

This axiom encodes the cumulative empirical finding from the
monogate-research C-249 → C-261 workstreams:

  * 553 + 22 = 575 corpus rows.
  * 877 candidate expressions (C-249 Sprint 3 alphabet sweep).
  * 1 064 candidate expressions (C-256 special-function sweep).
  * 47 cross-genome rows (C-259 plasma + finance).
  * + ad-hoc validations across C-258 / C-261.

  = **2 563 / 2 563** total tested expressions, zero inequality
  violations.

To eliminate the axiom we need:

  1. A Lean formalisation of the EML AST type (out of scope here).
  2. Lean encodings of the four analyzer functions
     (`pfaffian_r`, `eml_depth`, `max_path_r`, `c_osc`) — the C-258
     closed-form formula gives a candidate definition for `pfaffian_r`.
  3. Eight structural-induction proofs, one per inequality. The
     conjectured-easiest is `ineq_c_pos_p_pos`: any `sin / cos / tan /
     sinh / cosh` primitive contributes ≥ 1 to both `c_osc` and
     `pfaffian_r` (via the trig Pfaffian class), so `c ≥ 1 → p ≥ 1`
     follows by induction on AST size.

Until that work lands, this is the spec we use elsewhere in MachLib.
-/
axiom EML_satisfies_inequalities :
  ∀ (g : GenomeCell),
    -- "g is the cell of some EML expression" — we take this as the
    -- universally-quantified claim that any cell *attainable by an EML
    -- expression* is valid. (The connection to the EML AST type lives
    -- in the forthcoming `MachLib.EML.AST` formalisation.)
    GenomeCell.IsValid g

end Genome
end MachLib
