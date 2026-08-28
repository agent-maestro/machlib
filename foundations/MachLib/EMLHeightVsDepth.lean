import MachLib.EMLHeightInterface
import MachLib.EMLLadderMeasure

/-!
# Exponential height versus depth, and why height is not a ladder

`EMLHeightInterface` proves `HeightModel.eh_le_depth` — a depth-`j` tree has height at most `j` — and
its docstring calls `eh_sub` "the axiom the whole reframing turns on, and the one no tree measure
satisfies". `EMLLadderMeasure` separately proves that no `Nat`-valued measure descending strictly to
*both* children can carry the decay induction. This module is the bridge, and it says three things
the two files did not say jointly.

**1. `depth` is not the sharp bound; `ehTree` is.** The *syntactic* exponential height

    ehTree (eml A B) = max (ehTree A + 1) (ehTree B)

reads the `HeightModel` axioms off the tree — `exp` costs one over the left child, `log` costs
nothing over the right, subtraction stays in the layer — and `eh_le_ehTree` shows every model is
bounded by it. Since `ehTree_le_depth`, the existing `eh_le_depth` factors through this, and the
factorisation is **strict**: a right spine of depth 3 has `ehTree = 1`.

**2. Height satisfies `left_le` and FAILS `right_le`.** `ehTree` is a perfectly good measure going
left, and going right it does not descend at all — an `eml` node whose right child already carries
the maximum height buys nothing. So `no_ladderMeasure_with_ehTree`: height is not a `LadderMeasure`,
and the failure is **on the right**.

**3. That is the same side the germ route fails on.** `tower_height_does_not_descend_right`
(`EMLLadderMeasure`, §4) reaches the identical obstruction from the analytic side — a node
non-positive on `[1,∞)` whose right child is an arbitrarily tall tower. Two independent routes, one
obstruction, one side. The syntactic version here is three lines; the germ version needed the tower
machinery. Recording both is the point: it says the obstruction is structural, not an artifact of
either route.

**Provenance.** The choice to look here came from outside Lean. A complex-analytic probe
(`monogate-research/exploration/Frontier_G_monodromy_2026_08_27/`, Findings 7–8) measured the
branch-point locus of EML trees over `ℂ` and found its growth regime — finite, linear, exponential —
tracked by exponential height and **not** by depth, on two pairs of trees of *equal depth*. That
measurement is not transportable (`MachLib.Real` has no `Complex`) and nothing below cites it. What
transports is which statement was worth proving.

**Scope.** `ehTree` is a *syntactic* bound and it overcounts: `eml (eml (const 0) var) var` evaluates
to `exp (1 - log x) - log x = e/x - log x`, whose true height is `0`, while `ehTree = 2`. The slack
is in `eh_exp` — `eh (exp f) ≤ eh f + 1` is strict exactly when `f` does not grow — and closing it
needs `eh` of a quotient, which `HeightModel` does not axiomatise. Nothing here narrows
`LeadingMonomialFloor`, which is where `decayFloor_of_heightModel` is actually stuck.
-/

namespace MachLib

open Real

namespace EMLTree

/-- **Syntactic exponential height.** The `HeightModel` closure axioms read off the tree: `exp` costs
one level over the left child, `log` costs nothing over the right, and the subtraction joining them
stays inside the layer. Note the asymmetry — it is `Nat.max`, not `1 +` — which is exactly what makes
it sharper than `depth` and, below, what makes it fail on the right. -/
def ehTree : EMLTree → Nat
  | const _   => 0
  | var       => 0
  | eml A B   => Nat.max (A.ehTree + 1) B.ehTree

/-- **Height is bounded by depth**, so the sharper bound below implies the existing one. -/
theorem ehTree_le_depth : ∀ t : EMLTree, t.ehTree ≤ t.depth := by
  intro t
  induction t with
  | const c => exact Nat.le_refl 0
  | var     => exact Nat.le_refl 0
  | eml A B ihA ihB =>
      have hA1 : A.depth ≤ Nat.max A.depth B.depth := Nat.le_max_left _ _
      have hB1 : B.depth ≤ Nat.max A.depth B.depth := Nat.le_max_right _ _
      show Nat.max (A.ehTree + 1) B.ehTree ≤ 1 + Nat.max A.depth B.depth
      exact Nat.max_le.mpr ⟨by omega, by omega⟩

/-- **The bound is STRICT.** A right spine `1 - log (1 - log (1 - log x))` has depth `3` and height
`1`: every `eml` node on it puts a *constant* in the left child, and `exp` of a constant costs one
level once, not once per node. Depth counts nesting; height counts how many `exp`s stack. -/
theorem ehTree_lt_depth_witness :
    ∃ t : EMLTree, t.ehTree = 1 ∧ t.depth = 3 :=
  ⟨eml (const 0) (eml (const 0) (eml (const 0) var)), rfl, rfl⟩

/-- **Height descends to the LEFT child**, by one, always — `LadderMeasure.left_le` at `step = 1`. -/
theorem ehTree_left_le (A B : EMLTree) : A.ehTree + 1 ≤ (eml A B).ehTree :=
  Nat.le_max_left _ _

/-- **Height does NOT descend to the right child, for any positive step.** Witness:
`eml var (eml var var)`. Its right child already has height `1`, and the node has height
`max (0 + 1) 1 = 1` — the node buys nothing over a right child that is already the taller of the two.
This is `LadderMeasure.right_le` failing, and it is not a matter of choosing a smaller `step`: the
gap is exactly zero. -/
theorem ehTree_not_right_le (step : Nat) (hstep : 0 < step) :
    ¬ (∀ A B : EMLTree, B.ehTree + step ≤ (eml A B).ehTree) := by
  intro h
  have hchild : (eml var var).ehTree = 1 := rfl
  have hnode  : (eml var (eml var var)).ehTree = 1 := rfl
  have hle := h var (eml var var)
  rw [hchild, hnode] at hle
  omega

/-- **The syntactic height OVERCOUNTS, and this is the witness.** `eml (eml (const 0) var) var` has
`ehTree = 2`, but on `x > 0` it evaluates to `e/x - log x` — a rational term minus a log, whose true
exponential height is `0`. The `exp` is applied to `1 - log x`, which does not grow, so it buys no
level; the slack is in `eh_exp`, whose `≤` is strict exactly there.

This is why `ehTree` is a *bound* and not the parameter itself, and why the sharpening chain
`eh ≤ ehTree ≤ depth` has slack at **both** steps. Closing the first needs `eh` of a quotient, which
`HeightModel` does not axiomatise — a limit of the interface, not of the tree. -/
theorem ehTree_overcounts_witness {x : Real} (hx : 0 < x) :
    (eml (eml (const 0) var) var).eval x = exp 1 / x - log x
      ∧ (eml (eml (const 0) var) var).ehTree = 2 := by
  refine ⟨?_, rfl⟩
  show exp (exp 0 - log x) - log x = exp 1 / x - log x
  rw [exp_zero, exp_sub, exp_log hx]

end EMLTree

/-- **Every height model is bounded by the syntactic height** — sharper than `eh_le_depth`, same four
lines, and it is where the `Nat.max` in `ehTree` comes from: `eh_sub` keeps the node in the worse of
its two layers rather than adding one to it. -/
theorem HeightModel.eh_le_ehTree (M : HeightModel) : ∀ t : EMLTree, M.eh t.eval ≤ t.ehTree := by
  intro t
  induction t with
  | const c =>
      show M.eh (fun _ => c) ≤ 0
      rw [M.eh_const c]
      exact Nat.le_refl 0
  | var =>
      show M.eh (fun x => x) ≤ 0
      rw [M.eh_id]
      exact Nat.le_refl 0
  | eml A B ihA ihB =>
      have hsub := M.eh_sub (fun x => exp (A.eval x)) (fun x => log (B.eval x))
      have hexp := M.eh_exp A.eval
      have hlog := M.eh_log B.eval
      have hl : A.ehTree + 1 ≤ Nat.max (A.ehTree + 1) B.ehTree := Nat.le_max_left _ _
      have hr : B.ehTree ≤ Nat.max (A.ehTree + 1) B.ehTree := Nat.le_max_right _ _
      have hmaxle : Nat.max (M.eh (fun x => exp (A.eval x))) (M.eh (fun x => log (B.eval x)))
          ≤ Nat.max (A.ehTree + 1) B.ehTree :=
        Nat.max_le.mpr ⟨by omega, by omega⟩
      show M.eh (fun x => exp (A.eval x) - log (B.eval x)) ≤ Nat.max (A.ehTree + 1) B.ehTree
      exact Nat.le_trans hsub hmaxle

/-- **`eh_le_depth` factors through the syntactic height**, and by `ehTree_lt_depth_witness` the
first inequality is strict on a right spine. So depth was never the parameter — it is a bound on the
parameter, loose by as much as the tree is right-heavy. -/
theorem HeightModel.eh_le_depth_via_ehTree (M : HeightModel) (t : EMLTree) :
    M.eh t.eval ≤ t.depth :=
  Nat.le_trans (M.eh_le_ehTree t) (EMLTree.ehTree_le_depth t)

/-- **Exponential height is not a ladder measure.** Any `LadderMeasure` demands a strictly positive
descent to *both* children; height gives one to the left and none to the right. So the reframing that
`EMLHeightInterface` builds on cannot be run as a structural induction — which is consistent with,
and independent of, `EMLLadderMeasure`'s germ-side result that growth does not descend right either.

The two arguments share no machinery: this one is `Nat.max` arithmetic on the syntax, that one builds
a node non-positive on `[1,∞)` whose right child is an `(n+1)`-tower. They fail on the same side. -/
theorem no_ladderMeasure_with_ehTree (L : LadderMeasure) : L.μ ≠ EMLTree.ehTree := by
  intro hmu
  refine EMLTree.ehTree_not_right_le L.step L.step_pos ?_
  intro A B
  have := L.right_le A B
  rw [hmu] at this
  exact this

/-- **Specimen: the theorem above rules something out.** `LadderMeasure` is inhabited —
`depthMeasure` and `sizeMeasure` are both defined in `EMLLadderMeasure` — so
`no_ladderMeasure_with_ehTree` is not true for want of a subject. Instantiated at `depthMeasure`,
whose `μ` is `depth`, it says the two measures differ as functions, which
`ehTree_lt_depth_witness` exhibits at a right spine of depth `3`.

Shipping this alongside the capstone is the `positive_branch_impossible` lesson: a theorem
quantified over a structure proves nothing until something inhabits the structure. -/
theorem depth_ne_ehTree : EMLTree.depth ≠ EMLTree.ehTree :=
  no_ladderMeasure_with_ehTree depthMeasure

/-! ## §2 — the payoff: the same input buys a strictly larger class of trees

`decayFloor_of_heightModel` spends `eh_le_depth` and concludes `DecayFloor`, which quantifies over
`t.depth ≤ j`. That reduction is **lossy**: `LeadingMonomialFloor` constrains height, so it was
always giving a floor for every tree of *height* `≤ j`, and the depth-indexed conclusion throws away
every tree whose height is below its depth. Since `ehTree_lt_depth_witness` says that set is
non-empty, the loss is real, and recovering it costs nothing — the same input, one lemma swapped.
-/

/-- **`DecayFloor` indexed by syntactic height.** Identical to `DecayFloor` with `ehTree` in place of
`depth`. -/
def DecayFloorByHeight : Prop :=
  ∀ j : Nat, ∃ k : Nat, ∀ (t : EMLTree) (X₀ : Real), t.ehTree ≤ j → 1 ≤ X₀ →
    (∀ x : Real, X₀ ≤ x → 0 < t.eval x) →
    ∃ X₁ : Real, X₀ ≤ X₁ ∧ ∀ x : Real, X₁ ≤ x →
      exp (-(EMLTree.towerFn k x)) ≤ t.eval x

/-- **The same hypothesis as `decayFloor_of_heightModel`, and a stronger conclusion.** Only the
bridging lemma changes: `eh_le_ehTree` where that proof used `eh_le_depth`. -/
theorem decayFloorByHeight_of_heightModel (M : HeightModel) (h : LeadingMonomialFloor M) :
    DecayFloorByHeight := by
  intro j
  obtain ⟨m, hm⟩ := h j
  refine ⟨m, ?_⟩
  intro t X₀ hh hX₀ hpos
  exact hm t X₀ (Nat.le_trans (M.eh_le_ehTree t) hh) hX₀ hpos

/-- **And it still gives the original**, through `ehTree_le_depth`. So nothing is lost by stating the
height version and `decayFloor_of_heightModel` is a corollary of it. -/
theorem decayFloor_of_decayFloorByHeight (h : DecayFloorByHeight) : DecayFloor := by
  intro j
  obtain ⟨k, hk⟩ := h j
  refine ⟨k, ?_⟩
  intro t X₀ hdepth hX₀ hpos
  exact hk t X₀ (Nat.le_trans (EMLTree.ehTree_le_depth t) hdepth) hX₀ hpos

/-- **The strengthening is not cosmetic.** At level `j = 1` the height-indexed statement already
covers the right spine `1 - log (1 - log (1 - log x))`, which the depth-indexed one does not reach
until `j = 3`. Right spines of any length have height `1`, so at each fixed level the height index
covers an infinite family the depth index never reaches.

What it does **not** claim is a smaller floor. `LeadingMonomialFloor` gives one `m` per level with no
monotonicity in the level, so reaching a tree at level `1` instead of level `3` is not known to buy a
shorter tower. The gain is coverage, and only coverage.

**The converse is not proved.** `DecayFloor → DecayFloorByHeight` would need a floor at depth `j` to
constrain trees of unbounded depth, and nothing here supplies that. The two are not known to be
equivalent, and the ledger is not told they are. -/
theorem height_index_covers_more :
    ∃ t : EMLTree, t.ehTree ≤ 1 ∧ ¬ (t.depth ≤ 1) := by
  refine ⟨EMLTree.eml (EMLTree.const 0)
            (EMLTree.eml (EMLTree.const 0) (EMLTree.eml (EMLTree.const 0) EMLTree.var)), ?_, ?_⟩
  · exact Nat.le_refl 1
  · intro h
    have e : (EMLTree.eml (EMLTree.const 0)
        (EMLTree.eml (EMLTree.const 0) (EMLTree.eml (EMLTree.const 0) EMLTree.var))).depth = 3 := rfl
    rw [e] at h
    omega

end MachLib
