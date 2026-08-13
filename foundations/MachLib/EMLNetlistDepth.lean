import MachLib.EMLDepth2InvX
import MachLib.EMLSizeCost

/-!
# What a tree lower bound says about a DATAPATH

`d(1/x) = 4` and `s(1/x) ≥ 9` are facts about *trees*. Hardware is not a tree: a netlist is a DAG,
and every real datapath shares subexpressions. So the question that decides whether the reciprocal
lower-bound programme has any downstream meaning is: **which tree bounds survive sharing?**

The answer is asymmetric, and it inverts the naive guess.

* **Depth survives exactly.** Unfolding a DAG into a tree can blow the node count up
  exponentially, and it changes the depth by **nothing** (`netDepth_eq_depth`). So
  `inv_x_not_in_eml_depth_le_3` transfers verbatim: *no* straight-line EML program computes `1/x`
  with combinational block-depth `< 4` (`inv_x_netlist_depth_ge_four`), and therefore its output
  cannot sit before index 4 — at least five instruction slots (`inv_x_netlist_index_ge_four`).

* **Size survives only as a logarithmic shadow.** `sqProg` is `n+1` instructions whose unfolding
  has `2^(n+1) - 1` nodes (`sqProg_size`); concretely `sqProg_gap_at_four` — 5 instructions, 31
  nodes. Sharing is exactly the operation that makes node counts lie. It is **not** true that the
  size bound transfers nothing: `unfold_size_le` bounds the unfolding by `2^(i+1)`, so
  `s(1/x) ≥ 9` does force an output index `≥ 3` (`inv_x_netlist_index_ge_three_from_size`). But the
  depth route forces `≥ 4`, so **the size bound is real and strictly dominated**. The reciprocal's
  size question — `s(1/x) ∈ {9,11}` — therefore refines a quantity about the tree encoding that no
  datapath bound depends on.

**Two things this rests on, both explicit rather than implicit.**

`progEval_eq_unfold_eval` — the datapath's own semantics (read earlier results, share them) agrees
with its unfolding's. Without it `unfoldAt` would be a definition nobody had to accept, and a tree
lower bound would constrain nothing; every transfer theorem below takes its hypothesis on
`progEvalAt`, i.e. on the *program*.

`netWDepth_eq_wdepth` — the depth invariance is not special to unit weights. **Any path-additive
cost survives sharing exactly**, because `(+, max)` is blind to sharing while node-counting is not.
That is the algebraic reason for the whole asymmetry, and it is the socket a measured per-block
latency, LUT-depth or energy figure plugs into without re-proving the bridge.

**What may be plugged into that socket — a trap found by measuring.** The weight must be a quantity
that genuinely accumulates along a **serial dependency chain**. Three natural instantiations, one
correct (`forge/reports/eml_block_cost_2026_08_11.md`, yosys + verilator):

* `we` = **cycles per block** → `netWDepth` is total latency. **Correct.** A measured 5-cycle block
  gives `≥ 20` cycles for `1/x`.
* `we` = **combinational logic levels** → `netWDepth` returns `4 × 90 = 360`, a true fact about a
  weighted tree that **is not the physical critical path** of a *pipelined* artifact: a measured
  4-deep chain has the same critical path as one block (**×1.00**), because registers break it.
  **This is the one instantiation whose correctness depends on the lowering, and both sides are now
  measured.** Removing the pipeline registers and re-measuring the identical arithmetic sends the
  ratio to **×3.55** — so combinational depth *is* path-additive when nothing breaks the path, and
  stops being so the moment a register is inserted. The theorem does not know registers exist; the
  artifact decides whether it applies. (`×3.55` and not `×4` because, with no registers between
  blocks, the synthesiser optimises across the boundaries.)
* **area** → not a critical-path quantity at all. It sums over *blocks*, not along the *longest
  path*, and needs a distinct-node count — precisely the quantity that does **not** survive sharing.
  Wrong theorem, and the one whose measured ratio (**×4.00**) looks most like a confirmation.

A weight that is not path-additive in the physical artifact makes the conclusion false while leaving
the theorem true. Latency is path-additive unconditionally; combinational depth is path-additive
**exactly when the lowering leaves the path unbroken**; area never was. Only the middle one is
contingent, and that contingency is measured rather than argued.

**The invariant ledger, now for two arrows.** Asking *what survives each compiler transformation?*
is the general form of this module's question, and two arrows are answered:

| quantity | tree → DAG (sharing) | DAG → schedule (resource sharing) |
|---|---|---|
| **depth / latency** | preserved exactly (`netDepth_eq_depth`) | **floor survives** (`schedule_ge_wdepth`) |
| **size / area** | destroyed — exponential (`sqProg_size`) | destroyed — one block can serve every node |
| critical path | preserved (a per-stage quantity) | preserved (a per-stage quantity) |

**Depth is the only quantity that survives both.** The second arrow is where the measured `×4.00`
area multiplier dies: a time-multiplexed datapath reuses one block across cycles, so area becomes
`O(1)` in depth while latency cannot fall below `L ·  d` however many blocks are allocated
(`inv_x_schedule_ge_four_L`). Area's apparent agreement with the depth bound in the unshared
lowering was a property of *that* lowering, not of the quantity.

**Scope.** "Datapath" here means a straight-line program over the EML primitive
`(a, b) ↦ exp a − log b`, which is the block Forge's hardware lane emits. Nothing here bounds
gate-depth *inside* a block, and nothing here is a lower bound against arbitrary circuits — that
would be a circuit-complexity claim and this is not one. What is proved is that within the class of
EML-structured datapaths, tree depth is a faithful cost and tree size is not.

**The overclaim this must never become.** If a synthesised block measures 6 ns, `d(1/x) = 4` does
*not* give "every reciprocal circuit needs 24 ns". Four serial *abstract* EML dependencies is what
is proved; nothing here rules out retiming, pipelining, a different internal implementation, or a
different technology. A universal nanosecond floor would be physical circuit complexity and is not
in reach. What a measurement licenses is a statement about *one synthesised artifact*, reported
alongside the structural bound and never fused with it.
-/

namespace MachLib

/-- One instruction of a straight-line EML program. `eml a b` reads the results of the
instructions at indices `a` and `b`. -/
inductive EMLInstr : Type where
  | const : Real → EMLInstr
  | var   : EMLInstr
  | eml   : Nat → Nat → EMLInstr

/-- Well-formedness: an instruction may only read strictly earlier results. This is what makes the
program a DAG rather than a cyclic netlist, and it is the only structural assumption used. -/
def ProgWf (p : Nat → EMLInstr) : Prop :=
  ∀ i a b : Nat, p i = EMLInstr.eml a b → a < i ∧ b < i

/-- Unfold the value at index `i` into a tree. Fuel-driven so the definition is total without a
well-founded recursion; `unfoldAt` supplies enough, and `unfold_fuel_irrelevant` shows the surplus
is invisible. **This is where the exponential blowup happens** — a shared node is copied once per
path that reaches it. -/
noncomputable def unfold (p : Nat → EMLInstr) : Nat → Nat → EMLTree
  | 0, _ => EMLTree.const 0
  | Nat.succ f, i =>
    match p i with
    | EMLInstr.const c => EMLTree.const c
    | EMLInstr.var => EMLTree.var
    | EMLInstr.eml a b => EMLTree.eml (unfold p f a) (unfold p f b)

/-- The tree computed at index `i`. Index `i` needs `i+1` fuel: each level drops the index by at
least one. -/
noncomputable def unfoldAt (p : Nat → EMLInstr) (i : Nat) : EMLTree := unfold p (i + 1) i

/-- The netlist's own depth, defined on the program rather than on the unfolding — so that
`netDepth_eq_depth` is a theorem about two independently-given notions and not a restatement. -/
def netDepth (p : Nat → EMLInstr) : Nat → Nat → Nat
  | 0, _ => 0
  | Nat.succ f, i =>
    match p i with
    | EMLInstr.const _ => 0
    | EMLInstr.var => 0
    | EMLInstr.eml a b => 1 + max (netDepth p f a) (netDepth p f b)

/-- Combinational depth of the datapath feeding index `i`. -/
def netDepthAt (p : Nat → EMLInstr) (i : Nat) : Nat := netDepth p (i + 1) i

-- ▸ Fuel hygiene.

/-- Surplus fuel changes nothing, so `unfoldAt` names a single well-defined tree. -/
theorem unfold_fuel_irrelevant (p : Nat → EMLInstr) (hwf : ProgWf p) :
    ∀ f1 f2 i : Nat, i < f1 → i < f2 → unfold p f1 i = unfold p f2 i := by
  intro f1
  induction f1 with
  | zero => intro f2 i h1 _; exact absurd h1 (Nat.not_lt_zero i)
  | succ f ih =>
    intro f2 i h1 h2
    cases f2 with
    | zero => exact absurd h2 (Nat.not_lt_zero i)
    | succ g =>
      show (match p i with
            | EMLInstr.const c => EMLTree.const c
            | EMLInstr.var => EMLTree.var
            | EMLInstr.eml a b => EMLTree.eml (unfold p f a) (unfold p f b)) = _
      show _ = (match p i with
            | EMLInstr.const c => EMLTree.const c
            | EMLInstr.var => EMLTree.var
            | EMLInstr.eml a b => EMLTree.eml (unfold p g a) (unfold p g b))
      cases hp : p i with
      | const c => rfl
      | var => rfl
      | eml a b =>
        have hab := hwf i a b hp
        have hai : a < i := hab.1
        have hbi : b < i := hab.2
        have haf : a < f := Nat.lt_of_lt_of_le hai (Nat.le_of_lt_succ h1)
        have hag : a < g := Nat.lt_of_lt_of_le hai (Nat.le_of_lt_succ h2)
        have hbf : b < f := Nat.lt_of_lt_of_le hbi (Nat.le_of_lt_succ h1)
        have hbg : b < g := Nat.lt_of_lt_of_le hbi (Nat.le_of_lt_succ h2)
        show EMLTree.eml (unfold p f a) (unfold p f b)
               = EMLTree.eml (unfold p g a) (unfold p g b)
        rw [ih g a haf hag, ih g b hbf hbg]

-- ▸ Depth survives the unfolding EXACTLY.

/-- **The netlist's depth is its unfolding's depth.** No hypothesis on the program is needed: the
two recursions have the same shape, which is precisely the statement that sharing is invisible to
depth. -/
theorem netDepth_eq_depth (p : Nat → EMLInstr) :
    ∀ f i : Nat, netDepth p f i = (unfold p f i).depth := by
  intro f
  induction f with
  | zero => intro i; rfl
  | succ f ih =>
    intro i
    show (match p i with
          | EMLInstr.const _ => 0
          | EMLInstr.var => 0
          | EMLInstr.eml a b => 1 + max (netDepth p f a) (netDepth p f b)) = _
    show _ = EMLTree.depth (match p i with
          | EMLInstr.const c => EMLTree.const c
          | EMLInstr.var => EMLTree.var
          | EMLInstr.eml a b => EMLTree.eml (unfold p f a) (unfold p f b))
    cases hp : p i with
    | const c => rfl
    | var => rfl
    | eml a b =>
      show 1 + max (netDepth p f a) (netDepth p f b)
             = (EMLTree.eml (unfold p f a) (unfold p f b)).depth
      rw [ih a, ih b]; rfl

theorem netDepthAt_eq_depth (p : Nat → EMLInstr) (i : Nat) :
    netDepthAt p i = (unfoldAt p i).depth := netDepth_eq_depth p (i + 1) i

/-- Each level of the unfolding drops the index by at least one, so depth is bounded by the index.
This is what turns a depth bound into a bound on *where the output can sit*. -/
theorem unfold_depth_le_index (p : Nat → EMLInstr) (hwf : ProgWf p) :
    ∀ f i : Nat, i < f → (unfold p f i).depth ≤ i := by
  intro f
  induction f with
  | zero => intro i h; exact absurd h (Nat.not_lt_zero i)
  | succ f ih =>
    intro i hi
    show EMLTree.depth (match p i with
          | EMLInstr.const c => EMLTree.const c
          | EMLInstr.var => EMLTree.var
          | EMLInstr.eml a b => EMLTree.eml (unfold p f a) (unfold p f b)) ≤ i
    cases hp : p i with
    | const c => exact Nat.zero_le i
    | var => exact Nat.zero_le i
    | eml a b =>
      have hab := hwf i a b hp
      have hai : a < i := hab.1
      have hbi : b < i := hab.2
      have haf : a < f := Nat.lt_of_lt_of_le hai (Nat.le_of_lt_succ hi)
      have hbf : b < f := Nat.lt_of_lt_of_le hbi (Nat.le_of_lt_succ hi)
      have da := ih a haf
      have db := ih b hbf
      have hmax : max (unfold p f a).depth (unfold p f b).depth ≤ i - 1 := by
        rcases Nat.le_total (unfold p f a).depth (unfold p f b).depth with hle | hle
        · rw [Nat.max_eq_right hle]; omega
        · rw [Nat.max_eq_left hle]; omega
      show 1 + max (unfold p f a).depth (unfold p f b).depth ≤ i
      omega

theorem netDepthAt_le_index (p : Nat → EMLInstr) (hwf : ProgWf p) (i : Nat) :
    netDepthAt p i ≤ i := by
  rw [netDepthAt_eq_depth]
  exact unfold_depth_le_index p hwf (i + 1) i (Nat.lt_succ_self i)


-- ▸ The datapath's OWN semantics, and the fact that unfolding preserves it.

/-- Evaluate the program the way hardware does: read the results of earlier instructions, sharing
them. Nothing is duplicated here — this is the DAG's semantics, not the tree's. -/
noncomputable def progEval (p : Nat → EMLInstr) : Nat → Nat → Real → Real
  | 0, _, _ => 0
  | Nat.succ f, i, x =>
    match p i with
    | EMLInstr.const c => c
    | EMLInstr.var => x
    | EMLInstr.eml a b => Real.exp (progEval p f a x) - Real.log (progEval p f b x)

noncomputable def progEvalAt (p : Nat → EMLInstr) (i : Nat) (x : Real) : Real :=
  progEval p (i + 1) i x

/-- **Unfolding preserves semantics.** Load-bearing for every transfer below: without it,
`unfoldAt` would be a definition nobody had to accept, and a tree lower bound would constrain
nothing. With it, the datapath and its unfolding compute the same function, so tree lower bounds
descend to programs. -/
theorem progEval_eq_unfold_eval (p : Nat → EMLInstr) :
    ∀ f i : Nat, ∀ x : Real, progEval p f i x = (unfold p f i).eval x := by
  intro f
  induction f with
  | zero => intro i x; rfl
  | succ f ih =>
    intro i x
    show (match p i with
          | EMLInstr.const c => c
          | EMLInstr.var => x
          | EMLInstr.eml a b => Real.exp (progEval p f a x) - Real.log (progEval p f b x)) = _
    show _ = EMLTree.eval (match p i with
          | EMLInstr.const c => EMLTree.const c
          | EMLInstr.var => EMLTree.var
          | EMLInstr.eml a b => EMLTree.eml (unfold p f a) (unfold p f b)) x
    cases hp : p i with
    | const c => rfl
    | var => rfl
    | eml a b =>
      show Real.exp (progEval p f a x) - Real.log (progEval p f b x)
             = (EMLTree.eml (unfold p f a) (unfold p f b)).eval x
      rw [ih a x, ih b x]; rfl

theorem progEvalAt_eq_unfoldAt_eval (p : Nat → EMLInstr) (i : Nat) (x : Real) :
    progEvalAt p i x = (unfoldAt p i).eval x := progEval_eq_unfold_eval p (i + 1) i x

-- ▸ Weighted critical path: the durable form.

/-- Critical-path cost of a tree under per-kind block weights. `wdepth 0 0 1` is `depth`. -/
def EMLTree.wdepth (wc wv we : Nat) : EMLTree → Nat
  | EMLTree.const _ => wc
  | EMLTree.var => wv
  | EMLTree.eml a b => we + max (a.wdepth wc wv we) (b.wdepth wc wv we)

/-- The same cost read off the program. -/
def netWDepth (p : Nat → EMLInstr) (wc wv we : Nat) : Nat → Nat → Nat
  | 0, _ => wc   -- `unfold` at zero fuel yields `const 0`, so the base case must agree with `wc`
  | Nat.succ f, i =>
    match p i with
    | EMLInstr.const _ => wc
    | EMLInstr.var => wv
    | EMLInstr.eml a b => we + max (netWDepth p wc wv we f a) (netWDepth p wc wv we f b)

/-- **Any path-additive cost survives sharing exactly** — not just the unit-weight depth. This is
the socket a measured per-block latency, LUT-depth, or energy figure plugs into without re-proving
the structural bridge. Still no hypothesis on the program: `(+, max)` is simply blind to sharing. -/
theorem netWDepth_eq_wdepth (p : Nat → EMLInstr) (wc wv we : Nat) :
    ∀ f i : Nat, netWDepth p wc wv we f i = (unfold p f i).wdepth wc wv we := by
  intro f
  induction f with
  | zero => intro i; rfl
  | succ f ih =>
    intro i
    show (match p i with
          | EMLInstr.const _ => wc
          | EMLInstr.var => wv
          | EMLInstr.eml a b => we + max (netWDepth p wc wv we f a) (netWDepth p wc wv we f b)) = _
    show _ = EMLTree.wdepth wc wv we (match p i with
          | EMLInstr.const c => EMLTree.const c
          | EMLInstr.var => EMLTree.var
          | EMLInstr.eml a b => EMLTree.eml (unfold p f a) (unfold p f b))
    cases hp : p i with
    | const c => rfl
    | var => rfl
    | eml a b =>
      show we + max (netWDepth p wc wv we f a) (netWDepth p wc wv we f b)
             = (EMLTree.eml (unfold p f a) (unfold p f b)).wdepth wc wv we
      rw [ih a, ih b]; rfl

/-- The unit-weight instance is the ordinary depth, so `netDepth_eq_depth` is the `(0,0,1)` case of
the weighted theorem and not an independent fact. -/
theorem wdepth_unit_eq_depth : ∀ t : EMLTree, t.wdepth 0 0 1 = t.depth := by
  intro t
  induction t with
  | const c => rfl
  | var => rfl
  | eml a b iha ihb =>
    show 1 + max (a.wdepth 0 0 1) (b.wdepth 0 0 1) = 1 + max a.depth b.depth
    rw [iha, ihb]

-- ▸ What the SIZE bound really transfers: a logarithmic shadow.

/-- Unfolding at index `i` can at most double per level, so the tree it produces has fewer than
`2^(i+1)` nodes. This is the exact sense in which a tree-size bound survives sharing — with
exponential loss. -/
theorem unfold_size_le (p : Nat → EMLInstr) (hwf : ProgWf p) :
    ∀ f i : Nat, i < f → (unfold p f i).size + 1 ≤ 2 ^ (i + 1) := by
  intro f
  induction f with
  | zero => intro i h; exact absurd h (Nat.not_lt_zero i)
  | succ f ih =>
    intro i hi
    show EMLTree.size (match p i with
          | EMLInstr.const c => EMLTree.const c
          | EMLInstr.var => EMLTree.var
          | EMLInstr.eml a b => EMLTree.eml (unfold p f a) (unfold p f b)) + 1 ≤ 2 ^ (i + 1)
    have hpow1 : (2 : Nat) ^ 1 ≤ 2 ^ (i + 1) :=
      Nat.pow_le_pow_right (by omega) (by omega)
    cases hp : p i with
    | const c => show 1 + 1 ≤ 2 ^ (i + 1); omega
    | var => show 1 + 1 ≤ 2 ^ (i + 1); omega
    | eml a b =>
      have hab := hwf i a b hp
      have haf : a < f := Nat.lt_of_lt_of_le hab.1 (Nat.le_of_lt_succ hi)
      have hbf : b < f := Nat.lt_of_lt_of_le hab.2 (Nat.le_of_lt_succ hi)
      have ha := ih a haf
      have hb := ih b hbf
      have hai : (2 : Nat) ^ (a + 1) ≤ 2 ^ i := Nat.pow_le_pow_right (by omega) (by omega)
      have hbi : (2 : Nat) ^ (b + 1) ≤ 2 ^ i := Nat.pow_le_pow_right (by omega) (by omega)
      have hsplit : (2 : Nat) ^ (i + 1) = 2 ^ i + 2 ^ i := by
        rw [Nat.pow_succ]; omega
      show 1 + (unfold p f a).size + (unfold p f b).size + 1 ≤ 2 ^ (i + 1)
      omega

/-- **The size bound's shadow, and its strict domination.** `s(1/x) ≥ 9` forces the output index to
be at least **3**; the depth route forces at least **4**. So tree size does transfer — with
exponential loss, into a bound the depth bound already beats. "Carries nothing" would be wrong;
"carries a logarithmic shadow, strictly dominated" is right. -/
theorem inv_x_netlist_index_ge_three_from_size (p : Nat → EMLInstr) (hwf : ProgWf p) (i : Nat)
    (h : ∀ x : Real, 0 < x → progEvalAt p i x = 1 / x) :
    3 ≤ i := by
  have hev : ∀ x : Real, 0 < x → (unfoldAt p i).eval x = 1 / x := by
    intro x hx; rw [← progEvalAt_eq_unfoldAt_eval]; exact h x hx
  have h9 : 9 ≤ (unfoldAt p i).size := inv_x_size_ge_nine (unfoldAt p i) hev
  have hle : (unfoldAt p i).size + 1 ≤ 2 ^ (i + 1) :=
    unfold_size_le p hwf (i + 1) i (Nat.lt_succ_self i)
  rcases Nat.lt_or_ge i 3 with hlt | hge
  · exfalso
    have hb : (2 : Nat) ^ (i + 1) ≤ 2 ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
    have h8 : (2 : Nat) ^ 3 = 8 := rfl
    have hchain : (unfoldAt p i).size + 1 ≤ 8 :=
      Nat.le_trans hle (Nat.le_trans hb (Nat.le_of_eq h8))
    omega
  · exact hge

-- ▸ The transfer.

/-- **`1/x` needs combinational block-depth ≥ 4 in any straight-line EML datapath.**

`inv_x_not_in_eml_depth_le_3` is a statement about trees; `netDepth_eq_depth` is what makes it a
statement about hardware. Sharing cannot help, because sharing does not change depth. -/
theorem inv_x_netlist_depth_ge_four (p : Nat → EMLInstr) (i : Nat)
    (hp : ∀ x : Real, 0 < x → progEvalAt p i x = 1 / x) :
    4 ≤ netDepthAt p i := by
  have h : ∀ x : Real, 0 < x → (unfoldAt p i).eval x = 1 / x := by
    intro x hx; rw [← progEvalAt_eq_unfoldAt_eval]; exact hp x hx
  rw [netDepthAt_eq_depth]
  have hno : ¬ ((unfoldAt p i).depth ≤ 3) :=
    fun h3 => inv_x_not_in_eml_depth_le_3 (unfoldAt p i) h3 h
  omega

/-- **…hence its output cannot sit before index 4:** at least five instruction slots. A resource
statement about the program, obtained from a statement about trees. -/
theorem inv_x_netlist_index_ge_four (p : Nat → EMLInstr) (hwf : ProgWf p) (i : Nat)
    (hp : ∀ x : Real, 0 < x → progEvalAt p i x = 1 / x) :
    4 ≤ i := by
  have hd := inv_x_netlist_depth_ge_four p i hp
  have hi := netDepthAt_le_index p hwf i
  omega

-- ▸ Size does NOT transfer: the witness.

/-- Repeated squaring of the sharing structure: `n+1` instructions, each reading the previous one
twice. -/
def sqProg : Nat → EMLInstr
  | 0 => EMLInstr.var
  | Nat.succ k => EMLInstr.eml k k

theorem sqProg_wf : ProgWf sqProg := by
  intro i a b h
  cases i with
  | zero =>
    have hv : EMLInstr.var = EMLInstr.eml a b := h
    exact EMLInstr.noConfusion hv
  | succ k =>
    have hh : EMLInstr.eml k k = EMLInstr.eml a b := h
    injection hh with h1 h2
    exact ⟨by omega, by omega⟩

/-- `n+1` instructions unfold to a tree of depth `n` and `2^(n+1) - 1` nodes. -/
theorem sqProg_unfold (f : Nat) :
    ∀ n : Nat, n < f →
      (unfold sqProg f n).depth = n ∧ (unfold sqProg f n).size + 1 = 2 ^ (n + 1) := by
  induction f with
  | zero => intro n h; exact absurd h (Nat.not_lt_zero n)
  | succ f ih =>
    intro n hn
    cases n with
    | zero =>
      constructor
      · show EMLTree.depth (match sqProg 0 with
              | EMLInstr.const c => EMLTree.const c
              | EMLInstr.var => EMLTree.var
              | EMLInstr.eml a b => EMLTree.eml (unfold sqProg f a) (unfold sqProg f b)) = 0
        rfl
      · show EMLTree.size (match sqProg 0 with
              | EMLInstr.const c => EMLTree.const c
              | EMLInstr.var => EMLTree.var
              | EMLInstr.eml a b => EMLTree.eml (unfold sqProg f a) (unfold sqProg f b)) + 1
              = 2 ^ (0 + 1)
        rfl
    | succ k =>
      have hkf : k < f := Nat.lt_of_succ_lt_succ hn
      have hk := ih k hkf
      have hpow : (2 : Nat) ^ (k + 1 + 1) = 2 * 2 ^ (k + 1) := by
        rw [Nat.pow_succ]; omega
      constructor
      · show EMLTree.depth (EMLTree.eml (unfold sqProg f k) (unfold sqProg f k)) = k + 1
        show 1 + max (unfold sqProg f k).depth (unfold sqProg f k).depth = k + 1
        rw [hk.1]
        simp only [Nat.max_self]
        omega
      · show EMLTree.size (EMLTree.eml (unfold sqProg f k) (unfold sqProg f k)) + 1
              = 2 ^ (k + 1 + 1)
        show 1 + (unfold sqProg f k).size + (unfold sqProg f k).size + 1 = 2 ^ (k + 1 + 1)
        have := hk.2
        omega

/-- **Depth `n` from `n+1` instructions.** -/
theorem sqProg_depth (n : Nat) : (unfoldAt sqProg n).depth = n :=
  (sqProg_unfold (n + 1) n (Nat.lt_succ_self n)).1

/-- **…and `2^(n+1) − 1` nodes once unfolded.** So a lower bound of `k` on tree *nodes* forces only
about `log₂ k` instructions, which is why `s(1/x) ≥ 9` says nothing about a datapath while
`d(1/x) = 4` says everything it can. -/
theorem sqProg_size (n : Nat) : (unfoldAt sqProg n).size + 1 = 2 ^ (n + 1) :=
  (sqProg_unfold (n + 1) n (Nat.lt_succ_self n)).2

/-- The gap at a concrete point: **5 instructions, 31 nodes.** -/
theorem sqProg_gap_at_four : (unfoldAt sqProg 4).depth = 4 ∧ (unfoldAt sqProg 4).size = 31 := by
  refine ⟨sqProg_depth 4, ?_⟩
  have h := sqProg_size 4
  omega

-- ▸ The next arrow: DAG → SCHEDULED datapath.

/-- A schedule records when each instruction's result is available. -/
def SchedValid (p : Nat → EMLInstr) (L : Nat) (s : Nat → Nat) : Prop :=
  ∀ i a b : Nat, p i = EMLInstr.eml a b → s a + L ≤ s i ∧ s b + L ≤ s i

/-- `wdepth 0 0 L` is just `L ·  depth`. -/
theorem wdepth_scaled (L : Nat) : ∀ t : EMLTree, t.wdepth 0 0 L = L * t.depth := by
  intro t
  induction t with
  | const c => show (0 : Nat) = L * 0; omega
  | var => show (0 : Nat) = L * 0; omega
  | eml a b iha ihb =>
    show L + max (a.wdepth 0 0 L) (b.wdepth 0 0 L) = L * (1 + max a.depth b.depth)
    rw [iha, ihb]
    rcases Nat.le_total a.depth b.depth with hle | hle
    · rw [Nat.max_eq_right hle, Nat.max_eq_right (Nat.mul_le_mul_left L hle)]
      have hdist : L * (1 + b.depth) = L + L * b.depth := by rw [Nat.mul_add, Nat.mul_one]
      omega
    · rw [Nat.max_eq_left hle, Nat.max_eq_left (Nat.mul_le_mul_left L hle)]
      have hdist : L * (1 + a.depth) = L + L * a.depth := by rw [Nat.mul_add, Nat.mul_one]
      omega

/-- **Depth is a latency floor no schedule can beat.** Whatever a scheduler does — however many
blocks it allocates, in whatever order — an instruction's result cannot be available before
`L ·  (its depth)`. This is the arrow `DAG → scheduled datapath`, and it is the arrow on which the
*area* multiplier dies: one time-multiplexed block can serve every node, so area becomes `O(1)` in
depth. Latency survives; area does not. -/
theorem schedule_ge_wdepth (p : Nat → EMLInstr) (hwf : ProgWf p) (L : Nat) (s : Nat → Nat)
    (hs : SchedValid p L s) :
    ∀ f i : Nat, i < f → (unfold p f i).wdepth 0 0 L ≤ s i := by
  intro f
  induction f with
  | zero => intro i h; exact absurd h (Nat.not_lt_zero i)
  | succ f ih =>
    intro i hi
    show EMLTree.wdepth 0 0 L (match p i with
          | EMLInstr.const c => EMLTree.const c
          | EMLInstr.var => EMLTree.var
          | EMLInstr.eml a b => EMLTree.eml (unfold p f a) (unfold p f b)) ≤ s i
    cases hp : p i with
    | const c => exact Nat.zero_le (s i)
    | var => exact Nat.zero_le (s i)
    | eml a b =>
      have hab := hwf i a b hp
      have haf : a < f := Nat.lt_of_lt_of_le hab.1 (Nat.le_of_lt_succ hi)
      have hbf : b < f := Nat.lt_of_lt_of_le hab.2 (Nat.le_of_lt_succ hi)
      have hsa := (hs i a b hp).1
      have hsb := (hs i a b hp).2
      have ha := ih a haf
      have hb := ih b hbf
      have hm : max ((unfold p f a).wdepth 0 0 L) ((unfold p f b).wdepth 0 0 L) + L ≤ s i := by
        rcases Nat.le_total ((unfold p f a).wdepth 0 0 L) ((unfold p f b).wdepth 0 0 L) with h1 | h1
        · rw [Nat.max_eq_right h1]; omega
        · rw [Nat.max_eq_left h1]; omega
      show L + max ((unfold p f a).wdepth 0 0 L) ((unfold p f b).wdepth 0 0 L) ≤ s i
      omega

/-- **No schedule computes `1/x` in fewer than `4·L`.** At the measured `L = 5` cycles per block
(`forge/reports/eml_block_cost_2026_08_11.md`) that is **20 cycles**, and it holds however many
blocks the scheduler allocates — including one. -/
theorem inv_x_schedule_ge_four_L (p : Nat → EMLInstr) (hwf : ProgWf p) (L : Nat) (s : Nat → Nat)
    (hs : SchedValid p L s) (i : Nat)
    (hp : ∀ x : Real, 0 < x → progEvalAt p i x = 1 / x) :
    4 * L ≤ s i := by
  have hw := schedule_ge_wdepth p hwf L s hs (i + 1) i (Nat.lt_succ_self i)
  rw [wdepth_scaled] at hw
  -- `unfoldAt p i` is by definition `unfold p (i+1) i`, but omega keys on syntax, so the two
  -- forms become distinct atoms unless they are bridged here.
  have hw2 : L * (unfoldAt p i).depth ≤ s i := hw
  have hd : 4 ≤ (unfoldAt p i).depth := by
    have h : ∀ x : Real, 0 < x → (unfoldAt p i).eval x = 1 / x := by
      intro x hx; rw [← progEvalAt_eq_unfoldAt_eval]; exact hp x hx
    have hno : ¬ ((unfoldAt p i).depth ≤ 3) :=
      fun h3 => inv_x_not_in_eml_depth_le_3 (unfoldAt p i) h3 h
    omega
  have hmul : L * 4 ≤ L * (unfoldAt p i).depth := Nat.mul_le_mul_left L hd
  have hcomm : L * 4 = 4 * L := Nat.mul_comm L 4
  omega

end MachLib
