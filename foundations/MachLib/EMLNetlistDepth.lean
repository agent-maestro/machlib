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

* **Size does not survive at all.** `sqProg` is `n+1` instructions whose unfolding has
  `2^(n+1) - 1` nodes (`sqProg_size`). A lower bound of `9` on tree nodes is consistent with a
  netlist of four blocks. Sharing is exactly the operation that makes node counts lie, and the
  reciprocal's *size* question — `s(1/x) ∈ {9,11}` — is therefore a statement about the tree
  encoding and **not** about any datapath.

That asymmetry is the point of this module. The depth arm, which cost far more effort, is the one
carrying hardware meaning; the size arm, which looks like the sharper number, carries none. Neither
was chosen for that reason, and it is worth recording that the useful one was not the one that
looked useful.

**Scope.** "Datapath" here means a straight-line program over the EML primitive
`(a, b) ↦ exp a − log b`, which is the block Forge's hardware lane emits. Nothing here bounds
gate-depth *inside* a block, and nothing here is a lower bound against arbitrary circuits — that
would be a circuit-complexity claim and this is not one. What is proved is that within the class of
EML-structured datapaths, tree depth is a faithful cost and tree size is not.
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

-- ▸ The transfer.

/-- **`1/x` needs combinational block-depth ≥ 4 in any straight-line EML datapath.**

`inv_x_not_in_eml_depth_le_3` is a statement about trees; `netDepth_eq_depth` is what makes it a
statement about hardware. Sharing cannot help, because sharing does not change depth. -/
theorem inv_x_netlist_depth_ge_four (p : Nat → EMLInstr) (hwf : ProgWf p) (i : Nat)
    (h : ∀ x : Real, 0 < x → (unfoldAt p i).eval x = 1 / x) :
    4 ≤ netDepthAt p i := by
  rw [netDepthAt_eq_depth]
  have hno : ¬ ((unfoldAt p i).depth ≤ 3) :=
    fun h3 => inv_x_not_in_eml_depth_le_3 (unfoldAt p i) h3 h
  omega

/-- **…hence its output cannot sit before index 4:** at least five instruction slots. A resource
statement about the program, obtained from a statement about trees. -/
theorem inv_x_netlist_index_ge_four (p : Nat → EMLInstr) (hwf : ProgWf p) (i : Nat)
    (h : ∀ x : Real, 0 < x → (unfoldAt p i).eval x = 1 / x) :
    4 ≤ i := by
  have hd := inv_x_netlist_depth_ge_four p hwf i h
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

end MachLib
