/-
MachLib.Basic — axiomatic real numbers, zero Mathlib dependency.

The type `Real` is opaque, equipped with the standard arithmetic
operations, an order relation, and the analytic axioms exp / log /
trig will need (Archimedean, supremum on bounded predicates).

Construction from rationals via Cauchy sequences is omitted by
design: it adds ~3,000 lines for no MachLib benefit. Every axiom
below is consistent with classical ZFC.
-/

namespace MachLib

axiom Real : Type

namespace Real

/-! ### Underlying values + typeclass instances -/

axiom addR : Real → Real → Real
axiom subR : Real → Real → Real
axiom mulR : Real → Real → Real
axiom divR : Real → Real → Real
axiom negR : Real → Real
axiom oneR : Real
axiom zeroR : Real
axiom ltR : Real → Real → Prop
axiom leR : Real → Real → Prop

@[instance] noncomputable def instAdd  : Add Real := ⟨addR⟩
@[instance] noncomputable def instSub  : Sub Real := ⟨subR⟩
@[instance] noncomputable def instMul  : Mul Real := ⟨mulR⟩
@[instance] noncomputable def instDiv  : Div Real := ⟨divR⟩
@[instance] noncomputable def instNeg  : Neg Real := ⟨negR⟩
@[instance] noncomputable def instLT   : LT Real := ⟨ltR⟩
@[instance] noncomputable def instLE   : LE Real := ⟨leR⟩
@[instance] noncomputable def instOfNatZero : OfNat Real (nat_lit 0) := ⟨zeroR⟩
@[instance] noncomputable def instOfNatOne  : OfNat Real (nat_lit 1) := ⟨oneR⟩
@[instance] noncomputable def instInhabited : Inhabited Real := ⟨zeroR⟩

/-! ### Decimal literals

`realOfScientific`, the function a decimal literal elaborates to, is DEFINED at the end of this file -- after
`natCast` and the field operations it is defined from. Until 2026-10-04 it was an opaque function and seven
axioms said what it returns (`_pos`, `_one/_two/_three_dot_zero`, `_le_of_nat`, `_lt_of_nat` here, `_clears` in
`Decimal.lean`); all seven are theorems now. -/

/--
Real-to-real power. Forge kernels emit `(base ^ exp)` for
non-integer exponents (e.g. `(1 + (alpha * psi) ^ n_shape)` in
the van Genuchten retention curve). Lean's default `^` resolves
to integer powers via `Monoid.npow`; for `Real ^ Real` we must
provide an explicit `HPow` instance.

We do NOT axiomatise the analytic identity `realPow x y = exp(y * log x)`
here — that's a CHOICE the downstream theorem can pin down with
its own axioms when needed. The carrier is opaque so MachLib
stays agnostic about whether the kernel target is real-analytic
or a piecewise extension.
-/
axiom realPow : Real → Real → Real

@[instance] noncomputable def instHPow : HPow Real Real Real :=
  ⟨realPow⟩

axiom realPow_zero (x : Real) : realPow x 0 = 1
axiom realPow_one  (x : Real) : realPow x 1 = x
axiom realPow_pos  {x y : Real} : 0 < x → 0 < realPow x y
-- Elementary, disclosed: a nonneg base raised to any real exponent is
-- nonneg (realPow 0 y = 0 for y≠0, = 1 for y=0; positive base via realPow_pos).
-- `realPow` is opaque here, so this is axiomatized like its siblings above.
axiom realPow_nonneg {x : Real} (hx : 0 ≤ x) (y : Real) : 0 ≤ x ^ y
-- Lean div-by-zero convention (matches Mathlib's `div_zero`); sound for the
-- opaque `divR`. Lets `div_nonneg` (proved in Forge.lean) cover nonneg denominators.
axiom div_zero (a : Real) : a / 0 = 0

@[instance] noncomputable def instDecLT (a b : Real) : Decidable (a < b) :=
  Classical.propDecidable _
@[instance] noncomputable def instDecLE (a b : Real) : Decidable (a ≤ b) :=
  Classical.propDecidable _
/-- Decidable EQUALITY, by the same classical mechanism as the two above.

Missing until 2026-09-08, and its absence was invisible because nothing exercised it: an EML
kernel writing `if x == 0.0` lowers to `ite (x = 0) ..`, Lean asks for `Decidable (x = 0)`, and
`instDecLT`/`instDecLE` do not supply it. So `if a < b` compiled and `if a == b` did not, and
the failure surfaced only when Forge began emitting BODIES for kernels it had previously
axiomatised — an axiom has no `ite` in it to fail on. The gap was in this file the whole time. -/
@[instance] noncomputable def instDecEq (a b : Real) : Decidable (a = b) :=
  Classical.propDecidable _

/-! ### Field axioms -/

axiom add_comm    (a b   : Real) : a + b = b + a
axiom add_assoc   (a b c : Real) : (a + b) + c = a + (b + c)

/-! ### AC typeclass instances (used by `ac_rfl`)

`ac_rfl` is Lean 4's AC-aware reflexivity tactic; it closes any
goal of the form `e₁ = e₂` where `e₁` and `e₂` are equal up to
associativity and commutativity of a binary operator. The tactic
hunts for `Std.Commutative` and `Std.Associative` instances on
the operator in the goal, so we register them directly on
`(· + ·)` and `(· * ·)` over `Real` here. Costs ~10 lines and
trivially closes the AC residue that blocks `mach_ring` v1.5 on
cross-product / SDF-translation goals. -/

instance instAddComm  : Std.Commutative (α := Real) (· + ·) := ⟨add_comm⟩
instance instAddAssoc : Std.Associative (α := Real) (· + ·) := ⟨add_assoc⟩
axiom add_zero    (a     : Real) : a + 0 = a
axiom add_neg     (a     : Real) : a + (-a) = 0
axiom sub_def     (a b   : Real) : a - b = a + (-b)

axiom mul_comm    (a b   : Real) : a * b = b * a
axiom mul_assoc   (a b c : Real) : (a * b) * c = a * (b * c)

instance instMulComm  : Std.Commutative (α := Real) (· * ·) := ⟨mul_comm⟩
instance instMulAssoc : Std.Associative (α := Real) (· * ·) := ⟨mul_assoc⟩
axiom mul_one_ax  (a     : Real) : a * 1 = a
axiom mul_distrib (a b c : Real) : a * (b + c) = a * b + a * c

/-- `0 ≠ 1` is a FIELD axiom, and it stays one. It IS derivable -- from the ORDER axioms `zero_lt_one_ax` and
`lt_irrefl_ax` (`AxiomMinimality.zero_ne_one_derivable`) -- but not from the field axioms: the zero ring satisfies
every other one. MachLib's algebra spine is field-only by design (`AxiomLedger`'s `algebraFootprint`, 326 theorems
held to it), and proving this from the order put `ltR`, `lt_irrefl_ax` and `zero_lt_one_ax` into 33 of them --
measured 2026-10-04, the muses' E round, when "provable means proved" first converted it. Provable means proved
WITHIN THE SUB-THEORY AN AXIOM SERVES; this one is primitive for the field. -/
axiom zero_ne_one_ax : (0 : Real) ≠ 1
axiom div_def        (a b : Real) : b ≠ 0 → a / b = a * (1 / b)
axiom mul_inv        (a   : Real) : a ≠ 0 → a * (1 / a) = 1

/-! ### Order axioms -/

axiom lt_irrefl_ax (a   : Real) : ¬ a < a
axiom lt_trans_ax  {a b c : Real} : a < b → b < c → a < c
axiom lt_total     (a b : Real) : a < b ∨ a = b ∨ b < a
axiom le_iff_lt_or_eq (a b : Real) : a ≤ b ↔ a < b ∨ a = b

axiom add_lt_add_left  {a b : Real} (h : a < b) (c : Real) : c + a < c + b
axiom mul_pos          {a b : Real} : 0 < a → 0 < b → 0 < a * b
axiom zero_lt_one_ax   : (0 : Real) < 1

/-! ### Archimedean + completeness -/

/-- `n` as a real: `0`, and `+ 1` per step. A DEFINITION since 2026-10-04 -- three axioms (the function and its
two equations) said exactly what this recursion says. IRREDUCIBLE: a definitional-equality check must never
unfold `natCast 1000000` into a million additions; the equations below are the interface. -/
noncomputable def natCast : Nat → Real
  | 0 => 0
  | n + 1 => natCast n + 1

theorem natCast_zero : natCast 0 = 0 := rfl
theorem natCast_succ (n : Nat) : natCast (n + 1) = natCast n + 1 := rfl

-- Irreducible only AFTER its equations exist: Lean derives an equation lemma by unfolding, and cannot for a
-- definition already irreducible.
attribute [irreducible] natCast

def BoundedAbove (p : Real → Prop) : Prop :=
  ∃ M : Real, ∀ x : Real, p x → x ≤ M

axiom sup_exists
    (p : Real → Prop) (h_nonempty : ∃ x, p x) (h_bound : BoundedAbove p) :
    ∃ s : Real,
      (∀ x, p x → x ≤ s) ∧
      (∀ s', (∀ x, p x → x ≤ s') → s ≤ s')

private theorem le_of_not_lt_b {a b : Real} (h : ¬ a < b) : b ≤ a := by
  rcases lt_total a b with hlt | heq | hgt
  · exact absurd hlt h
  · exact (le_iff_lt_or_eq b a).mpr (Or.inr heq.symm)
  · exact (le_iff_lt_or_eq b a).mpr (Or.inl hgt)

private theorem sub_one_lt_b (s : Real) : s - 1 < s := by
  have h := add_lt_add_left zero_lt_one_ax (s - 1)
  rw [add_zero] at h
  have hid : s - 1 + 1 = s := by
    rw [sub_def, add_assoc, add_comm (-(1 : Real)) 1, add_neg, add_zero]
  rwa [hid] at h

private theorem lt_of_le_of_lt_b {a b c : Real} (hab : a ≤ b) (hbc : b < c) : a < c := by
  rcases (le_iff_lt_or_eq a b).mp hab with h | h
  · exact lt_trans_ax h hbc
  · rw [h]; exact hbc

private theorem add_le_add_right_b {a b : Real} (h : a ≤ b) (c : Real) : a + c ≤ b + c := by
  rcases (le_iff_lt_or_eq a b).mp h with hlt | heq
  · refine (le_iff_lt_or_eq (a + c) (b + c)).mpr (Or.inl ?_)
    rw [add_comm a c, add_comm b c]
    exact add_lt_add_left hlt c
  · rw [heq]; exact (le_iff_lt_or_eq (b + c) (b + c)).mpr (Or.inr rfl)

private theorem le_sub_one_of_succ_le_b {a s : Real} (h : a + 1 ≤ s) : a ≤ s - 1 := by
  have h2 := add_le_add_right_b h (-(1 : Real))
  have hid : a + 1 + -(1 : Real) = a := by
    rw [add_assoc, add_neg, add_zero]
  rwa [hid, ← sub_def] at h2

/-- **Archimedean**: a Dedekind-complete ordered field is Archimedean. A theorem since 2026-10-04 (its
derivation from `sup_exists`, `AxiomMinimality.archimedean_derivable`, had been gated for months). The proof
shows `s - 1` IS an upper bound of the casts -- `natCast (n+1) ≤ s` gives `natCast n ≤ s - 1` -- against
leastness, so it needs no case analysis beyond excluded middle on the conclusion. -/
theorem archimedean (x : Real) : ∃ n : Nat, x < natCast n := by
  rcases Classical.em (∃ n : Nat, x < natCast n) with hcon | hcon
  · exact hcon
  · exfalso
    have hall : ∀ n : Nat, natCast n ≤ x := fun n => le_of_not_lt_b (fun hlt => hcon ⟨n, hlt⟩)
    have hbound : BoundedAbove (fun y => ∃ n : Nat, y = natCast n) := by
      refine ⟨x, ?_⟩
      rintro y ⟨n, rfl⟩
      exact hall n
    obtain ⟨s, hub, hleast⟩ :=
      sup_exists (fun y => ∃ n : Nat, y = natCast n) ⟨natCast 0, ⟨0, rfl⟩⟩ hbound
    have hub' : ∀ y, (∃ n : Nat, y = natCast n) → y ≤ s - 1 := by
      rintro y ⟨n, rfl⟩
      have hsucc : natCast (n + 1) ≤ s := hub (natCast (n + 1)) ⟨n + 1, rfl⟩
      rw [natCast_succ] at hsucc
      exact le_sub_one_of_succ_le_b hsucc
    exact lt_irrefl_ax s (lt_of_le_of_lt_b (hleast (s - 1) hub') (sub_one_lt_b s))

/-! ## Derived definitions -/

noncomputable def abs (x : Real) : Real := if 0 ≤ x then x else -x
noncomputable def min (a b : Real) : Real := if a ≤ b then a else b
noncomputable def max (a b : Real) : Real := if a ≤ b then b else a

/-- Two-argument Heaviside step. `step a b = 1` when `a ≥ b`,
otherwise `0`. The 2-arg form matches the `step(sample, threshold)`
convention Forge kernels emit (e.g. shadow PCF, neural threshold
activations) and avoids carrying around a separate
`heaviside`/`step1` distinction. -/
noncomputable def step (a b : Real) : Real := if b ≤ a then 1 else 0

/-! ## Basic derived lemmas -/

theorem zero_add (a : Real) : 0 + a = a := by
  rw [add_comm]; exact add_zero a

theorem neg_add_self (a : Real) : -a + a = 0 := by
  rw [add_comm]; exact add_neg a

theorem one_mul_thm (a : Real) : 1 * a = a := by
  rw [mul_comm]; exact mul_one_ax a

theorem mul_zero (a : Real) : a * 0 = 0 := by
  have h : a * 0 = a * 0 + a * 0 := by
    have step : a * (0 + 0) = a * 0 + a * 0 := mul_distrib a 0 0
    rw [add_zero] at step
    exact step
  have h2 : a * 0 + (-(a * 0)) = (a * 0 + a * 0) + (-(a * 0)) := by
    rw [← h]
  rw [add_neg, add_assoc, add_neg, add_zero] at h2
  exact h2.symm

theorem zero_mul (a : Real) : 0 * a = 0 := by
  rw [mul_comm]; exact mul_zero a

theorem ne_of_lt {a b : Real} (h : a < b) : a ≠ b := by
  intro heq; rw [heq] at h; exact lt_irrefl_ax b h

theorem ne_of_gt {a b : Real} (h : b < a) : a ≠ b := by
  intro heq; rw [heq] at h; exact lt_irrefl_ax b h

theorem one_pos : (0 : Real) < 1 := zero_lt_one_ax

theorem one_ne_zero : (1 : Real) ≠ 0 := fun h => zero_ne_one_ax h.symm

theorem abs_zero : abs (0 : Real) = 0 := by
  unfold abs
  have h : (0 : Real) ≤ 0 := (le_iff_lt_or_eq 0 0).mpr (Or.inr rfl)
  simp [h]

theorem abs_one : abs (1 : Real) = 1 := by
  unfold abs
  have h : (0 : Real) ≤ 1 := (le_iff_lt_or_eq 0 1).mpr (Or.inl zero_lt_one_ax)
  simp [h]

theorem min_self (a : Real) : min a a = a := by
  unfold min
  have h : a ≤ a := (le_iff_lt_or_eq a a).mpr (Or.inr rfl)
  simp [h]

theorem max_self (a : Real) : max a a = a := by
  unfold max
  have h : a ≤ a := (le_iff_lt_or_eq a a).mpr (Or.inr rfl)
  simp [h]

/-! ## Ordered-field facts the axioms imply, and what a decimal literal means

Theorems since 2026-10-04 (the muses' E round: "no axiom that could instead be a theorem under the intended
foundation"). Each was an axiom somewhere downstream -- `one_div_pos_of_pos` in `Linarith.lean`,
`mul_lt_mul_of_pos_right`, `div_lt_one_of_pos_lt` and `lit_zero_eq` in `Forge.lean`, `realOfScientific_clears`
in `Decimal.lean` -- whose own docstring said it was derivable "once the helpers are in `MachLib.Basic`".
They are here, where every file can reach them. -/

private theorem le_rfl_b (a : Real) : a ≤ a := (le_iff_lt_or_eq a a).mpr (Or.inr rfl)

private theorem le_of_lt_b {a b : Real} (h : a < b) : a ≤ b := (le_iff_lt_or_eq a b).mpr (Or.inl h)

private theorem add_le_add_left_b {a b : Real} (h : a ≤ b) (c : Real) : c + a ≤ c + b := by
  rcases (le_iff_lt_or_eq a b).mp h with hlt | heq
  · exact (le_iff_lt_or_eq (c + a) (c + b)).mpr (Or.inl (add_lt_add_left hlt c))
  · rw [heq]; exact le_rfl_b _

/-- `a * -b = -(a * b)`, from distributivity and cancellation. -/
private theorem mul_neg_b (a b : Real) : a * -b = -(a * b) := by
  have h : a * b + a * -b = 0 := by rw [← mul_distrib, add_neg, mul_zero]
  have hc : -(a * b) + (a * b + a * -b) = -(a * b) + 0 := by rw [h]
  rw [← add_assoc, neg_add_self, zero_add, add_zero] at hc
  exact hc

/-- `0 < b → 0 < 1 / b`: `1/b = 0` makes `b · (1/b) = 0`, but `mul_inv` says `1`; `1/b < 0` makes it
negative, but it is `1`. Trichotomy is a disjunction here, so the case split is constructive. -/
theorem one_div_pos_of_pos {b : Real} (hb : 0 < b) : 0 < 1 / b := by
  have hinv : b * (1 / b) = 1 := mul_inv b (ne_of_gt hb)
  rcases lt_total 0 (1 / b) with hpos | hzero | hneg
  · exact hpos
  · exfalso
    rw [← hzero, mul_zero] at hinv
    exact zero_ne_one_ax hinv
  · exfalso
    have hnegpos : 0 < -(1 / b) := by
      have h := add_lt_add_left hneg (-(1 / b))
      rwa [neg_add_self, add_zero] at h
    have hprod : 0 < b * -(1 / b) := mul_pos hb hnegpos
    rw [mul_neg_b, hinv] at hprod
    have h1 := add_lt_add_left hprod 1
    rw [add_zero, add_neg] at h1
    exact lt_irrefl_ax 0 (lt_trans_ax zero_lt_one_ax h1)

/-- `a < b → 0 < c → a * c < b * c`: `(b - a) · c > 0` by `mul_pos`, and distributivity. -/
theorem mul_lt_mul_of_pos_right {a b c : Real} (h : a < b) (hc : 0 < c) : a * c < b * c := by
  have hba : 0 < b + -a := by
    have h2 := add_lt_add_left h (-a)
    rwa [neg_add_self, add_comm (-a) b] at h2
  have hp : 0 < (b + -a) * c := mul_pos hba hc
  have hexp : (b + -a) * c = b * c + -(a * c) := by
    rw [mul_comm, mul_distrib, mul_neg_b, mul_comm c b, mul_comm c a]
  rw [hexp] at hp
  have h3 := add_lt_add_left hp (a * c)
  rw [add_zero] at h3
  have hid : a * c + (b * c + -(a * c)) = b * c := by
    rw [add_comm (b * c) (-(a * c)), ← add_assoc, add_neg, zero_add]
  rwa [hid] at h3

private theorem mul_le_mul_of_pos_right_b {a b c : Real} (h : a ≤ b) (hc : 0 < c) : a * c ≤ b * c := by
  rcases (le_iff_lt_or_eq a b).mp h with hlt | heq
  · exact le_of_lt_b (mul_lt_mul_of_pos_right hlt hc)
  · rw [heq]; exact le_rfl_b _

/-- `0 < b → a < b → a / b < 1`. -/
theorem div_lt_one_of_pos_lt {a b : Real} (hb : 0 < b) (hab : a < b) : a / b < 1 := by
  rw [div_def a b (ne_of_gt hb)]
  have h := mul_lt_mul_of_pos_right hab (one_div_pos_of_pos hb)
  rwa [mul_inv b (ne_of_gt hb)] at h

/-! ### `natCast` arithmetic (moved here from `Decimal.lean`, which only some files import) -/

/-- `natCast` is additive. -/
theorem natCast_add (a b : Nat) : natCast (a + b) = natCast a + natCast b := by
  induction b with
  | zero => rw [Nat.add_zero, natCast_zero, add_zero]
  | succ n ih => rw [Nat.add_succ, natCast_succ, natCast_succ, ih, add_assoc]

/-- `natCast` is multiplicative. -/
theorem natCast_mul (a b : Nat) : natCast (a * b) = natCast a * natCast b := by
  induction b with
  | zero => rw [Nat.mul_zero, natCast_zero, mul_zero]
  | succ k ih => rw [Nat.mul_succ, natCast_add, ih, natCast_succ, mul_distrib, mul_one_ax]

private theorem pos_of_nonneg_add_one_b {x : Real} (h : 0 ≤ x) : 0 < x + 1 := by
  have h1 := add_lt_add_left zero_lt_one_ax x
  rw [add_zero] at h1
  exact lt_of_le_of_lt_b h h1

/-- `0 ≤ natCast n`. -/
theorem natCast_nonneg (n : Nat) : 0 ≤ natCast n := by
  induction n with
  | zero => rw [natCast_zero]; exact le_rfl_b 0
  | succ k ih => rw [natCast_succ]; exact le_of_lt_b (pos_of_nonneg_add_one_b ih)

/-- `0 < natCast (n+1)`. -/
theorem natCast_succ_pos (n : Nat) : 0 < natCast (n + 1) := by
  rw [natCast_succ]; exact pos_of_nonneg_add_one_b (natCast_nonneg n)

/-- `0 < n → 0 < natCast n`. -/
theorem natCast_pos {n : Nat} (h : 0 < n) : 0 < natCast n := by
  cases n with
  | zero => exact absurd h (Nat.lt_irrefl 0)
  | succ k => exact natCast_succ_pos k

/-- `a ≤ b → natCast a ≤ natCast b`. -/
theorem natCast_le_natCast {a b : Nat} (h : a ≤ b) : natCast a ≤ natCast b := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [natCast_add]
  have h2 := add_le_add_left_b (natCast_nonneg d) (natCast a)
  rwa [add_zero] at h2

/-- `a < b → natCast a < natCast b`. -/
theorem natCast_lt_natCast {a b : Nat} (h : a < b) : natCast a < natCast b := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt h
  rw [natCast_succ, natCast_add]
  have h2 := add_lt_add_left (pos_of_nonneg_add_one_b (natCast_nonneg d)) (natCast a)
  rwa [add_zero, ← add_assoc] at h2

private theorem natCast_two_b : natCast 2 = 1 + 1 := by
  rw [show (2 : Nat) = 0 + 1 + 1 from rfl, natCast_succ, natCast_succ, natCast_zero, zero_add]

private theorem natCast_three_b : natCast 3 = 1 + 1 + 1 := by
  rw [show (3 : Nat) = 0 + 1 + 1 + 1 from rfl, natCast_succ, natCast_succ, natCast_succ, natCast_zero, zero_add]

private theorem pow10_pos_b (e : Nat) : 0 < natCast (10 ^ e) := natCast_pos (Nat.pow_pos (by decide))

/-! ### What a decimal literal means -/

/-- What a decimal literal DENOTES: `m · 10⁻ᵉ` when `exponentSign` (the form Lean's elaborator produces for a
`Real` literal with a decimal point -- `(0.5 : Real)` is `realOfScientific 5 true 1`), `m · 10ᵉ` otherwise:
`natCast` and the field operations, nothing else.

A DEFINITION since 2026-10-04 (the muses' E round: "an axiom asserting how a literal denotes is the
Lean-real-number form of the Float.ofScientific trap, and it is exactly where a wrong number hides by fiat").
It was an opaque function and seven axioms said what it returns; every one is a theorem below. IRREDUCIBLE,
as `natCast` is: a definitional check never unfolds a literal into cast arithmetic. -/
noncomputable def realOfScientific
    (mantissa : Nat) (exponentSign : Bool) (decimalExponent : Nat) : Real :=
  if exponentSign then natCast mantissa / natCast (10 ^ decimalExponent)
  else natCast mantissa * natCast (10 ^ decimalExponent)

@[instance] noncomputable def instOfScientific : OfScientific Real :=
  ⟨realOfScientific⟩

/-- A decimal literal with a decimal point is its mantissa over a power of ten. -/
theorem realOfScientific_true (m e : Nat) : realOfScientific m true e = natCast m / natCast (10 ^ e) := rfl

/-- The other form: the mantissa times a power of ten. -/
theorem realOfScientific_false (m e : Nat) : realOfScientific m false e = natCast m * natCast (10 ^ e) := rfl

attribute [irreducible] realOfScientific

/-- Mantissa-positive literals are positive (was an axiom, C-240). -/
theorem realOfScientific_pos (m : Nat) (s : Bool) (e : Nat) (hm : 0 < m) : 0 < realOfScientific m s e := by
  cases s with
  | true =>
    rw [realOfScientific_true, div_def _ _ (ne_of_gt (pow10_pos_b e))]
    exact mul_pos (natCast_pos hm) (one_div_pos_of_pos (pow10_pos_b e))
  | false =>
    rw [realOfScientific_false]
    exact mul_pos (natCast_pos hm) (pow10_pos_b e)

/-- `(m·10⁻ᵉ)·10ᵉ = m`: the defining property `Decimal.lean` used to assume. -/
theorem realOfScientific_clears (m e : Nat) : realOfScientific m true e * natCast (10 ^ e) = natCast m := by
  have hp : natCast (10 ^ e) ≠ 0 := ne_of_gt (pow10_pos_b e)
  rw [realOfScientific_true, div_def _ _ hp, mul_assoc, mul_comm (1 / natCast (10 ^ e)), mul_inv _ hp,
      mul_one_ax]

/-- `1.0 = 1` (was an axiom, C-243). -/
theorem realOfScientific_one_dot_zero : realOfScientific 10 true 1 = 1 := by
  have hp : natCast 10 ≠ 0 := ne_of_gt (natCast_pos (by decide))
  rw [realOfScientific_true, Nat.pow_one, div_def _ _ hp, mul_inv _ hp]

/-- `2.0 = 1 + 1` (was an axiom, C-243). -/
theorem realOfScientific_two_dot_zero : realOfScientific 20 true 1 = 1 + 1 := by
  have hp : natCast 10 ≠ 0 := ne_of_gt (natCast_pos (by decide))
  rw [realOfScientific_true, Nat.pow_one, div_def _ _ hp, show (20 : Nat) = 2 * 10 from rfl, natCast_mul,
      mul_assoc, mul_inv _ hp, mul_one_ax, natCast_two_b]

/-- `3.0 = 1 + 1 + 1` (was an axiom, C-243). -/
theorem realOfScientific_three_dot_zero : realOfScientific 30 true 1 = 1 + 1 + 1 := by
  have hp : natCast 10 ≠ 0 := ne_of_gt (natCast_pos (by decide))
  rw [realOfScientific_true, Nat.pow_one, div_def _ _ hp, show (30 : Nat) = 3 * 10 from rfl, natCast_mul,
      mul_assoc, mul_inv _ hp, mul_one_ax, natCast_three_b]

/-- Decimal-literal order by `Nat` cross-multiplication: `m₁/10^e₁ ≤ m₂/10^e₂ ⟸ m₁·10^e₂ ≤ m₂·10^e₁` (was an
axiom, C-247). Multiply the cast inequality by `(1/10^e₁)(1/10^e₂) > 0` and cancel. -/
theorem realOfScientific_le_of_nat {m₁ e₁ m₂ e₂ : Nat} (h : m₁ * 10 ^ e₂ ≤ m₂ * 10 ^ e₁) :
    realOfScientific m₁ true e₁ ≤ realOfScientific m₂ true e₂ := by
  have hP := pow10_pos_b e₁
  have hQ := pow10_pos_b e₂
  have h' := natCast_le_natCast h
  rw [natCast_mul, natCast_mul] at h'
  have hk : 0 < 1 / natCast (10 ^ e₁) * (1 / natCast (10 ^ e₂)) :=
    mul_pos (one_div_pos_of_pos hP) (one_div_pos_of_pos hQ)
  have h2 := mul_le_mul_of_pos_right_b h' hk
  have eL : natCast m₁ * natCast (10 ^ e₂) * (1 / natCast (10 ^ e₁) * (1 / natCast (10 ^ e₂)))
      = natCast m₁ * (1 / natCast (10 ^ e₁)) * (natCast (10 ^ e₂) * (1 / natCast (10 ^ e₂))) := by ac_rfl
  have eR : natCast m₂ * natCast (10 ^ e₁) * (1 / natCast (10 ^ e₁) * (1 / natCast (10 ^ e₂)))
      = natCast m₂ * (1 / natCast (10 ^ e₂)) * (natCast (10 ^ e₁) * (1 / natCast (10 ^ e₁))) := by ac_rfl
  rw [eL, eR, mul_inv _ (ne_of_gt hQ), mul_inv _ (ne_of_gt hP), mul_one_ax, mul_one_ax] at h2
  rw [realOfScientific_true, realOfScientific_true, div_def _ _ (ne_of_gt hP), div_def _ _ (ne_of_gt hQ)]
  exact h2

/-- The strict form (was an axiom, C-247). -/
theorem realOfScientific_lt_of_nat {m₁ e₁ m₂ e₂ : Nat} (h : m₁ * 10 ^ e₂ < m₂ * 10 ^ e₁) :
    realOfScientific m₁ true e₁ < realOfScientific m₂ true e₂ := by
  have hP := pow10_pos_b e₁
  have hQ := pow10_pos_b e₂
  have h' := natCast_lt_natCast h
  rw [natCast_mul, natCast_mul] at h'
  have hk : 0 < 1 / natCast (10 ^ e₁) * (1 / natCast (10 ^ e₂)) :=
    mul_pos (one_div_pos_of_pos hP) (one_div_pos_of_pos hQ)
  have h2 := mul_lt_mul_of_pos_right h' hk
  have eL : natCast m₁ * natCast (10 ^ e₂) * (1 / natCast (10 ^ e₁) * (1 / natCast (10 ^ e₂)))
      = natCast m₁ * (1 / natCast (10 ^ e₁)) * (natCast (10 ^ e₂) * (1 / natCast (10 ^ e₂))) := by ac_rfl
  have eR : natCast m₂ * natCast (10 ^ e₁) * (1 / natCast (10 ^ e₁) * (1 / natCast (10 ^ e₂)))
      = natCast m₂ * (1 / natCast (10 ^ e₂)) * (natCast (10 ^ e₁) * (1 / natCast (10 ^ e₁))) := by ac_rfl
  rw [eL, eR, mul_inv _ (ne_of_gt hQ), mul_inv _ (ne_of_gt hP), mul_one_ax, mul_one_ax] at h2
  rw [realOfScientific_true, realOfScientific_true, div_def _ _ (ne_of_gt hP), div_def _ _ (ne_of_gt hQ)]
  exact h2

/-- The decimal literal `0.0` and the `OfNat` literal `0` are the same `Real` (was an axiom in `Forge.lean`). -/
theorem lit_zero_eq : (0.0 : Real) = (0 : Real) := by
  show realOfScientific 0 true 1 = 0
  rw [realOfScientific_true, natCast_zero, div_def _ _ (ne_of_gt (pow10_pos_b 1)), zero_mul]

end Real

end MachLib
