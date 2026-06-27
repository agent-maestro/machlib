/-!
# Leg B seed — a Mathlib-free ripple-carry adder, proved correct

The forward-error work (Leg A + the algebra) bounds the *real-valued* error of a
fixed-point datapath. **Leg B** is the orthogonal, bit-exact half: prove the
*gates* Forge emits compute the integer function they denote. This is the seed —
a bit-vector adder built on Lean-core `Nat`/`Bool`/`List` (no Mathlib), with the
foundational correctness theorem everything else (multiply, the Q-format
datapath) will build on.

Representation: a bit-vector is a little-endian `List Bool` (head = LSB).
`toNat` is its value; `rca` is the ripple-carry adder (a chain of full-adders);
`rca_correct` proves it computes addition *exactly*, carrying the overflow in the
final carry-out (no modular arithmetic):

    toNat (rca cin a b).1 + bitVal (rca cin a b).2 · 2^|a|
      = toNat a + toNat b + bitVal cin

`sorryAx`-free, Lean-core only.
-/

namespace MachLib.RTL

/-- Value of a single bit. -/
def bitVal (b : Bool) : Nat := if b then 1 else 0

/-- Little-endian bit-vector value (head = least significant bit). -/
def toNat : List Bool → Nat
  | []      => 0
  | b :: bs => bitVal b + 2 * toNat bs

/-- One full adder: `(sum, carry-out)` from two bits and a carry-in. -/
def fa (a b cin : Bool) : Bool × Bool :=
  (xor (xor a b) cin, (a && b) || (cin && xor a b))

/-- Full-adder correctness — the local invariant, true by exhaustion of the 8
Boolean cases. -/
theorem fa_correct (a b cin : Bool) :
    bitVal (fa a b cin).1 + 2 * bitVal (fa a b cin).2
      = bitVal a + bitVal b + bitVal cin := by
  cases a <;> cases b <;> cases cin <;> rfl

/-- Ripple-carry adder over equal-length bit-vectors: `(sum bits, carry-out)`. -/
def rca : Bool → List Bool → List Bool → (List Bool × Bool)
  | cin, [],      _       => ([], cin)
  | cin, _ :: _,  []      => ([], cin)
  | cin, a :: as, b :: bs =>
      ((fa a b cin).1 :: (rca (fa a b cin).2 as bs).1, (rca (fa a b cin).2 as bs).2)

/-- **Ripple-carry adder is exactly addition.** The sum bits plus the carry-out
(weighted by `2^width`) equal the integer sum of the inputs and the carry-in.
The seed theorem of Leg B: the gates compute the function. -/
theorem rca_correct : ∀ (a b : List Bool) (cin : Bool), a.length = b.length →
    toNat (rca cin a b).1 + bitVal (rca cin a b).2 * 2 ^ a.length
      = toNat a + toNat b + bitVal cin := by
  intro a
  induction a with
  | nil =>
      intro b cin hlen
      cases b with
      | nil => simp [rca, toNat]
      | cons b bs => simp at hlen
  | cons a as ih =>
      intro b cin hlen
      cases b with
      | nil => simp at hlen
      | cons b bs =>
        have hlen' : as.length = bs.length := by simpa using hlen
        have ihab := ih bs (fa a b cin).2 hlen'
        have hfa := fa_correct a b cin
        -- expose the recursive structure; weight 2^(n+1) = 2^n * 2; reassociate so
        -- the one nonlinear product matches ihab's, then abstract it to an atom.
        simp only [rca, toNat, List.length_cons]
        rw [Nat.pow_succ,
            ← Nat.mul_assoc (bitVal (rca (fa a b cin).2 as bs).2) (2 ^ as.length) 2]
        generalize bitVal (rca (fa a b cin).2 as bs).2 * 2 ^ as.length = M at ihab ⊢
        -- now linear: ihab : toNat(rca..).1 + M = toNat as + toNat bs + bitVal(fa..).2
        --             hfa  : bitVal(fa..).1 + 2·bitVal(fa..).2 = bitVal a+bitVal b+bitVal cin
        omega
