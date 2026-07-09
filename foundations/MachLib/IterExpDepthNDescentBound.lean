import MachLib.IterExpDepthNBudgetGen

/-!
# Chain-N explicit bound — the recursive descent-length bound `descentBound` (corrected inner rank)

The step-5 obstruction (§4″): a FLAT rank over `chainNMeasureEI` cannot bound the number of reduces at a
fixed `degreeY_top` level, because although `chainNMeasureEI` *descends* in `nestedOrder` under the reduce,
that lex-descent's LOWER digits can still grow (`(3,0) > (2,100) > (2,50)` grows the low digit) — bounded
only by the `+1`/reduce degree growth. A uniform-`B` flat rank needs all digits `≤ B`, which the growth
breaks; making `B` grow re-triggers the monotone-in-`B` conflict.

The fix is a **recursive** count: `descentBound n B` bounds the length of a `nestedOrder`-descending
sequence of `NestedNat n` whose lower digits grow `≤ 1` per step, via a level-indexed budget with ONE level
per digit — the inner cap at each digit being the budget over the digits below it (`descentBound (n−1)`).
This mirrors `chainNMeasureEI`'s own depth recursion, and it threads because each digit is a level-index
(non-increasing on its own descent) rather than a bounded high digit. Pure `Nat`; this file is the cap +
its monotonicity. The `descentBound`-drops-under-a-reduce lemma (connecting to `chainNReduce_descends`) is
the next brick.
-/

namespace MachLib.IterExpDepthN

/-- One digit's level-indexed contribution: `d` values of this digit, each contributing `inner B`
descent-steps of the digits below, with the degree bound growing by `inner B + 1` per value (the lower
digits' reset headroom on a drop of this digit). -/
def dLevel (inner : Nat → Nat) : Nat → Nat → Nat
  | 0,     B => inner B
  | d + 1, B => inner B + dLevel inner d (B + inner B + 1)

/-- **The recursive lex-descent-length bound** for a `NestedNat n` (digits `≤ B`, lower digits grow
`≤ 1`/step): a nested level-indexed budget, one level per digit. The corrected (non-flat) inner rank. -/
def descentBound : (n : Nat) → Nat → Nat
  | 0     => fun B => B + 1
  | n + 1 => fun B => dLevel (descentBound n) B B

/-- `dLevel` is monotone in the degree bound `B`, given `inner` monotone. -/
theorem dLevel_mono_B (inner : Nat → Nat) (hinner : ∀ {B B' : Nat}, B ≤ B' → inner B ≤ inner B') :
    ∀ (d : Nat) {B B' : Nat}, B ≤ B' → dLevel inner d B ≤ dLevel inner d B'
  | 0, _, _, h => hinner h
  | d + 1, B, B', h => by
      have hi := hinner h
      show inner B + dLevel inner d (B + inner B + 1) ≤ inner B' + dLevel inner d (B' + inner B' + 1)
      have hrec := dLevel_mono_B inner hinner d
        (show B + inner B + 1 ≤ B' + inner B' + 1 from by omega)
      omega

/-- One extra value of the digit only adds count. -/
theorem dLevel_le_succ (inner : Nat → Nat) (hinner : ∀ {B B' : Nat}, B ≤ B' → inner B ≤ inner B')
    (d B : Nat) : dLevel inner d B ≤ dLevel inner (d + 1) B := by
  show dLevel inner d B ≤ inner B + dLevel inner d (B + inner B + 1)
  calc dLevel inner d B
        ≤ dLevel inner d (B + inner B + 1) := dLevel_mono_B inner hinner d (by omega)
    _ ≤ inner B + dLevel inner d (B + inner B + 1) := Nat.le_add_left _ _

/-- `dLevel` is monotone in the number of digit-values `d`. -/
theorem dLevel_mono_d (inner : Nat → Nat) (hinner : ∀ {B B' : Nat}, B ≤ B' → inner B ≤ inner B')
    (B : Nat) {d d' : Nat} (h : d ≤ d') : dLevel inner d B ≤ dLevel inner d' B := by
  induction h with
  | refl => exact Nat.le_refl _
  | step _ ih => exact Nat.le_trans ih (dLevel_le_succ inner hinner _ B)

/-- **`descentBound n` is monotone in `B`** — the property the recursion relies on (larger degree bound ⇒
larger count), proved by induction on the depth `n`. -/
theorem descentBound_mono : ∀ (n : Nat) {B B' : Nat}, B ≤ B' → descentBound n B ≤ descentBound n B'
  | 0, _, _, h => by show _ + 1 ≤ _ + 1; omega
  | n + 1, B, B', h => by
      show dLevel (descentBound n) B B ≤ dLevel (descentBound n) B' B'
      exact Nat.le_trans
        (dLevel_mono_d (descentBound n) (fun hbb => descentBound_mono n hbb) B h)
        (dLevel_mono_B (descentBound n) (fun hbb => descentBound_mono n hbb) B' h)

end MachLib.IterExpDepthN
