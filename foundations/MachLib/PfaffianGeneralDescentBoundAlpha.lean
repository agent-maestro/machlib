import MachLib.IterExpDepthNDescentBound

/-!
# α-generalized recursive descent-length cap (general Pfaffian explicit bound, step-4 cap)

`descentBound` (`IterExpDepthNDescentBound.lean`) bounds the length of a `nestedOrder`-descending
sequence of `NestedNat n` whose lower digits grow **`≤ 1`** per step — the iterated-exp *tower*'s
`+1`/reduce degree growth. A general coherent exp-chain grows its lower degrees by the format `α` per
reduce (`degreeX/degreeY_chainReduce_le_format`), so the descent cap must tolerate lower digits growing
**`≤ α`** per step. `descentBoundA α` is that generalization: the per-drop reset headroom in `dLevelA`
is `inner B + α` in place of `inner B + 1`. `descentBoundA 1 = descentBound`; the monotonicity the
`invPhiG` cap requires (`hcap`) is preserved. Pure `Nat`.
-/

namespace MachLib.IterExpDepthN

/-- α-generalized `dLevel`: each value of this digit contributes `inner B` inner steps, with the degree
bound growing by `inner B + α` per value (lower digits' reset headroom on a drop, for `≤ α` growth). -/
def dLevelA (inner : Nat → Nat) (α : Nat) : Nat → Nat → Nat
  | 0,     B => inner B
  | d + 1, B => inner B + dLevelA inner α d (B + inner B + α)

/-- `dLevelA` is monotone in the degree bound `B`, given `inner` monotone. -/
theorem dLevelA_mono_B (inner : Nat → Nat) (hinner : ∀ {B B' : Nat}, B ≤ B' → inner B ≤ inner B')
    (α : Nat) :
    ∀ (d : Nat) {B B' : Nat}, B ≤ B' → dLevelA inner α d B ≤ dLevelA inner α d B'
  | 0, _, _, h => hinner h
  | d + 1, B, B', h => by
      have hi := hinner h
      show inner B + dLevelA inner α d (B + inner B + α)
          ≤ inner B' + dLevelA inner α d (B' + inner B' + α)
      have hrec := dLevelA_mono_B inner hinner α d
        (show B + inner B + α ≤ B' + inner B' + α from by omega)
      omega

/-- One extra value of the digit only adds count. -/
theorem dLevelA_le_succ (inner : Nat → Nat) (hinner : ∀ {B B' : Nat}, B ≤ B' → inner B ≤ inner B')
    (α d B : Nat) : dLevelA inner α d B ≤ dLevelA inner α (d + 1) B := by
  show dLevelA inner α d B ≤ inner B + dLevelA inner α d (B + inner B + α)
  calc dLevelA inner α d B
        ≤ dLevelA inner α d (B + inner B + α) := dLevelA_mono_B inner hinner α d (by omega)
    _ ≤ inner B + dLevelA inner α d (B + inner B + α) := Nat.le_add_left _ _

/-- `dLevelA` is monotone in the number of digit-values `d`. -/
theorem dLevelA_mono_d (inner : Nat → Nat) (hinner : ∀ {B B' : Nat}, B ≤ B' → inner B ≤ inner B')
    (α B : Nat) {d d' : Nat} (h : d ≤ d') : dLevelA inner α d B ≤ dLevelA inner α d' B := by
  induction h with
  | refl => exact Nat.le_refl _
  | step _ ih => exact Nat.le_trans ih (dLevelA_le_succ inner hinner α _ B)

/-- **The α-generalized recursive lex-descent-length cap** for `NestedNat n` whose lower digits grow
`≤ α` per step: one level per digit, the inner cap being the budget over the digits below. -/
def descentBoundA (α : Nat) : (n : Nat) → Nat → Nat
  | 0     => fun B => α * (B + 1)
  | n + 1 => fun B => dLevelA (descentBoundA α n) α B B

/-- **`descentBoundA α n` is monotone in `B`** — the `invPhiG` cap requirement (`hcap`). By induction on
depth `n`, mirroring `descentBound_mono`. -/
theorem descentBoundA_mono (α : Nat) :
    ∀ (n : Nat) {B B' : Nat}, B ≤ B' → descentBoundA α n B ≤ descentBoundA α n B'
  | 0, B, B', h => by show α * (B + 1) ≤ α * (B' + 1); exact Nat.mul_le_mul (Nat.le_refl α) (by omega)
  | n + 1, B, B', h => by
      show dLevelA (descentBoundA α n) α B B ≤ dLevelA (descentBoundA α n) α B' B'
      exact Nat.le_trans
        (dLevelA_mono_d (descentBoundA α n) (fun hbb => descentBoundA_mono α n hbb) α B h)
        (dLevelA_mono_B (descentBoundA α n) (fun hbb => descentBoundA_mono α n hbb) α B' h)

/-- `descentBoundA 1 = descentBound` (the tower's `≤ 1` growth is the `α = 1` instance). -/
theorem descentBoundA_one_eq (n B : Nat) : descentBoundA 1 n B = descentBound n B := by
  induction n generalizing B with
  | zero => show 1 * (B + 1) = B + 1; rw [Nat.one_mul]
  | succ n ih =>
    show dLevelA (descentBoundA 1 n) 1 B B = dLevel (descentBound n) B B
    have hfun : ∀ (d B0 : Nat), dLevelA (descentBoundA 1 n) 1 d B0 = dLevel (descentBound n) d B0 := by
      intro d
      induction d with
      | zero => intro B0; exact ih B0
      | succ d ihd =>
        intro B0
        show descentBoundA 1 n B0 + dLevelA (descentBoundA 1 n) 1 d (B0 + descentBoundA 1 n B0 + 1)
           = descentBound n B0 + dLevel (descentBound n) d (B0 + descentBound n B0 + 1)
        rw [ih B0, ihd (B0 + descentBound n B0 + 1)]
    exact hfun B B

end MachLib.IterExpDepthN
