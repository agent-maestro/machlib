import MachLib.Basic

/-!
# Verified amortization — reconciles to the penny, exactly

The finance-assurance analogue of the controller contracts: a machine-checked certificate for the
property a loan servicer and an auditor actually care about — **the schedule closes out to exactly
$0.00 and the principal payments sum to exactly the loan amount**, computed in integer cents (money is
decimal fixed-point; floating point is wrong for it).

Two results, both Mathlib-free (Int + `omega` only):

* `amortization_reconciles` — for ANY balance trajectory `b` in integer cents whose per-period
  principal is `b k − b (k+1)` (the balance drops by exactly that period's principal, *whatever*
  rounding produced the interest), if it starts at the loan `P` and the final payment drives the
  balance to exactly `0`, the principals sum to **exactly `P`**. Exact (`=`, not `≤ ε`) and
  **rounding-mode-independent** — it holds because the final payment absorbs the accumulated rounding,
  which is exactly how real amortization schedules are built.

* `roundHalfEven_half_ulp` — the money rounding mode (round-half-to-even / banker's rounding) is
  correct to within **half a cent per period**: `−den ≤ 2·(den·round − num) ≤ den`, i.e.
  `|round − num/den| ≤ 1/2`.

Together: each period is cent-exact under banker's rounding, and the schedule reconciles to the penny.
This is the runtime `sims/amortization_sim.py` schedule, certified.
-/

namespace MachLib.Finance

/-! ## Exact reconciliation (integer cents) -/

/-- `Σ_{k<N} f k`, integer cents. -/
def partialSum (f : Nat → Int) : Nat → Int
  | 0 => 0
  | n + 1 => partialSum f n + f n

/-- **Telescoping.** `Σ_{k<N} (b k − b (k+1)) = b 0 − b N`. -/
theorem telescoping (b : Nat → Int) (N : Nat) :
    partialSum (fun k => b k - b (k + 1)) N = b 0 - b N := by
  induction N with
  | zero => show (0 : Int) = b 0 - b 0; omega
  | succ n ih =>
    show partialSum (fun k => b k - b (k + 1)) n + (b n - b (n + 1)) = b 0 - b (n + 1)
    rw [ih]; omega

/-- **Amortization reconciles to the penny — exactly, for any rounding.** With per-period principal
`b k − b (k+1)`, starting at the loan `P` and closing at `b N = 0`, the principal payments sum to
exactly `P`. -/
theorem amortization_reconciles (b : Nat → Int) (P : Int) (N : Nat)
    (hstart : b 0 = P) (hclose : b N = 0) :
    partialSum (fun k => b k - b (k + 1)) N = P := by
  rw [telescoping b N, hstart, hclose]; omega

/-! ## Round-half-to-even (banker's rounding) is correct to half a cent -/

/-- `round_half_even (num/den)` for `den > 0`, ties to even — the money rounding mode (matches
`sims/amortization_sim.py`). Euclidean `emod` keeps the remainder in `[0, den)`. -/
def roundHalfEven (num den : Int) : Int :=
  if 2 * (num.emod den) < den then num.ediv den
  else if 2 * (num.emod den) > den then num.ediv den + 1
  else if num.ediv den % 2 == 0 then num.ediv den else num.ediv den + 1

/-- **The money rounding mode is correct to within half a cent per period.**
`−den ≤ 2·(den·round − num) ≤ den` when `den > 0`  (i.e. `|round − num/den| ≤ 1/2`). -/
theorem roundHalfEven_half_ulp (num den : Int) (hden : 0 < den) :
    -den ≤ 2 * (den * roundHalfEven num den - num)
      ∧ 2 * (den * roundHalfEven num den - num) ≤ den := by
  have hdm : den * num.ediv den + num.emod den = num := Int.ediv_add_emod num den
  have hr0 : 0 ≤ num.emod den := Int.emod_nonneg num (by omega)
  have hr1 : num.emod den < den := Int.emod_lt_of_pos num hden
  have hsucc : den * (num.ediv den + 1) = den * num.ediv den + den := by
    rw [Int.mul_add, Int.mul_one]
  unfold roundHalfEven
  repeat' split
  all_goals omega

end MachLib.Finance
