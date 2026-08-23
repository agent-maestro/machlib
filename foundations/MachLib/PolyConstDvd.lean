import MachLib.PolyPoleCount

/-!
# An irreducible never divides a nonzero constant

A small module with a specific purpose: separating the *polynomial* content of the composition's
second characteristic-zero input from its *field* content.

`cleared_relation_impossible` needs `q ∤ Nc` for the constant `Nc = n·1`, `n = m − j`. That looks
like another statement about divisibility, and it is not: `Pdvd_length` already says a divisor is no
longer than what it divides, so an irreducible — degree `≥ 2` by definition — cannot divide anything
of degree `0`. The only way `q ∣ Nc` can hold is `Nc ≈ 0`.

So the input reduces to **`Nc ≉ 0`**, which is `natCast n ≠ 0` — a statement about `ℝ` with no
polynomial content at all. That is worth doing before the composition rather than after: it fixes
what the final theorem's hypotheses look like, and a hypothesis phrased as "`q` does not divide this
constant" would have obscured that the content is characteristic zero and nothing else.

Everything here is field-axiom-only and inside invariant (7).
-/

namespace MachLib

open Real

/-- The contrapositive of `Pdvd_length`: too short to be divisible. -/
theorem not_Pdvd_of_length_lt {q A : List Real} (hq : PNormal q) (hqne : q ≠ [])
    (hA : pnorm A ≠ []) (hlt : (pnorm A).length < q.length) : ¬ Pdvd q A := by
  intro h
  have hle := Pdvd_length hq hqne hA h
  omega

/-- **An irreducible does not divide a nonzero constant.** Degree alone settles it. -/
theorem not_Pdvd_const {q c : List Real} (hq : PIrred q)
    (hc : pnorm c ≠ []) (hlen : c.length ≤ 1) : ¬ Pdvd q c := by
  have hqn := hq.1
  have hqlen := hq.2.1
  have hqne : q ≠ [] := by
    intro h; rw [h] at hqlen; exact Nat.not_succ_le_zero 1 hqlen
  refine not_Pdvd_of_length_lt hqn hqne hc ?_
  have h1 : (pnorm c).length ≤ c.length := pnorm_length_le c
  omega

/-- `pnsum n [1]` is a single coefficient however large `n` is — `padd` against a length-one list
never lengthens it. -/
theorem pnsum_one_length : ∀ n : Nat, (pnsum n [(1 : Real)]).length ≤ 1 := by
  intro n
  induction n with
  | zero => exact Nat.zero_le 1
  | succ k ih =>
      show (padd [(1 : Real)] (pnsum k [1])).length ≤ 1
      rw [padd_length_ge [(1 : Real)] (pnsum k [1]) (by simpa using ih)]
      simp

/-- The form the composition consumes: the constant `n·1` is undivided by `q` exactly when it is
nonzero, which is `natCast n ≠ 0` and nothing more. -/
theorem not_Pdvd_pnsum_one {q : List Real} (hq : PIrred q) {n : Nat}
    (hn : pnorm (pnsum n [1]) ≠ []) : ¬ Pdvd q (pnsum n [1]) :=
  not_Pdvd_const hq hn (pnsum_one_length n)

end MachLib
