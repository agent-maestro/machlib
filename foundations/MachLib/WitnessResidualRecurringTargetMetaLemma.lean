import MachLib.WitnessResidualNestedTargetFullyUnconditional

/-!
# The meta-lemma: no finite EML tree equals any target with a recurring level and witness

Continuation of Option D (`EML_WITNESS_FINDING_DECISION_2026_07_15.md`). Two muses independently
flagged the same generalization after cont. 69: the tail-restricted zero-counting argument doesn't
actually use much about `nestedTarget` specifically — it uses (a) a zero-value fact recurring at
infinitely many points marching to infinity, and (b) a witness value recurring arbitrarily far
out, exceeding each zero. Checked directly, within a bounded effort, rather than assumed: yes, the
quantifier bookkeeping IS genuinely uniform. `no_tree_eq_recurring_target_fully_unconditional`
below is a mechanical lift of `no_tree_eq_nestedTarget_fully_unconditional`'s own proof — every
`nestedTarget`-specific step (the `kπ`-family's monotonicity/unboundedness, the periodicity-shifted
witness) is replaced by an abstract hypothesis of the identical shape, and the proof body is
otherwise IDENTICAL. `no_tree_eq_nestedTarget_fully_unconditional_via_meta` re-derives cont. 69's
own theorem as a five-line instantiation, confirming the abstraction is equivalent to, not merely
similar to, the concrete result.

**The hypothesis shape, stated precisely.** A strictly increasing, unbounded `Nat`-indexed family
`Z` at which `TARGET` takes a fixed value `L` (the "recurring zero"), and a family `W` — indexed
the SAME way, each `W n` exceeding the CORRESPONDING `Z n` — at which `TARGET` differs from `L`
(the "recurring witness"). This is genuinely a special case of a WEAKER, more general condition
(`TARGET` having no `TailSign` relative to `L` — i.e., `¬TailSign (fun x => TARGET x - L)`, in the
sense already built for `sin`/`cos`/`nestedTarget`) — but closing THAT weaker form here would need
target-side continuity plus an IVT-based zero CONSTRUCTION (mirroring `rcep_zero_between`'s own
machinery, built for EML trees specifically, not yet built for an arbitrary continuous function).
Flagged as the natural further generalization, NOT attempted this round — this file captures the
level that was actually reachable within the check, honestly, rather than reaching further and
guessing.

**Payoff.** One proof, `nestedTarget cs` (hence `sin`, `cos`, and `log(c2+\sin x)` for every
`c2 > 1`, all as special cases via `cs = []`, `cs = [c2]`) all become five-line instantiations
rather than a fresh round each. This retroactively unifies cont. 58's `sin` result and cont. 69's
`nestedTarget` result as corollaries of ONE statement, matching exactly what was asked for.
-/

namespace MachLib
namespace Real

open MachLib.EMLExplicitBound
open MachLib.EMLLogArgPosBridge
open MachLib.PfaffianGeneralReduce
open MachLib.MultiPolyMod

/-- **The meta-lemma.** No finite EML tree equals `TARGET`, given a recurring level `Z`/`L` and a
recurring witness `W` exceeding each `Z n`. Identical proof shape to `no_tree_eq_nestedTarget_
fully_unconditional` — `eml_eventually_valid_repr` supplies a tail where SOME representative is
valid; `Z`'s unboundedness places `M+1` distinct recurring-level points inside that tail; `W` at
the largest such index supplies the nonzero witness the zero-count bound needs. -/
theorem no_tree_eq_recurring_target_fully_unconditional
    (TARGET : Real → Real) (L : Real)
    (Z : Nat → Real) (hZmono : ∀ i j : Nat, i < j → Z i < Z j)
    (hZunbounded : ∀ R : Real, ∃ n : Nat, R < Z n)
    (hZeq : ∀ n : Nat, TARGET (Z n) = L)
    (W : Nat → Real) (hWgt : ∀ n : Nat, Z n < W n) (hWne : ∀ n : Nat, TARGET (W n) ≠ L)
    (T : EMLTree) (heq : ∀ x : Real, T.eval x = TARGET x) : False := by
  obtain ⟨Trep, a, hvalid, R, heqR⟩ := eml_eventually_valid_repr T
  let p := (enc Trep emlEmptyChain).2
  let p' := MultiPoly.sub p (MultiPoly.const L)
  let M := combinedBoundE (len Trep 0) (enc Trep emlEmptyChain).1 (encTags Trep emlEmptyChain ()) p'
  obtain ⟨T0, haT0, hRT0⟩ := lt_of_lt_both a R
  obtain ⟨K, hK⟩ := hZunbounded T0
  have haa' : a < Z K := lt_trans_ax haT0 hK
  have hRa' : R < Z K := lt_trans_ax hRT0 hK
  have hzM1 : Z K < Z (K + M + 2) := hZmono K (K + M + 2) (by omega)
  have hzM1_lt_w : Z (K + M + 2) < W (K + M + 2) := hWgt (K + M + 2)
  let b : Real := W (K + M + 2) + 1
  have hwb : W (K + M + 2) < b := lt_add_pos (W (K + M + 2)) 1 zero_lt_one_ax
  have ha'b : Z K < b := lt_trans_ax (lt_trans_ax hzM1 hzM1_lt_w) hwb
  have hRw : R < W (K + M + 2) := lt_trans_ax hRa' (lt_trans_ax hzM1 hzM1_lt_w)
  have houter : b < b + 1 := lt_add_pos b 1 zero_lt_one_ax
  have hab1 : a < b + 1 := lt_trans_ax haa' (lt_trans_ax ha'b houter)
  have hvalidon_here : EMLPfaffianValidOn Trep a (b + 1) := hvalid (b + 1) hab1
  have hlogPos : LogArgPosOn Trep (Icc (Z K) b) :=
    logArgPosOn_Icc_of_validOn Trep a (b + 1) (Z K) b haa' houter hvalidon_here
  have hne : ∃ z : Real, Z K < z ∧ z < b ∧
      (pfaffianChainFn (enc Trep emlEmptyChain).1 p').eval z ≠ 0 := by
    refine ⟨W (K + M + 2), lt_trans_ax hzM1 hzM1_lt_w, hwb, ?_⟩
    show MultiPoly.eval p' (W (K + M + 2)) ((enc Trep emlEmptyChain).1.chainValues
      (W (K + M + 2))) ≠ 0
    show MultiPoly.eval p (W (K + M + 2))
      ((enc Trep emlEmptyChain).1.chainValues (W (K + M + 2))) - L ≠ 0
    have heval : MultiPoly.eval p (W (K + M + 2))
        ((enc Trep emlEmptyChain).1.chainValues (W (K + M + 2)))
        = Trep.eval (W (K + M + 2)) := enc_eval Trep emlEmptyChain (W (K + M + 2))
    rw [heval, heqR _ hRw, heq]
    intro hz
    have e : TARGET (W (K + M + 2)) = (TARGET (W (K + M + 2)) - L) + L := by mach_ring
    rw [hz] at e
    have e2 : (0 : Real) + L = L := by mach_ring
    rw [e2] at e
    exact hWne (K + M + 2) e
  have hbound := enc_combinedBound Trep emlEmptyChain () (Z K) b ha'b
    trivial trivial (fun i _ hij => i.elim0) (fun _ _ _ i => i.elim0) (fun i => i.elim0)
    hlogPos p' hne
  let zeros : List Real := (List.range (M + 1)).map (fun i => Z (K + i + 1))
  have hzeros_len : zeros.length = M + 1 := by
    simp [zeros, List.length_map, List.length_range]
  have hzeros_valid : ∀ z ∈ zeros,
      Z K < z ∧ z < b ∧
        (pfaffianChainFn (enc Trep emlEmptyChain).1 p').eval z = 0 := by
    intro z hz
    simp only [zeros, List.mem_map, List.mem_range] at hz
    obtain ⟨i, hilt, hzeq⟩ := hz
    have hzR0 : R < Z (K + i + 1) := lt_trans_ax hRa' (hZmono K (K + i + 1) (by omega))
    have hzR : R < z := by rw [← hzeq]; exact hzR0
    refine ⟨?_, ?_, ?_⟩
    · rw [← hzeq]; exact hZmono K (K + i + 1) (by omega)
    · rw [← hzeq]
      rcases Nat.lt_or_ge i M with hlt | hge
      · exact lt_trans_ax (hZmono (K + i + 1) (K + M + 2) (by omega))
          (lt_trans_ax hzM1_lt_w hwb)
      · have hiM : i = M := by omega
        rw [hiM]
        exact lt_trans_ax (hZmono (K + M + 1) (K + M + 2) (by omega))
          (lt_trans_ax hzM1_lt_w hwb)
    · rw [← hzeq]
      show MultiPoly.eval p (Z (K + i + 1))
          ((enc Trep emlEmptyChain).1.chainValues (Z (K + i + 1))) - L = 0
      have heval : MultiPoly.eval p (Z (K + i + 1))
          ((enc Trep emlEmptyChain).1.chainValues (Z (K + i + 1)))
          = Trep.eval (Z (K + i + 1)) := enc_eval Trep emlEmptyChain _
      rw [heval, heqR _ hzR0, heq, hZeq (K + i + 1)]
      mach_ring
  have hzeros_nodup : zeros.Nodup := by
    show List.Pairwise (· ≠ ·) zeros
    exact (List.nodup_range (M + 1)).map (fun i => Z (K + i + 1))
      (fun i j (_hij_neq : i ≠ j) => by
        intro hij_eq
        dsimp only at hij_eq
        rcases Nat.lt_or_ge i j with hlt | hge
        · have h := hZmono (K + i + 1) (K + j + 1) (by omega)
          rw [hij_eq] at h
          exact lt_irrefl_ax _ h
        · have hlt2 : j < i := by omega
          have h := hZmono (K + j + 1) (K + i + 1) (by omega)
          rw [← hij_eq] at h
          exact lt_irrefl_ax _ h)
  have hlen_le : zeros.length ≤ M := hbound zeros hzeros_nodup hzeros_valid
  rw [hzeros_len] at hlen_le
  omega

/-- **The test: does `nestedTarget cs` instantiate cleanly?** Yes — `Z n := natCast(n+1)*π`
(`nestedTarget cs`'s own `kπ`-level fact, `nestedTarget_facts`), `W n := π+1+natCast(n+2)*(2π)`
(the periodicity-shifted witness, `nestedTarget_add_natCast_mul_two_pi`). Every hypothesis the
meta-lemma needs is EXACTLY a fact already built for `no_tree_eq_nestedTarget_fully_unconditional`
— no new reasoning, no target-specific epsilon smuggled in. Confirms the abstraction is genuinely
uniform, not merely superficially similar. -/
theorem no_tree_eq_nestedTarget_fully_unconditional_via_meta (cs : List Real) (hwf : nestedWF cs)
    (T : EMLTree) (heq : ∀ x : Real, T.eval x = nestedTarget cs x) : False := by
  obtain ⟨_hrange, hkpi, hpi1⟩ := nestedTarget_facts cs hwf
  apply no_tree_eq_recurring_target_fully_unconditional (nestedTarget cs) (nestedLevel cs)
    (fun n => natCast (n + 1) * pi)
    (fun i j hij => natCast_mul_pi_lt (show i + 1 < j + 1 by omega))
    (fun R => by
      obtain ⟨n, hn⟩ := archimedean R
      refine ⟨n, lt_trans_ax hn (lt_of_lt_of_le ?_ (natCast_le_natCast_mul_pi (n + 1)))⟩
      exact natCast_lt_natCast_of_lt (show n < n + 1 by omega))
    (fun n => hkpi (n + 1) (by omega))
    (fun n => pi + 1 + natCast (n + 2) * ((1 + 1) * pi))
    (fun n => by
      have h := natCast_mul_pi_lt_natCast_mul_two_pi (show n + 1 < n + 2 by omega)
      have hpi1pos : (0 : Real) < pi + 1 := lt_trans_ax pi_pos (lt_add_pos pi 1 zero_lt_one_ax)
      have hstep := lt_add_pos (natCast (n + 2) * ((1 + 1) * pi)) (pi + 1) hpi1pos
      rw [add_comm (natCast (n + 2) * ((1 + 1) * pi)) (pi + 1)] at hstep
      exact lt_trans_ax h hstep)
    (fun n => by rw [nestedTarget_add_natCast_mul_two_pi]; exact hpi1)
    T heq

end Real
end MachLib
