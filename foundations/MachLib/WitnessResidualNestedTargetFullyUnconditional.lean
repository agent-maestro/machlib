import MachLib.WitnessResidualNestedTargetTailSign

/-!
# The FULL closure: no finite EML tree equals any well-formed `nestedTarget cs` — no restriction

Continuation of Option D (`EML_WITNESS_FINDING_DECISION_2026_07_15.md`). Cont. 68 pinned the exact
remaining gap for `c2 ≥ 2`: `TailSign` cannot separate a tree from `log(c2+\sin x)` there, since
that target is entirely positive (has its own `TailSign.pos`). The natural fallback was the
original Khovanskii/`EMLPfaffianValidOn` route — genuinely hard, multi-session by this arc's own
repeated estimate. This file finds a THIRD way, using a tool built for `TailSign` but never
applied to the zero-counting argument directly: `eml_eventually_valid_repr`.

**The idea.** `no_tree_eq_target_given_validon`'s zero-counting argument needs `EMLPfaffianValidOn
T1` on an interval `(0, b)` — validity from `0`. But it only ever USES that validity to run
`enc_combinedBound` on ONE bounded sub-interval, chosen to contain `M+1` zeros of the target
(`kπ`, giving a fixed level `L`) plus one nonzero witness (`π+1`). `eml_eventually_valid_repr`
gives every tree `T` a representative `Trep` that is valid on a TAIL (not from `0`) and matches
`T`'s value on a (possibly different) tail. `nestedTarget cs`'s `kπ`-level fact holds at EVERY
`k ≥ 1` (not just `k` past some threshold) and its `π+1` witness recurs at `π+1+2mπ` for every `m`
(`nestedTarget_add_natCast_mul_two_pi`, cont. 59) — so BOTH ingredients the zero-counting argument
needs are available ARBITRARILY FAR OUT, not just near `0`. Running the argument entirely within
the region where `Trep` is valid AND matches `T` closes it — no straddle condition, no
`RightChildrenSimplePositive` restriction, no validity-from-`0` hypothesis at all.

**Payoff.** `no_tree_eq_nestedTarget_fully_unconditional` — no finite EML tree's `eval` equals any
WELL-FORMED `nestedTarget cs`, completely unconditionally. This supersedes cont. 59-63's
straddle-conditioned version entirely (which needed `nestedLo cs ≤ 0 < nestedHi cs`) and closes
`c2 ≥ 2` (indeed every `c2 > 1`) directly, removing `eml_depth2_witness_of_const_gt_one_sibling_
simple_T1`'s `RightChildrenSimplePositive T1` restriction for ALL `c2 > 1`, not just `1 < c2 ≤ 2`.
-/

open MachLib.EMLExplicitBound
open MachLib.EMLLogArgPosBridge
open MachLib.PfaffianGeneralReduce
open MachLib.MultiPolyMod

namespace MachLib
namespace Real

/-- `natCast` is strictly monotone — the plain Nat-order fact `natCast_mul_pi_lt`'s own induction
uses internally, extracted standalone since this file needs it without the `*pi` factor too. -/
theorem natCast_lt_natCast_of_lt {j k : Nat} (hjk : j < k) : natCast j < natCast k := by
  induction k with
  | zero => omega
  | succ m ih =>
    by_cases h : j < m
    · have ih' := ih h
      rw [natCast_succ]
      exact lt_trans_ax ih' (lt_add_pos (natCast m) 1 zero_lt_one_ax)
    · have hjm : j = m := by omega
      rw [hjm, natCast_succ]
      exact lt_add_pos (natCast m) 1 zero_lt_one_ax

/-- `pi < (1+1)*pi` — `2π` strictly exceeds `π`. -/
theorem pi_lt_two_pi : pi < (1 + 1) * pi := by
  rw [mul_distrib_right, one_mul_thm]
  exact lt_add_pos pi pi pi_pos

/-- A `π`-multiple is always strictly exceeded by a `2π`-multiple with a STRICTLY larger natural
index — the comparison the periodicity-shifted witness point needs against the `kπ`-family zeros. -/
theorem natCast_mul_pi_lt_natCast_mul_two_pi {j k : Nat} (hjk : j < k) :
    natCast j * pi < natCast k * ((1 + 1) * pi) := by
  have h1 : natCast j * pi < natCast k * pi := natCast_mul_pi_lt hjk
  have hkpos : (0 : Real) < natCast k := by
    rcases Nat.eq_zero_or_pos k with hk0 | hkpos'
    · exfalso; omega
    · have h := natCast_lt_natCast_of_lt hkpos'
      rwa [natCast_zero] at h
  have h2 : natCast k * pi < natCast k * ((1 + 1) * pi) := by
    have h := mul_lt_mul_of_pos_right pi_lt_two_pi hkpos
    rwa [mul_comm pi (natCast k), mul_comm ((1+1)*pi) (natCast k)] at h
  exact lt_trans_ax h1 h2

/-- The `kπ`-family, shifted by a fixed offset `K`, remains pairwise distinct — same
`List.nodup_range.map` recipe used throughout this arc for growing zero families. -/
theorem natCast_kpi_shifted_list_nodup (K M : Nat) :
    ((List.range (M + 1)).map (fun i => natCast (K + i + 1) * pi)).Nodup := by
  show List.Pairwise (· ≠ ·) ((List.range (M + 1)).map (fun i => natCast (K + i + 1) * pi))
  exact (List.nodup_range (M + 1)).map (fun i => natCast (K + i + 1) * pi)
    (fun i j (_hij_neq : i ≠ j) => by
      intro hij_eq
      dsimp only at hij_eq
      rcases Nat.lt_or_ge i j with hlt | hge
      · have h := natCast_mul_pi_lt (show K + i + 1 < K + j + 1 by omega)
        rw [hij_eq] at h
        exact lt_irrefl_ax _ h
      · have hlt2 : j < i := by omega
        have h := natCast_mul_pi_lt (show K + j + 1 < K + i + 1 by omega)
        rw [← hij_eq] at h
        exact lt_irrefl_ax _ h)

/-- **The full closure.** No finite EML tree's `eval` equals a well-formed `nestedTarget cs`,
completely unconditionally — no straddle condition on `nestedLo`/`nestedHi`, no restriction on
`T` at all. Mirrors `no_tree_eq_target_given_validon`'s zero-counting argument, but run entirely
on a tail: `eml_eventually_valid_repr` supplies a representative `Trep` valid past some `a` and
matching `T` past some `R`; `nestedTarget cs`'s `kπ`-level fact and periodicity-shifted `π+1`
witness are both available past ANY threshold, so the whole argument lives inside `(a', b)` for a
suitably large `a'`, never needing validity from `0`. -/
theorem no_tree_eq_nestedTarget_fully_unconditional (cs : List Real) (hwf : nestedWF cs)
    (T : EMLTree) (heq : ∀ x : Real, T.eval x = nestedTarget cs x) : False := by
  obtain ⟨Trep, a, hvalid, R, heqR⟩ := eml_eventually_valid_repr T
  obtain ⟨_hrange, hkpi, hpi1⟩ := nestedTarget_facts cs hwf
  let p := (enc Trep emlEmptyChain).2
  let p' := MultiPoly.sub p (MultiPoly.const (nestedLevel cs))
  let M := combinedBoundE (len Trep 0) (enc Trep emlEmptyChain).1 (encTags Trep emlEmptyChain ()) p'
  obtain ⟨T0, haT0, hRT0⟩ := lt_of_lt_both a R
  obtain ⟨K, hK⟩ := archimedean T0
  have hKpi : T0 < natCast K * pi := lt_of_lt_of_le hK (natCast_le_natCast_mul_pi K)
  have haa' : a < natCast K * pi := lt_trans_ax haT0 hKpi
  have hRa' : R < natCast K * pi := lt_trans_ax hRT0 hKpi
  have hzM1 : natCast K * pi < natCast (K + M + 1) * pi :=
    natCast_mul_pi_lt (show K < K + M + 1 by omega)
  let w : Real := pi + 1 + natCast (K + M + 2) * ((1 + 1) * pi)
  have hzM1_lt_w : natCast (K + M + 1) * pi < w := by
    have h := natCast_mul_pi_lt_natCast_mul_two_pi (show K + M + 1 < K + M + 2 by omega)
    have hpi1pos : (0 : Real) < pi + 1 := lt_trans_ax pi_pos (lt_add_pos pi 1 zero_lt_one_ax)
    have hstep := lt_add_pos (natCast (K + M + 2) * ((1 + 1) * pi)) (pi + 1) hpi1pos
    rw [add_comm (natCast (K + M + 2) * ((1 + 1) * pi)) (pi + 1)] at hstep
    exact lt_trans_ax h hstep
  let b : Real := w + 1
  have hwb : w < b := lt_add_pos w 1 zero_lt_one_ax
  have ha'b : natCast K * pi < b :=
    lt_trans_ax (lt_trans_ax hzM1 hzM1_lt_w) hwb
  have hRw : R < w := lt_trans_ax hRa' (lt_trans_ax hzM1 hzM1_lt_w)
  have houter : b < b + 1 := lt_add_pos b 1 zero_lt_one_ax
  have hab1 : a < b + 1 := lt_trans_ax haa' (lt_trans_ax ha'b houter)
  have hvalidon_here : EMLPfaffianValidOn Trep a (b + 1) := hvalid (b + 1) hab1
  have hlogPos : LogArgPosOn Trep (Icc (natCast K * pi) b) :=
    logArgPosOn_Icc_of_validOn Trep a (b + 1) (natCast K * pi) b haa' houter hvalidon_here
  have hne : ∃ z : Real, natCast K * pi < z ∧ z < b ∧
      (pfaffianChainFn (enc Trep emlEmptyChain).1 p').eval z ≠ 0 := by
    refine ⟨w, lt_trans_ax hzM1 hzM1_lt_w, hwb, ?_⟩
    show MultiPoly.eval p' w ((enc Trep emlEmptyChain).1.chainValues w) ≠ 0
    show MultiPoly.eval p w ((enc Trep emlEmptyChain).1.chainValues w) - nestedLevel cs ≠ 0
    have heval : MultiPoly.eval p w ((enc Trep emlEmptyChain).1.chainValues w)
        = Trep.eval w := enc_eval Trep emlEmptyChain w
    rw [heval, heqR w hRw, heq w]
    intro hz
    have e : nestedTarget cs w = (nestedTarget cs w - nestedLevel cs) + nestedLevel cs := by
      mach_ring
    rw [hz] at e
    have e2 : (0 : Real) + nestedLevel cs = nestedLevel cs := by mach_ring
    rw [e2] at e
    have hne' : nestedTarget cs w ≠ nestedLevel cs := by
      rw [show w = pi + 1 + natCast (K + M + 2) * ((1 + 1) * pi) from rfl,
        nestedTarget_add_natCast_mul_two_pi]
      exact hpi1
    exact hne' e
  have hbound := enc_combinedBound Trep emlEmptyChain () (natCast K * pi) b ha'b
    trivial trivial (fun i _ hij => i.elim0) (fun _ _ _ i => i.elim0) (fun i => i.elim0)
    hlogPos p' hne
  let zeros : List Real := (List.range (M + 1)).map (fun i => natCast (K + i + 1) * pi)
  have hzeros_len : zeros.length = M + 1 := by
    simp [zeros, List.length_map, List.length_range]
  have hzeros_valid : ∀ z ∈ zeros,
      natCast K * pi < z ∧ z < b ∧
        (pfaffianChainFn (enc Trep emlEmptyChain).1 p').eval z = 0 := by
    intro z hz
    simp only [zeros, List.mem_map, List.mem_range] at hz
    obtain ⟨i, hilt, hzeq⟩ := hz
    have hzR0 : R < natCast (K + i + 1) * pi :=
      lt_trans_ax hRa' (natCast_mul_pi_lt (show K < K + i + 1 by omega))
    have hzR : R < z := by rw [← hzeq]; exact hzR0
    refine ⟨?_, ?_, ?_⟩
    · rw [← hzeq]; exact natCast_mul_pi_lt (show K < K + i + 1 by omega)
    · rw [← hzeq]
      rcases Nat.lt_or_ge i M with hlt | hge
      · exact lt_trans_ax (natCast_mul_pi_lt (show K + i + 1 < K + M + 1 by omega))
          (lt_trans_ax hzM1_lt_w hwb)
      · have hiM : i = M := by omega
        rw [hiM]; exact lt_trans_ax hzM1_lt_w hwb
    · rw [← hzeq]
      show MultiPoly.eval p (natCast (K + i + 1) * pi)
          ((enc Trep emlEmptyChain).1.chainValues (natCast (K + i + 1) * pi))
          - nestedLevel cs = 0
      have heval : MultiPoly.eval p (natCast (K + i + 1) * pi)
          ((enc Trep emlEmptyChain).1.chainValues (natCast (K + i + 1) * pi))
          = Trep.eval (natCast (K + i + 1) * pi) := enc_eval Trep emlEmptyChain _
      rw [heval, heqR _ hzR0, heq]
      rw [hkpi (K + i + 1) (by omega)]
      mach_ring
  have hzeros_nodup : zeros.Nodup := natCast_kpi_shifted_list_nodup K M
  have hlen_le : zeros.length ≤ M := hbound zeros hzeros_nodup hzeros_valid
  rw [hzeros_len] at hlen_le
  omega

/-- **`log(c2+\sin x)`, for EVERY `c2 > 1`, no upper bound.** Supersedes cont. 60's
`no_tree_eq_log_c2_plus_sin_unconditional`, which needed `c2 ≤ 2`. -/
theorem no_tree_eq_log_c2_plus_sin_fully_unconditional (c2 : Real) (hc2 : 1 < c2)
    (T : EMLTree) (heq : ∀ x : Real, T.eval x = Real.log (c2 + Real.sin x)) : False := by
  have hc2m1_pos : (0 : Real) < c2 - 1 := by
    have h01 : (0 : Real) + 1 = 1 := by mach_ring
    exact lt_sub_of_add_lt (by rw [h01]; exact hc2)
  have hwf : nestedWF [c2] := by
    refine ⟨?_, trivial⟩
    show (0 : Real) < c2 + (-1)
    have e : c2 + (-1 : Real) = c2 - 1 := by mach_ring
    rw [e]; exact hc2m1_pos
  have heq' : ∀ x : Real, T.eval x = nestedTarget [c2] x := by
    intro x
    rw [nestedTarget_cons, nestedTarget_nil]
    exact heq x
  exact no_tree_eq_nestedTarget_fully_unconditional [c2] hwf T heq'

end Real
end MachLib
