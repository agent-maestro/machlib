import MachLib.Rolle

/-!
# Arc count bound: `#arcs ≤ #critical-points + 1` (Gate 2d, two-exp — the topological input M)

The arc count `M` in `khovanskii_rolle_multiarc` — the number of monotonic arcs of `{f = 0}` — is a
topological quantity, but the model has no topology. The honest combinatorial core: **arcs are pairwise
separated by critical points** (between two adjacent monotonic arcs of `{f=0}` there is a point where the
parametrization breaks, `fᵧ = 0`), so `n` arcs need `n−1` separating critical points, whence
`#arcs ≤ #critical + 1`.

This is the SAME interleaving structure as `zero_count_bound_by_deriv` (`n` zeros ⟹ `n−1` derivative-zeros
by Rolle), but the separator between adjacent arcs is taken as a HYPOTHESIS — bundled into a `ChainSep`
predicate carrying both the sorting and the separator between each consecutive pair — rather than produced
by `rolle_ct`. (`List.Chain` is absent from this toolchain, so `ChainSep` is the local equivalent.) The
resulting bound is `arc_count_le`: with the critical points `N`-bounded (the recursive input — `#critical =
#{f=0, fᵧ=0}`, itself a Khovanskii–Rolle count), the arcs number `≤ N + 1`. Pure combinatorics.
-/

namespace MachLib
namespace Real

/-- A sorted-with-separators chain: each consecutive pair `u, v` satisfies `u < v` and has a separator
`w ∈ (u, v)` with `sep w`. -/
def ChainSep (sep : Real → Prop) : Real → List Real → Prop
  | _, [] => True
  | hd, z1 :: rest => (hd < z1 ∧ ∃ w, hd < w ∧ w < z1 ∧ sep w) ∧ ChainSep sep z1 rest

/-- **Interleaving core.** A `ChainSep` (adjacent links `u < v` with a separator `w ∈ (u,v)`, `sep w`)
yields a `Nodup` list `cs` of separators — one strictly between each consecutive pair, each `> hd` — of
length `≥ length − 1`. Mirror of `interleave_from`, with the separator hypothesized instead of produced by
Rolle. -/
theorem interleave_sep (sep : Real → Prop) :
    ∀ (hd : Real) (s : List Real), ChainSep sep hd s →
      ∃ cs : List Real, cs.Nodup ∧ (∀ c ∈ cs, sep c) ∧ (∀ c ∈ cs, hd < c) ∧
        (hd :: s).length ≤ cs.length + 1 := by
  intro hd s
  induction s generalizing hd with
  | nil =>
    intro _
    exact ⟨[], List.nodup_nil, fun c hc => absurd hc (List.not_mem_nil c),
      fun c hc => absurd hc (List.not_mem_nil c), by simp⟩
  | cons z1 rest ih =>
    intro hchain
    obtain ⟨⟨hhd_z1, w0, hw0_lo, hw0_hi, hw0_sep⟩, hchain_tail⟩ := hchain
    obtain ⟨cs', hcs'_nodup, hcs'_sep, hcs'_gt, hcs'_len⟩ := ih z1 hchain_tail
    refine ⟨w0 :: cs', ?_, ?_, ?_, ?_⟩
    · rw [List.nodup_cons]
      exact ⟨fun hmem => lt_irrefl_ax w0 (lt_trans_ax hw0_hi (hcs'_gt w0 hmem)), hcs'_nodup⟩
    · intro c hc
      rcases List.mem_cons.mp hc with rfl | h
      · exact hw0_sep
      · exact hcs'_sep c h
    · intro c hc
      rcases List.mem_cons.mp hc with rfl | h
      · exact hw0_lo
      · exact lt_trans_ax hhd_z1 (hcs'_gt c h)
    · simp only [List.length_cons] at hcs'_len ⊢
      omega

/-- **Arc count bound.** A nonempty list of arcs whose adjacent (sorted) elements are separated by a
critical point (`ChainSep`), with the critical points `N`-bounded (`hN`), numbers `≤ N + 1`. The
`M ≤ #critical + 1` of the Khovanskii–Rolle multi-arc bound; `#critical = #{f=0, fᵧ=0}` is the recursive
Khovanskii input. (The empty arc list is trivially `0 ≤ N+1`.) -/
theorem arc_count_le (sep : Real → Prop) (N : Nat)
    (hN : ∀ ss : List Real, ss.Nodup → (∀ s ∈ ss, sep s) → ss.length ≤ N)
    (hd : Real) (s : List Real) (hchain : ChainSep sep hd s) :
    (hd :: s).length ≤ N + 1 := by
  obtain ⟨cs, hcs_nodup, hcs_sep, _, hcs_len⟩ := interleave_sep sep hd s hchain
  exact Nat.le_trans hcs_len (Nat.succ_le_succ (hN cs hcs_nodup hcs_sep))

end Real
end MachLib
