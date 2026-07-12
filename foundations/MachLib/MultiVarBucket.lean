import MachLib.MultiVar

/-!
# Bucketing: flat solution count from #keys × fiber-size (Gate 2d, full polynomial Bezout)

`prsResultant_xbound` bounds the number of distinct x-coordinates of common zeros; `fiber_count` bounds
each vertical fiber. To combine them into a bound on the **total** solution count (a flat `Nodup` list of
solution points), we need the combinatorial bucketing: a list whose keys lie in `keys` (`|keys| ≤ A`) and
whose every key-fiber has `≤ B` elements has length `≤ A·B`. Classical (decidable key equality) + core
`List`. This file proves the key-agnostic combinatorial core.
-/

namespace MachLib
namespace MultiVarMod

open Classical

/-- Filtering by `p` and by `¬p` partitions the length. -/
theorem length_filter_partition {α : Type} (p : α → Bool) :
    ∀ l : List α, (l.filter p).length + (l.filter (fun a => !p a)).length = l.length
  | [] => rfl
  | a :: l => by
      have ih := length_filter_partition p l
      rw [List.filter_cons, List.filter_cons]
      cases hp : p a <;> simp [hp] <;> omega

/-- **Bucketing.** A list whose keys all lie in `keys`, and each of whose key-fibers has `≤ B` elements,
has length `≤ |keys|·B`. The combinatorial core of the full solution count: `keys` = the distinct
x-coordinates (`≤ deg_x R` by `prsResultant_xbound`), `B` = the fiber bound (`deg_y` by `fiber_count`). -/
theorem length_le_bucket {α β : Type} (key : α → β) (B : Nat) :
    ∀ (keys : List β) (l : List α),
      (∀ a ∈ l, key a ∈ keys) →
      (∀ k : β, (l.filter (fun a => decide (key a = k))).length ≤ B) →
      l.length ≤ keys.length * B
  | [], l, hcov, _ => by
      have hl : l = [] := by
        cases l with
        | nil => rfl
        | cons a as => exact absurd (hcov a (List.mem_cons_self a as)) (List.not_mem_nil _)
      rw [hl]; simp
  | k :: keys', l, hcov, hfib => by
      have hpart := length_filter_partition (fun a => decide (key a = k)) l
      have h1 : (l.filter (fun a => decide (key a = k))).length ≤ B := hfib k
      have hcov' : ∀ a ∈ l.filter (fun a => !decide (key a = k)), key a ∈ keys' := by
        intro a ha
        rw [List.mem_filter] at ha
        obtain ⟨hal, hak⟩ := ha
        have hne : key a ≠ k := by simpa using hak
        rcases List.mem_cons.mp (hcov a hal) with h | h
        · exact absurd h hne
        · exact h
      have hfib' : ∀ k' : β,
          ((l.filter (fun a => !decide (key a = k))).filter (fun a => decide (key a = k'))).length ≤ B :=
        fun k' => Nat.le_trans
          (List.Sublist.length_le
            (List.Sublist.filter (fun a => decide (key a = k')) (List.filter_sublist l)))
          (hfib k')
      have hrec := length_le_bucket key B keys' (l.filter (fun a => !decide (key a = k))) hcov' hfib'
      calc l.length
          = (l.filter (fun a => decide (key a = k))).length
            + (l.filter (fun a => !decide (key a = k))).length := hpart.symm
        _ ≤ B + keys'.length * B := Nat.add_le_add h1 hrec
        _ = (k :: keys').length * B := by rw [List.length_cons, Nat.succ_mul]; omega

end MultiVarMod
end MachLib
