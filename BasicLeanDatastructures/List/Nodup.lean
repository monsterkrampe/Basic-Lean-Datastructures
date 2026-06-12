/-
Copyright 2026 Lukas Gerlach
Released under Apache 2.0 license as described in the file LICENSE.
-/

module

/-!
This file contains auxiliary results for lists without duplicates (which have the Nodup property).
-/

public section

namespace List

/-- If two lists have no duplicates and have the same elements, then their length is the same. Note that the lists are not necessarily equal since the order of elements may differ. -/
theorem length_eq_of_nodup_of_same_elements [DecidableEq α]
    (as bs : List α) (nodup_as : as.Nodup) (nodup_bs : bs.Nodup) (same_elems : ∀ e, e ∈ as ↔ e ∈ bs) : as.length = bs.length := by
  induction as generalizing bs with
  | nil =>
    suffices bs = [] by rw [this]
    rw [List.eq_nil_iff_forall_not_mem]; grind
  | cons a as ih =>
    suffices bs.length = (bs.erase a).length + 1 by grind
    grind

/-- If a list is duplicate free and the sublist of another list, then the second list is at least as long as the first. -/
theorem length_le_of_nodup_of_subset [DecidableEq α] (as bs : List α) (nodup : as.Nodup) (subset : as ⊆ bs) : as.length ≤ bs.length := by
  induction as generalizing bs with
  | nil => simp
  | cons a as ih =>
    let bs_without_a := bs.erase a
    simp only [nodup_cons] at nodup
    specialize ih
      bs_without_a
      nodup.right
      (by intro c c_mem; rw [List.mem_erase_of_ne]; apply subset; simp [c_mem]; intro contra; rw [contra] at c_mem; apply nodup.left; exact c_mem)
    rw [List.length_erase_of_mem (by apply subset; simp)] at ih
    rw [Nat.le_sub_one_iff_lt (by apply List.length_pos_of_mem; exact subset List.mem_cons_self)] at ih
    apply Nat.succ_le_of_lt
    exact ih

/-- If a list is duplicate free and the sublist of another list that has the same length, then both lists have exactly the same elements. -/
theorem equiv_of_nodup_of_length_eq_of_subset [DecidableEq α]
    (as bs : List α) (nodup : as.Nodup) (eq_length : as.length = bs.length) (subset : as ⊆ bs) : ∀ e, e ∈ as ↔ e ∈ bs := by
  intro e
  constructor
  . apply subset
  . intro mem_bs
    induction as generalizing bs e with
    | nil => cases bs; simp at mem_bs; simp at eq_length
    | cons a as ih =>
      let bs_without_a := bs.erase a
      simp only [nodup_cons] at nodup
      specialize ih
        bs_without_a
        nodup.right
        (by rw [List.length_erase_of_mem, ← eq_length]; simp; exact subset List.mem_cons_self)
        (by intro c c_mem; rw [List.mem_erase_of_ne]; apply subset; simp [c_mem]; intro contra; rw [contra] at c_mem; apply nodup.left; exact c_mem)
      cases Decidable.em (e = a) with
      | inl eq => simp [eq]
      | inr neq =>
        simp only [mem_cons]; apply Or.inr
        apply ih
        rw [List.mem_erase_of_ne]
        exact mem_bs
        exact neq

end List

