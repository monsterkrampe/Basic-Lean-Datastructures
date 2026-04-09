/-
Copyright 2026 Lukas Gerlach
Released under Apache 2.0 license as described in the file LICENSE.
-/

module

public import BasicLeanDatastructures.Set.Basic

/-!
This file contains a collection definitions and theorems about lists that are not part of Lean's standard library.
At least when initially writing some of these, suitable variants did not exist or I simply did not find them.

Some cleanup is certainly needed here.
-/

def List.decidableEqNil : (l : List α) -> Decidable (l = [])
| .nil => .isTrue rfl
| .cons hd tl => .isFalse (by simp)

instance (l : List α) : Decidable (l = []) := l.decidableEqNil

public section

namespace List

/-- We can convert a list to a set by defining membership in the set through membership in the list. -/
def toSet (l : List α) : Set α := fun e => e ∈ l

/-- Membership does not change across the `toSet` conversion. -/
@[simp, grind =]
theorem mem_toSet {l : List α} {e : α} : e ∈ l.toSet ↔ e ∈ l := by
  simp [toSet, Membership.mem]

/-- For each valid index, the list element at that index is also in `toSet`. -/
theorem getElem_mem_toSet (l : List α) (i : Fin l.length) : l[i] ∈ l.toSet := by rw [mem_toSet]; apply List.getElem_mem

/-- Converting a list to a set and then applying a function to each element is the same as first applyign the function and then converting to the set. -/
@[simp, grind =]
theorem map_toSet_eq_toSet_map {l : List α} {f : α -> β} : l.toSet.map f = (l.map f).toSet := by
  ext; simp

/-- For each element of `l.toSet`, the mapped version of that element is in the set obtained from the mapped list. -/
theorem mem_toSet_map_of_mem_toSet {l : List α} {e : α} {f : α -> β} : e ∈ l.toSet -> f e ∈ (l.map f).toSet := by
  intro mem
  rw [← map_toSet_eq_toSet_map]
  apply Set.mem_map_of_mem
  exact mem

/-- The sum of taking any number of elements from a list cannot exceed the sum over the whole list. -/
theorem sum_take_le_sum (l : List Nat) (i : Fin (l.length + 1)) : (l.take i.val).sum ≤ l.sum := by
  induction l with
  | nil => simp
  | cons hd tl ih =>
    cases i using Fin.cases with
    | zero => simp
    | succ i =>
      rw [List.take_cons (by simp), List.sum_cons, List.sum_cons]
      apply Nat.add_le_add_left
      apply ih ⟨i.val, i.isLt⟩

/-- This function is essentially `List.zipIdx` but the indices are associated with a proof that they are indeed smaller than the length of the list, represented as `Fin`. -/
def zipIdx_with_lt (l : List α) : List (α × (Fin l.length)) :=
  l.zipIdx.attach.map (fun ⟨pair, h⟩ => (pair.fst, ⟨pair.snd, List.snd_lt_of_mem_zipIdx h⟩))

/-- The length of `zipIdx_with_lt` is the original length. -/
@[simp, grind =]
theorem length_zipIdx_with_lt (l : List α) : l.zipIdx_with_lt.length = l.length := by simp [zipIdx_with_lt]

/-- The first part of a pair at a given index in `zipIdx_with_lt` corresponds to the list element at the same index. -/
@[simp, grind =]
theorem zipIdx_with_lt_getElem_fst_eq_getElem {l : List α} {index : Nat} (h : index < l.length) : (l.zipIdx_with_lt[index]'(by rw [length_zipIdx_with_lt]; exact h)).fst = l[index] := by simp [zipIdx_with_lt]

/-- The second part of a pair at a given index in `zipIdx_with_lt` is exactly this index (represented as `Fin`). -/
@[simp, grind =]
theorem zipIdx_with_lt_getElem_snd_eq_index {l : List α} {index : Nat} (h : index < l.length) : (l.zipIdx_with_lt[index]'(by rw [length_zipIdx_with_lt]; exact h)).snd = ⟨index, h⟩ := by simp [zipIdx_with_lt]

/-- Membership in `zipIdx_with_lt` is equivalent to membership in `List.zipIdx`. -/
@[simp, grind =]
theorem mem_zipIdx_with_lt_iff_mem_zipIdx {l : List α} : ∀ (i : Fin l.length) (el : α), (el, i) ∈ l.zipIdx_with_lt ↔ (el, i.val) ∈ l.zipIdx := by
  intro i el
  unfold zipIdx_with_lt
  simp
  constructor
  . intro h
    cases h with | intro ival h =>
      cases h with | intro h eq =>
        rw [← eq]
        exact h
  . intro h; exists i.val; exists h

/-- A pair of an element `el` and an index `i` is in `zipIdx_with_lt` if and only if `el` is at index `i` in the underlying list. -/
theorem mk_mem_zipIdx_with_lt_iff_getElem {l : List α} : ∀ (i : Fin l.length) (el : α), (el, i) ∈ l.zipIdx_with_lt ↔ l[i.val] = el := by
  simp [List.mk_mem_zipIdx_iff_getElem?]

/-- Converts any with a negated predicate into a negated call to all with a positive predicate. -/
theorem neg_all_of_any_neg (l : List α) (p : α -> Bool) : l.any (fun a => ¬p a) -> ¬l.all p := by simp

/-- Components of two append calls are equal if the appended lists are equal and the first components have the same length. -/
theorem append_args_eq_of_append_eq_of_same_length {as bs cs ds : List α} (h : as.length = cs.length) : as ++ bs = cs ++ ds -> as = cs ∧ bs = ds := by
  induction as generalizing cs with
  | nil => cases cs with | nil => simp | cons _ _ => contradiction
  | cons a as ih =>
    cases cs with
    | nil => contradiction
    | cons c cs => grind

/-- Two lists resulting from append calls are equal if the individual components are equal. -/
theorem append_eq_append_of_parts_eq (as bs cs ds : List α) : as = cs -> bs = ds -> as ++ bs = cs ++ ds := by grind

/-- If two lists resulting from append calls are equal and the second components have the same length, then the first components also have the same length. -/
theorem append_left_same_length_of_append_eq_append_of_right_same_length {as bs cs ds : List α} : as ++ bs = cs ++ ds -> bs.length = ds.length -> as.length = cs.length := by
  induction as generalizing cs <;> cases cs <;> grind

/-- A non-empty list can be split into its head and tail. -/
theorem head_cons_tail_of_ne_nil {l : List α} (h : l ≠ []) : l = (l.head h) :: l.tail := by simp

/-- An element is in a list if and only if the list is composable such the element has its first occurrence in this composition. -/
theorem mem_iff_append_and_not_in_first [DecidableEq α] (l : List α) (e : α) : e ∈ l ↔ ∃ as bs, l = as ++ (e :: bs) ∧ ¬ e ∈ as := by
  induction l with
  | nil => simp
  | cons hd tl ih =>
    constructor
    . intro h
      cases Decidable.em (e = hd) with
      | inl eq => exists []; simp [eq]
      | inr neq => grind
    . grind

/-- Mapping over list produces the same list if the mapping function maps each list member to itself. Note that this is very close to `List.map_id''`
  but that `List.map_id''` has a stronger assumption. Namely it requires the function to be the id not only on list elements but on every representant of the element type. -/
theorem map_id_of_id_on_all_mem (l : List α) (f : α -> α) (id_on_all_mem : ∀ e, e ∈ l -> f e = e) : l.map f = l := by
  induction l <;> grind

/-- Filtering a list based on two predicates yields the same list if the predicates behave the same on all elements. -/
theorem filter_eq_of_all_eq (l : List α) (p q : α -> Bool) : (∀ e, e ∈ l -> p e = q e) -> l.filter p = l.filter q := by
  induction l <;> grind

/-- Lists over subtypes are equal if and only if their unattached versions are equal. -/
@[simp, grind =]
theorem eq_iff_unattach_eq {α : Type u} {p : α -> Prop} {as bs : List {x : α // p x}} : as.unattach = bs.unattach ↔ as = bs := by
  constructor
  . intro h
    apply List.ext_getElem
    . have : as.unattach.length = bs.unattach.length := by rw [h]
      simp only [List.length_unattach] at this
      exact this
    . rw [List.ext_getElem?_iff] at h
      intro n le le'
      specialize h n
      unfold List.unattach at h
      rw [List.getElem?_map] at h
      rw [List.getElem?_map] at h
      rw [List.getElem?_eq_getElem le] at h
      rw [List.getElem?_eq_getElem le'] at h
      simp at h
      apply Subtype.ext
      exact h
  . grind

/-- A list that is longer than a list without duplicates but only contains the same elements must have a duplicate. -/
theorem contains_dup_of_exceeding_nodup_list_with_same_elements
    [DecidableEq α]
    (as bs : List α)
    (nodup_as : as.Nodup)
    (len_lt : as.length < bs.length)
    (contains_all : bs ⊆ as) :
    ¬ bs.Nodup := by
  induction bs generalizing as with
  | nil => simp at len_lt
  | cons hd tl ih =>
    rw [List.nodup_cons]
    intro contra
    cases Decidable.em (hd ∈ tl) with
    | inl mem => apply contra.left; exact mem
    | inr mem => apply ih (as.erase hd) <;> grind

/-- For two equal lists, filter does the same. -/
theorem filter_eq_of_eq {as bs : List α} : as = bs -> ∀ (f : α -> Bool), as.filter f = bs.filter f := by grind

/-- For two equal lists, map does the same. -/
theorem map_eq_of_eq {as bs : List α} : as = bs -> ∀ (f : α -> β), as.map f = bs.map f := by grind

/-- For two equal lists, flatten does the same. -/
theorem flatten_eq_of_eq {as bs : List (List α)} : as = bs -> as.flatten = bs.flatten := by grind

/-- Elements at equal indices are the same. -/
theorem getElem_eq_getElem_of_idx_eq {l : List α} {i j : Nat} {i_lt : i < l.length} (idx_eq : i = j) : l[i] = l[j] := by grind

/-- We getting the element at the index of a given element `e`, we obtain exactly `e`. Note that this depends on `LawfulBEq`. -/
theorem getElem_idxOf_of_mem [BEq α] [LawfulBEq α] {l : List α} {e : α} (mem : e ∈ l) : l[l.idxOf e]'(by apply List.idxOf_lt_length_of_mem; exact mem) = e := by
  induction l <;> grind

/-- The index of an element that we get from given index is exactly this index. Note that this uses `DecidableEq`. -/
@[grind <-]
theorem idxOf_getElem [DecidableEq α] {l : List α} {i : Nat} {lt : i < l.length} (nodup : l.Nodup) : l.idxOf l[i] = i := by
  induction l generalizing i <;> grind

end List

