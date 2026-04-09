/-
Copyright 2026 Lukas Gerlach
Released under Apache 2.0 license as described in the file LICENSE.
-/

module

public import BasicLeanDatastructures.Set.Basic
public import BasicLeanDatastructures.List.Basic
import BasicLeanDatastructures.List.EraseDupsKeepRight

/-!
# Set.finite

This file handles a simple definition for when a set is considered finite, namely
when there exists a list that contains the same elements.
-/

public section

namespace Set

/-- A set is finite if there is a list with the same elements. We also enforce this list to be free of duplicates right now but this might change in the future. -/
@[expose]
def finite (X : Set α) : Prop := ∃ (l : List α), l.Nodup ∧ ∀ (e : α), e ∈ l ↔ e ∈ X

/-- To show that a Set is finite, it is enough to give a list with the same elements not caring about duplicates. Duplicates are removed using `List.eraseDupsKeepRight` internally. -/
theorem finite_of_list_with_same_elements [DecidableEq α] {X : Set α} (l : List α) (same_elements : ∀ e, e ∈ l ↔ e ∈ X) : X.finite := by
  exists l.eraseDupsKeepRight
  grind

/-- Subsets of finite sets are finite. -/
@[grind ->]
theorem finite_of_subset_finite [DecidableEq α] {a b : Set α} (fin : b.finite) : a ⊆ b -> a.finite := by
  intro sub
  rcases fin with ⟨l, _, l_eq⟩
  exists (l.filter (fun e =>
    have := Classical.propDecidable (e ∈ a)
    decide (e ∈ a)
  )).eraseDupsKeepRight
  grind

/-- Unions of finite sets are finite. -/
@[grind <-]
theorem union_finite_of_both_finite [DecidableEq α] {a b : Set α} (fin_a : a.finite) (fin_b : b.finite) : (a ∪ b).finite := by
  rcases fin_a with ⟨l, _, l_eq⟩
  rcases fin_b with ⟨k, _, k_eq⟩
  exists (l ++ k).eraseDupsKeepRight
  constructor
  . apply List.nodup_eraseDupsKeepRight
  . intro e
    constructor
    . grind
    . intro h; cases h <;> grind

end Set


namespace List

/-- Sets obtained from lists are finite. -/
@[grind <-]
theorem finite_toSet [DecidableEq α] (l : List α) : l.toSet.finite := by
  apply Set.finite_of_list_with_same_elements l
  simp

end List


