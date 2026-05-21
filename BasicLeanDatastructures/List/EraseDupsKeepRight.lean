/-
Copyright 2026 Lukas Gerlach
Released under Apache 2.0 license as described in the file LICENSE.
-/

module

import BasicLeanDatastructures.List.Nodup

/-!
# eraseDupsKeepRight

In this file, we define the `eraseDupsKeepRight` convenience function that removes duplicates from a given list while keeping the rightmost occurrence.
This function assumes `DecidableEq` on the list elements.
As one would expect, the resulting list is free of duplicates and still contains the same members as the original list, which
is shown in theorems below.
-/

public section

namespace List

/-- Remove duplicates from a list, keeping the rightmost occurrense. -/
def eraseDupsKeepRight [DecidableEq α] : List α -> List α
| [] => []
| hd::tl => if hd ∈ tl then tl.eraseDupsKeepRight else hd::(tl.eraseDupsKeepRight)

/-- The deduplicated list contains the same elements as the original list. -/
@[simp, grind =]
theorem mem_eraseDupsKeepRight [DecidableEq α] (l : List α) : ∀ e, e ∈ l.eraseDupsKeepRight ↔ e ∈ l := by
  fun_induction eraseDupsKeepRight <;> grind

/-- eraseDupsKeepRight can only make the list shorter. -/
theorem length_eraseDupsKeepRight_le [DecidableEq α] (l : List α) : l.eraseDupsKeepRight.length ≤ l.length := by
  fun_induction eraseDupsKeepRight <;> grind

/-- The deduplicated list indeed has no duplicates. -/
@[grind <-]
theorem nodup_eraseDupsKeepRight [DecidableEq α] (l : List α) : l.eraseDupsKeepRight.Nodup := by
  fun_induction eraseDupsKeepRight <;> grind

/-- Erasing dups from a list without duplicates does not change anything. -/
@[simp, grind =]
theorem eraseDupsKeepRight_eq_self_of_nodup [DecidableEq α] (l : List α) (nodup : l.Nodup) : l.eraseDupsKeepRight = l := by
  fun_induction eraseDupsKeepRight <;> grind

/-- If the length after erasing duplicates remains the same, then the list contains no duplicates. -/
theorem nodup_of_length_eraseDupsKeepRight_same [DecidableEq α] (l : List α) (length_eq : l.eraseDupsKeepRight.length = l.length) : l.Nodup := by
  fun_induction eraseDupsKeepRight <;> grind [length_eraseDupsKeepRight_le]

/-- Calling `eraseDupsKeepRight` a second time does not change anything anymore. -/
@[simp, grind =]
theorem eraseDupsKeepRight_idempotent [DecidableEq α] (l : List α) : l.eraseDupsKeepRight.eraseDupsKeepRight = l.eraseDupsKeepRight := by grind

/-- If two lists contain the same elements, then calling `eraseDupsKeepRight` on both ends up with lists of equal length. Again the lists might not be equal as they could differ in their order of elements. -/
theorem length_eraseDupsKeepRight_eq_of_same_elements [DecidableEq α] (l1 l2 : List α) :
    (∀ e, e ∈ l1 ↔ e ∈ l2) -> l1.eraseDupsKeepRight.length = l2.eraseDupsKeepRight.length := by
  intros; apply length_eq_of_nodup_of_same_elements <;> grind

end List

