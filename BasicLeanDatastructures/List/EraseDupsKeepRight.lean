module

/-!
# eraseDupsKeepRight

In this file, we define the `eraseDupsKeepRight` convenience function that removes duplicates from a given list while keeping the rightmost occurrence.
This function assumes `DecidableEq` on the list elements.
As one would expect, the resulting list is free of duplicates and still contains the same members as the original list, which
is shown in theorems below.
-/

/-- If two lists have no duplicates and have the same elements, then their length is the same. Note that the lists are not necessarily equal since the order of elements may differ. -/
theorem List.length_eq_of_nodup_of_same_elements [DecidableEq α] (l1 l2 : List α) (nodup1 : l1.Nodup) (nodup2 : l2.Nodup) (same_elems : ∀ e, e ∈ l1 ↔ e ∈ l2) : l1.length = l2.length := by
  induction l1 generalizing l2 with
  | nil =>
    have : l2 = [] := by rw [List.eq_nil_iff_forall_not_mem]; grind
    rw [this]
  | cons hd tl ih =>
    have : l2.length = (l2.erase hd).length + 1 := by grind
    grind

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

/-- The deduplicated list indeed has no duplicates. -/
@[grind <-]
theorem nodup_eraseDupsKeepRight [DecidableEq α] (l : List α) : l.eraseDupsKeepRight.Nodup := by
  fun_induction eraseDupsKeepRight <;> grind

/-- Erasing dups from a list without duplicates does not change anything. -/
@[simp, grind =]
theorem eraseDupsKeepRight_eq_self_of_nodup [DecidableEq α] (l : List α) (nodup : l.Nodup) : l.eraseDupsKeepRight = l := by
  fun_induction eraseDupsKeepRight <;> grind

/-- Calling `eraseDupsKeepRight` a second time does not change anything anymore. -/
@[simp, grind =]
theorem eraseDupsKeepRight_idempotent [DecidableEq α] (l : List α) : l.eraseDupsKeepRight.eraseDupsKeepRight = l.eraseDupsKeepRight := by grind

/-- If two lists contain the same elements, then calling `eraseDupsKeepRight` on both ends up with lists of equal length. Again the lists might not be equal as they could differ in their order of elements. -/
theorem length_eraseDupsKeepRight_eq_of_same_elements [DecidableEq α] (l1 l2 : List α) :
    (∀ e, e ∈ l1 ↔ e ∈ l2) -> l1.eraseDupsKeepRight.length = l2.eraseDupsKeepRight.length := by
  intros; apply length_eq_of_nodup_of_same_elements <;> grind

end List

