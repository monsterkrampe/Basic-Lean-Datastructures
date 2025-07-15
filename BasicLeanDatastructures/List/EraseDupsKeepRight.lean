namespace List

  theorem length_eq_of_nodup_of_same_elements [DecidableEq α] (l1 l2 : List α) (nodup1 : l1.Nodup) (nodup2 : l2.Nodup) (same_elems : ∀ e, e ∈ l1 ↔ e ∈ l2) : l1.length = l2.length := by
    induction l1 generalizing l2 with
    | nil =>
      have : l2 = [] := by rw [List.eq_nil_iff_forall_not_mem]; intro e contra; rw [← same_elems] at contra; simp at contra
      rw [this]
    | cons hd tl ih =>
      rw [List.length_cons]
      have : l2.length = (l2.erase hd).length + 1 := by
        rw [List.length_erase]
        have hd_mem_l2 : hd ∈ l2 := by
          rw [← same_elems]
          simp
        simp only [hd_mem_l2, ↓reduceIte]
        have : l2.length ≠ 0 := by
          intro contra
          rw [← List.eq_nil_iff_length_eq_zero] at contra
          rw [contra] at hd_mem_l2
          simp at hd_mem_l2
        rw [Nat.sub_one_add_one this]
      rw [this]
      rw [Nat.add_right_cancel_iff]
      apply ih
      . exact (List.nodup_cons.mp nodup1).right
      . apply List.Nodup.erase; exact nodup2
      . intro e
        rw [List.Nodup.mem_erase_iff nodup2, ← same_elems]
        constructor
        . intro e_mem
          constructor
          . intro contra; apply (List.nodup_cons.mp nodup1).left; rw [← contra]; exact e_mem
          . simp [e_mem]
        . intro ⟨neq, e_mem⟩
          rw [List.mem_cons] at e_mem
          cases e_mem; contradiction; assumption

  def eraseDupsKeepRight [DecidableEq α] : List α -> List α
  | [] => []
  | hd::tl => if hd ∈ tl then tl.eraseDupsKeepRight else hd::(tl.eraseDupsKeepRight)

  theorem mem_eraseDupsKeepRight [DecidableEq α] (l : List α) : ∀ e, e ∈ l.eraseDupsKeepRight ↔ e ∈ l := by
    induction l with
    | nil => simp [eraseDupsKeepRight]
    | cons hd tl ih =>
      unfold eraseDupsKeepRight
      intro e
      cases Decidable.em (hd ∈ tl) with
      | inl mem => simp [mem]; rw [ih]; simp; intro eq; rw [eq]; exact mem
      | inr not_mem => simp [not_mem]; rw [ih]

  theorem nodup_eraseDupsKeepRight [DecidableEq α] (l : List α) : l.eraseDupsKeepRight.Nodup := by
    induction l with
    | nil => simp [eraseDupsKeepRight]
    | cons hd tl ih =>
      simp only [eraseDupsKeepRight]
      cases Decidable.em (hd ∈ tl) with
      | inl mem => simp [mem, ih]
      | inr not_mem => simp [not_mem, ih]; rw [mem_eraseDupsKeepRight]; exact not_mem

  theorem eraseDupsKeepRight_idempotent [DecidableEq α] (l : List α) : l.eraseDupsKeepRight.eraseDupsKeepRight = l.eraseDupsKeepRight := by
    induction l with
    | nil => simp [eraseDupsKeepRight]
    | cons hd tl ih =>
      simp only [eraseDupsKeepRight]
      cases Decidable.em (hd ∈ tl) with
      | inl hd_mem =>
        simp only [hd_mem, ↓reduceIte]
        exact ih
      | inr hd_mem =>
        simp only [hd_mem, ↓reduceIte]
        simp only [eraseDupsKeepRight]
        have : hd ∉ tl.eraseDupsKeepRight := by rw [mem_eraseDupsKeepRight]; exact hd_mem
        simp only [this, ↓reduceIte]
        rw [ih]

  theorem length_eraseDupsKeepRight_eq_of_same_elements [DecidableEq α] (l1 l2 : List α) : (∀ e, e ∈ l1 ↔ e ∈ l2) -> l1.eraseDupsKeepRight.length = l2.eraseDupsKeepRight.length := by
    intro same_elems
    apply length_eq_of_nodup_of_same_elements
    . apply nodup_eraseDupsKeepRight
    . apply nodup_eraseDupsKeepRight
    . intro e; rw [mem_eraseDupsKeepRight, mem_eraseDupsKeepRight]; exact same_elems e

end List

