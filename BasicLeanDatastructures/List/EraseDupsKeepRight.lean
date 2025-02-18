namespace List

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

end List

