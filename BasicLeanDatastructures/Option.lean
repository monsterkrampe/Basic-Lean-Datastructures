namespace Option

  def is_none_or : Option α -> (α -> Prop) -> Prop
    | none, _ => True
    | some a, pred => pred a

  theorem is_none_or_iff {o : Option α} {f : α -> Prop} : o.is_none_or f ↔ (∀ a, o = some a -> f a) := by
    cases o with 
    | none => simp [is_none_or]
    | some b => 
      simp only [is_none_or]
      constructor
      . intro h a eq
        injection eq with eq
        rw [← eq]
        exact h
      . intro h
        apply h
        rfl

  def is_some_and : Option α -> (α -> Prop) -> Prop
    | none, _ => False
    | some a, pred => pred a

  theorem is_some_and_iff {o : Option α} {f : α -> Prop} : o.is_some_and f ↔ ∃ a, o = some a ∧ f a := by 
    cases o with 
    | none => simp [is_some_and]
    | some b => 
      simp only [is_some_and]
      constructor
      . intro h 
        exists b
      . intro h 
        rcases h with ⟨a, eq, h⟩
        injection eq with eq
        rw [eq]
        exact h

end Option
