def Set (α : Type u) := α -> Prop

instance : EmptyCollection (Set α) where
  emptyCollection := fun _ => False

instance : Membership α (Set α) where
  mem S a := S a

instance : Union (Set α) where
  union A B := fun e => e ∈ A ∨ e ∈ B

instance : HasSubset (Set α) where
  Subset A B := ∀ e, e ∈ A -> e ∈ B

instance : HasSSubset (Set α) where
  SSubset A B := A ⊆ B ∧ ¬ B ⊆ A

namespace Set

  theorem ext (X Y : Set α) : (∀ e, e ∈ X ↔ e ∈ Y) -> X = Y := by
    intro h
    apply funext
    intro e
    apply propext
    specialize h e
    exact h

  theorem ext_iff (X Y : Set α) : (∀ e, e ∈ X ↔ e ∈ Y) ↔ X = Y := by
    constructor
    . apply ext
    . intro h e; rw [h]

  theorem not_empty_contains_element (X : Set α) : X ≠ ∅ -> ∃ e, e ∈ X := by
    intro neq
    apply Classical.byContradiction
    intro contra
    apply neq
    apply ext
    intro e
    simp only [not_exists] at contra
    specialize contra e
    simp only [contra, false_iff]
    simp [Membership.mem, EmptyCollection.emptyCollection]

  def map (X : Set α) (f : α -> β) : Set β := fun e => ∃ e', e' ∈ X ∧ e = f e'

  theorem element_mapping_preserves_membership (e : α) (X : Set α) (f : α -> α) : e ∈ X -> f e ∈ X.map f := by
    intro helem
    exists e

  theorem subset_refl (X : Set α) : X ⊆ X := by
    intros _ h
    exact h

  theorem subset_trans {a b c : Set α} : a ⊆ b -> b ⊆ c -> a ⊆ c := by
    intro ha hb
    intro e he
    apply hb
    apply ha
    assumption

  theorem subset_union_of_subset_left {a b c : Set α} : a ⊆ b -> a ⊆ b ∪ c := by
    intro aSubB e eInA
    apply Or.inl
    apply aSubB
    exact eInA

  theorem subset_union_of_subset_right (a b c : Set α) : a ⊆ c -> a ⊆ b ∪ c := by
    intro aSubC e eInA
    apply Or.inr
    apply aSubC
    exact eInA

  theorem union_subset_iff_both_subset (a b c : Set α) : a ∪ b ⊆ c ↔ a ⊆ c ∧ b ⊆ c := by
    constructor
    . intro h
      constructor
      . intro e hl
        apply h
        apply Or.inl
        exact hl
      . intro e hr
        apply h
        apply Or.inr
        exact hr
    . intro ⟨ha, hb⟩
      intro e
      intro h
      cases h
      . apply ha
        assumption
      . apply hb
        assumption

end Set
