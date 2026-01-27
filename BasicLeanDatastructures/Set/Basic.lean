/-!
# Set

This file introduces a very basic `Set` type, which is merely a function from the element type into `Prop`.
-/

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

  /-- Two sets are the same if they feature the same elements. -/
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

  /-- A non-empty set contains at least one element. -/
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

  /-- Apply a mapping function to each member of a set yielding a new set; think of `List.map`. -/
  def map (X : Set α) (f : α -> β) : Set β := fun e => ∃ e', e' ∈ X ∧ e = f e'

  /-- For a set element, the mapped version of the element is in the mapped set. -/
  theorem mem_map_of_mem {e : α} {X : Set α} {f : α -> β} : e ∈ X -> f e ∈ X.map f := by
    intros
    exists e

  /-- The subset relation on sets is reflexive. -/
  theorem subset_refl {X : Set α} : X ⊆ X := by
    intros _ h
    exact h

  /-- The subset relation on sets is transitive. -/
  theorem subset_trans {a b c : Set α} : a ⊆ b -> b ⊆ c -> a ⊆ c := by
    intro ha hb
    intro e he
    apply hb
    apply ha
    assumption

  /-- When a is a subset of b, then a is still a subset of the union of b with c. -/
  theorem subset_union_of_subset_left {a b c : Set α} : a ⊆ b -> a ⊆ b ∪ c := by
    intro aSubB e eInA
    apply Or.inl
    apply aSubB
    exact eInA

  /-- When a is a subset of c, then a is still a subset of the union of b with c. -/
  theorem subset_union_of_subset_right (a b c : Set α) : a ⊆ c -> a ⊆ b ∪ c := by
    intro aSubC e eInA
    apply Or.inr
    apply aSubC
    exact eInA

  /-- The union of a and b is a subset of c if and only if a and b are both subsets of c. -/
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
