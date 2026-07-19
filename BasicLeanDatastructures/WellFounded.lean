/-
Copyright 2026 Lukas Gerlach
Released under Apache 2.0 license as described in the file LICENSE.
-/

module

/-!
This file contains convenience theorems around `WellFoundedRelation`s.
Right now, it only features `minimal_elem_for_prop_exists` that returns the minimal element
of a `WellFoundedRelation` that fulfills a given property. This is basically the [well-ordering principle](https://en.wikipedia.org/wiki/Well-ordering_principle).
-/

/-- If a there is an element such that a certain property holds, then there is a smallest such element. -/
public theorem minimal_element_for_property_and_relation
    {α : Type u} [rel : WellFoundedRelation α] (prop : α -> Prop) (a : α) (ha : prop a) :
    (∃ a, prop a ∧ ∀ b, rel.rel b a -> ¬ prop b) := by
  induction a using WellFounded.induction rel.wf with
  | h a ih =>
    cases Classical.em (∃ b, rel.rel b a ∧ prop b) with
    | inl ex =>
      rcases ex with ⟨b, rel_b, hb⟩
      exact ih b rel_b hb
    | inr nex =>
      simp only [not_exists, not_and] at nex
      exists a

