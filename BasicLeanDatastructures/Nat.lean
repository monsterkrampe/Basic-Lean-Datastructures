theorem prop_for_nat_has_minimal_such_nat (prop : Nat -> Prop) : ∀ i, prop i -> (∃ i, prop i ∧ ∀ (j : Fin i), ¬ prop j.val) := by
  intro i h
  -- TODO: can we do this without classical? at least going through all j < i should be possible; only prop might not be decidable
  cases Classical.em (∃ (j : Fin i), prop j.val) with
  | inl ex =>
    rcases ex with ⟨j, hj⟩
    exact prop_for_nat_has_minimal_such_nat prop j.val hj
  | inr nex =>
    simp only [not_exists] at nex
    exists i

