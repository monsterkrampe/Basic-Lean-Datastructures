/-!
This file contains a helper function that generates all possible lists over a given list of candidates such that each of the lists has a given length.
Since the definition would hardly be useful in proofs, the accompanying theorem states the desired properties ensured by the definition.
-/

def all_lists_of_length (candidates : List α) : Nat -> List (List α)
| .zero => [[]]
| .succ n =>
  let prev_terms := all_lists_of_length candidates n
  candidates.flatMap (fun t =>
    prev_terms.map (fun ts =>
      t :: ts
    )
  )

theorem mem_all_lists_of_length (candidates : List α) (length : Nat) : ∀ as, as ∈ (all_lists_of_length candidates length) ↔ (as.length = length ∧ (∀ a, a ∈ as -> a ∈ candidates)) := by
  induction length with
  | zero => intro as; unfold all_lists_of_length; simp; intro eq a mem; rw [eq] at mem; simp at mem
  | succ length ih =>
    intro as
    unfold all_lists_of_length
    simp only [List.mem_flatMap, List.mem_map]

    constructor
    . intro h
      rcases h with ⟨a, a_mem, prev, prev_mem, as_eq⟩
      rw [← as_eq]
      specialize ih prev
      have ih := ih.mp prev_mem
      constructor
      . rw [List.length_cons, ih.left]
      . intro a' a'_mem
        rw [List.mem_cons] at a'_mem
        cases a'_mem with
        | inl a'_mem => rw [a'_mem]; apply a_mem
        | inr a'_mem => apply ih.right; exact a'_mem
    . intro h
      cases as with
      | nil => simp at h
      | cons hd tl =>
        exists hd
        constructor
        . apply h.right
          simp
        . exists tl
          constructor
          . rw [ih]
            constructor
            . have l := h.left
              rw [List.length_cons, Nat.add_right_cancel_iff] at l
              exact l
            . intro a a_mem
              apply h.right
              simp [a_mem]
          . rfl

