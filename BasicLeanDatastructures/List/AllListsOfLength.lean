module

/-!
This file contains a helper function that generates all possible lists over a given list of candidates such that each of the lists has a given length.
Since the definition would hardly be useful in proofs, the accompanying theorem states the desired properties ensured by the definition.
-/

public section

def all_lists_of_length (candidates : List α) : Nat -> List (List α)
| .zero => [[]]
| .succ n =>
  let prev_terms := all_lists_of_length candidates n
  candidates.flatMap (fun t =>
    prev_terms.map (fun ts =>
      t :: ts
    )
  )

@[simp, grind =]
theorem mem_all_lists_of_length (candidates : List α) (length : Nat) : ∀ as, as ∈ (all_lists_of_length candidates length) ↔ (as.length = length ∧ (∀ a, a ∈ as -> a ∈ candidates)) := by
  fun_induction all_lists_of_length
  . simp
  . intro as
    constructor
    . grind
    . cases as
      . simp
      . simp; grind

