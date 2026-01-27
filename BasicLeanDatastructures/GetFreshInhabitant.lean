/-!
# GetFreshInhabitant

This file defines a type class `GetFreshInhabitant`
that provides a single function `GetFreshInhabitant.fresh`.
This function takes as input a list `l` over a type `t` and then returns an element
of type `t` that does itself not occur in `l`.
This captures the intuition that certain types always allow picking "fresh" representants.
For example, one would assume that it is always possibly to pick a fresh natural numbers if only finitely many numbers have been used so far.

To give an example, we also implement this typeclass for the natural numbers at the end of the file.
-/


/-- A type class that allows to get a fresh element of the desired type. That is, an element that does not occur in a given list. -/
class GetFreshInhabitant (t : Type u) where
  fresh (l : List t) : { e : t // e ∉ l }

namespace GetFreshInhabitant

  /-- If we are able to pick individual fresh elements, we can also pick a list of n fresh elements at once using this function. Of course this list shall not contain any duplicates. -/
  def fresh_n {t : Type u} [GetFreshInhabitant t] (l : List t) (n : Nat) :
      { l' : List t // l'.length = n ∧ l'.Nodup ∧ ∀ e ∈ l', e ∉ l } :=
    match n with
    | .zero => ⟨[], by simp⟩
    | .succ n =>
      let rec_res := GetFreshInhabitant.fresh_n l n
      let fresh_e := GetFreshInhabitant.fresh (rec_res.val ++ l)
      ⟨fresh_e.val :: rec_res.val, by
        constructor
        . simp [rec_res.property.left]
        constructor
        . rw [List.nodup_cons]
          constructor
          . intro contra
            apply fresh_e.property
            rw [List.mem_append]
            apply Or.inl
            exact contra
          . exact rec_res.property.right.left
        . intro e e_mem
          rw [List.mem_cons] at e_mem
          cases e_mem with
          | inr e_mem => apply rec_res.property.right.right; exact e_mem
          | inl e_mem =>
            intro contra
            apply fresh_e.property
            rw [List.mem_append]
            apply Or.inr
            rw [e_mem] at contra
            exact contra
      ⟩

end GetFreshInhabitant

namespace Nat

  /-! We give an example implementation for the natural numbers. -/

  /-- For a list of natural numbers, we can pick a fresh element by taking the successor of the maximal number from the list. -/
  def fresh (l : List Nat) : { n : Nat // n ∉ l} :=
    ⟨(l.max?.getD 0).succ, by
      intro contra
      have le : (l.max?.getD 0).succ ≤ l.max?.getD 0 := List.le_max?_getD_of_mem contra
      rw [Nat.succ_le_iff] at le
      simp at le
    ⟩

  instance : GetFreshInhabitant Nat where
    fresh := Nat.fresh

  -- #eval GetFreshInhabitant.fresh_n [2,27,6,3] 5

end Nat

