-- Gets a fresh element of the type that does not occur in the given list
class GetFreshInhabitant (t : Type u) where
  fresh (l : List t) : { e : t // e ∉ l }

def GetFreshInhabitant.fresh_n {t : Type u} [GetFreshInhabitant t] (l : List t) (n : Nat) :
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

-- Just using Nat as an example / proof of concept here
def Nat.fresh (l : List Nat) : { n : Nat // n ∉ l} :=
  ⟨(l.max?.getD 0).succ, by
    intro contra
    have le : (l.max?.getD 0).succ ≤ l.max?.getD 0 := List.le_max?_getD_of_mem contra
    rw [Nat.succ_le] at le
    simp at le
  ⟩

instance : GetFreshInhabitant Nat where
  fresh := Nat.fresh

-- #eval GetFreshInhabitant.fresh_n [2,27,6,3] 5

