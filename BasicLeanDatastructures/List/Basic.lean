import BasicLeanDatastructures.Set.Basic

def List.decidableEqNil : (l : List α) -> Decidable (l = [])
| .nil => .isTrue rfl
| .cons hd tl => .isFalse (by simp)

instance (l : List α) : Decidable (l = []) := l.decidableEqNil

namespace List
  def toSet (l : List α) : Set α := fun e => e ∈ l

  theorem mem_toSet {l : List α} {e : α} : e ∈ l.toSet ↔ e ∈ l := by
    simp [toSet, Membership.mem]

  theorem getElem_mem_toSet (l : List α) (i : Fin l.length) : l[i] ∈ l.toSet := by rw [mem_toSet]; apply List.getElem_mem

  theorem map_toSet_eq_toSet_map {l : List α} {f : α -> β} : l.toSet.map f = (l.map f).toSet := by
    apply Set.ext
    intro e
    constructor
    . intro e_mem
      rcases e_mem with ⟨e', e'_mem, eq⟩
      rw [List.mem_toSet, eq]
      apply List.mem_map_of_mem
      rw [List.mem_toSet] at e'_mem
      exact e'_mem
    . intro e_mem
      rw [List.mem_toSet, List.mem_map] at e_mem
      rcases e_mem with ⟨e', e'_mem, eq⟩
      rw [← eq]
      apply Set.mem_map_of_mem
      rw [List.mem_toSet]
      exact e'_mem

  theorem mem_toSet_map_of_mem_toSet {l : List α} {e : α} {f : α -> β} : e ∈ l.toSet -> f e ∈ (l.map f).toSet := by
    intro mem
    rw [← map_toSet_eq_toSet_map]
    apply Set.mem_map_of_mem
    exact mem

  theorem sum_take_le_sum (l : List Nat) (i : Fin (l.length + 1)) : (l.take i.val).sum ≤ l.sum := by
    induction l with
    | nil => simp
    | cons hd tl ih =>
      cases i using Fin.cases with
      | zero => simp
      | succ i =>
        rw [List.take_cons (by simp), List.sum_cons, List.sum_cons]
        apply Nat.add_le_add_left
        apply ih ⟨i.val, i.isLt⟩

  def zipIdx_with_lt (l : List α) : List (α × (Fin l.length)) :=
    l.zipIdx.attach.map (fun ⟨pair, h⟩ => (pair.fst, ⟨pair.snd, List.snd_lt_of_mem_zipIdx h⟩))

  theorem length_zipIdx_with_lt (l : List α) : l.zipIdx_with_lt.length = l.length := by unfold zipIdx_with_lt; simp

  theorem zipIdx_with_lt_getElem_fst_eq_getElem {l : List α} {index : Nat} (h : index < l.length) : (l.zipIdx_with_lt[index]'(by rw [length_zipIdx_with_lt]; exact h)).fst = l[index] := by
    unfold zipIdx_with_lt
    simp

  theorem zipIdx_with_lt_getElem_snd_eq_index {l : List α} {index : Nat} (h : index < l.length) : (l.zipIdx_with_lt[index]'(by rw [length_zipIdx_with_lt]; exact h)).snd = ⟨index, h⟩ := by
    unfold zipIdx_with_lt
    simp

  theorem mem_zipIdx_with_lt_iff_mem_zipIdx {l : List α} : ∀ (i : Fin l.length) (el : α), (el, i) ∈ l.zipIdx_with_lt ↔ (el, i.val) ∈ l.zipIdx := by
    intro i el
    unfold zipIdx_with_lt
    simp
    constructor
    . intro h
      cases h with | intro ival h =>
        cases h with | intro h eq =>
          rw [← eq]
          exact h
    . intro h; exists i.val; exists h

  theorem mk_mem_zipIdx_with_lt_iff_getElem {l : List α} : ∀ (i : Fin l.length) (el : α), (el, i) ∈ l.zipIdx_with_lt ↔ l[i.val] = el := by
    intro i el
    rw [mem_zipIdx_with_lt_iff_mem_zipIdx]
    rw [List.mk_mem_zipIdx_iff_getElem?]
    simp

  theorem neg_all_of_any_neg (l : List α) (p : α -> Bool) : l.any (fun a => ¬p a) -> ¬l.all p := by simp

  theorem append_args_eq_of_append_eq_of_same_length {as bs cs ds : List α} (h : as.length = cs.length) : as ++ bs = cs ++ ds -> as = cs ∧ bs = ds := by
    induction as generalizing cs with
    | nil => cases cs with | nil => simp | cons _ _ => contradiction
    | cons a as ih =>
      cases cs with
      | nil => contradiction
      | cons c cs =>
        intro h_eq
        injection h_eq with head tail
        injection h with h
        constructor
        . rw [head]
          rw [(ih h tail).left]
        . exact (ih h tail).right

  theorem append_eq_append_of_parts_eq (as bs cs ds : List α) : as = cs -> bs = ds -> as ++ bs = cs ++ ds := by
    intro eq eq2
    rw [eq, eq2]

  theorem append_left_same_length_of_append_eq_append_of_right_same_length {as bs cs ds : List α} : as ++ bs = cs ++ ds -> bs.length = ds.length -> as.length = cs.length := by
    induction as generalizing cs with
    | nil => cases cs with | nil => simp | cons _ _ => simp only [List.nil_append]; intro eq eq2; rw [eq, Nat.eq_iff_le_and_ge] at eq2; have contra := eq2.left; simp only [List.length_append, List.length_cons] at contra; rw [Nat.add_assoc] at contra; apply False.elim; apply Nat.not_succ_le_self; rw [Nat.succ_eq_one_add]; exact Nat.le_of_add_left_le contra
    | cons a as ih =>
      cases cs with
      | nil =>
        intro eq eq2
        have : (a :: as ++ bs).length = ([] ++ ds).length := by rw [eq]
        simp only [List.nil_append, List.length_append, List.length_cons] at this
        rw [Nat.add_assoc, eq2, Nat.eq_iff_le_and_ge] at this; apply False.elim; apply Nat.not_succ_le_self; rw [Nat.succ_eq_one_add]; exact Nat.le_of_add_left_le this.left
      | cons c cs =>
        intro eq eq2
        rw [List.length_cons, @ih cs]
        . simp
        . rw [List.cons_append, List.cons_append, List.cons_eq_cons] at eq; exact eq.right
        . exact eq2

  theorem head_cons_tail_of_ne_nil {l : List α} (h : l ≠ []) : l = (l.head h) :: l.tail := by
    cases l with
    | nil => contradiction
    | cons head tail => simp

  theorem mem_iff_append_and_not_in_first [DecidableEq α] (l : List α) (e : α) : e ∈ l ↔ ∃ as bs, l = as ++ (e :: bs) ∧ ¬ e ∈ as := by
    induction l with
    | nil => simp
    | cons hd tl ih =>
      constructor
      . intro h
        cases Decidable.em (e = hd) with
        | inl eq =>
          exists []
          exists tl
          simp [eq]
        | inr neq =>
          simp [neq] at h
          rcases ih.mp h with ⟨as, bs, eq, n_mem⟩
          exists hd :: as
          exists bs
          simp [eq, neq, n_mem]
      . intro h
        rcases h with ⟨as, bs, eq, _⟩
        simp [eq]

  theorem map_id_of_id_on_all_mem (l : List α) (f : α -> α) (id_on_all_mem : ∀ e, e ∈ l -> f e = e) : l.map f = l := by
    induction l with
    | nil => simp
    | cons hd tl ih =>
      unfold map
      rw [id_on_all_mem hd]
      . rw [ih]
        intro e e_mem
        apply id_on_all_mem
        simp [e_mem]
      . simp

  theorem filter_eq_of_all_eq (l : List α) (p q : α -> Bool) : (∀ e, e ∈ l -> p e = q e) -> l.filter p = l.filter q := by
    intro h
    induction l with
    | nil => simp
    | cons hd tl ih =>
      rw [List.filter_cons]
      rw [List.filter_cons]

      have : tl.filter p = tl.filter q := by
        apply ih
        intro e e_mem
        apply h
        simp [e_mem]

      cases eq : p hd with
      | false =>
        rw [← h]
        . rw [eq]
          simp [this]
        . simp
      | true =>
        rw [← h]
        . rw [eq]
          simp [this]
        . simp

  theorem eq_iff_unattach_eq {α : Type u} {p : α -> Prop} {as bs : List {x : α // p x}} : as.unattach = bs.unattach ↔ as = bs := by
    constructor
    . intro h
      apply List.ext_getElem
      . have : as.unattach.length = bs.unattach.length := by rw [h]
        rw [List.length_unattach] at this
        rw [List.length_unattach] at this
        exact this
      . rw [List.ext_getElem?_iff] at h
        intro n le le'
        specialize h n
        unfold List.unattach at h
        rw [List.getElem?_map] at h
        rw [List.getElem?_map] at h
        rw [List.getElem?_eq_getElem le] at h
        rw [List.getElem?_eq_getElem le'] at h
        simp at h
        apply Subtype.ext
        exact h
    . intro h
      rw [h]

  theorem nodup_erase_of_nodup [DecidableEq α] (l : List α) (e : α) (nodup : l.Nodup) : (l.erase e).Nodup := by
    induction l with
    | nil => simp [List.erase]
    | cons hd tl ih =>
      rw [List.nodup_cons] at nodup
      unfold List.erase
      cases Decidable.em (hd == e) with
      | inl eq =>
        simp only [eq]
        exact nodup.right
      | inr eq =>
        simp only [eq]
        rw [List.nodup_cons]
        constructor
        . rw [List.mem_erase_of_ne]
          . exact nodup.left
          . simp at eq
            exact eq
        . exact ih nodup.right

  theorem contains_dup_of_exceeding_nodup_list_with_same_elements
      [DecidableEq α]
      (as bs : List α)
      (nodup_as : as.Nodup)
      (len_lt : as.length < bs.length)
      (contains_all : ∀ e, e ∈ bs -> e ∈ as) :
      ¬ bs.Nodup := by
    induction bs generalizing as with
    | nil => simp at len_lt
    | cons hd tl ih =>
      rw [List.nodup_cons]
      intro contra
      cases Decidable.em (hd ∈ tl) with
      | inl mem => apply contra.left; exact mem
      | inr mem =>
        apply ih (as.erase hd)
        . apply nodup_erase_of_nodup
          exact nodup_as
        . rw [List.length_erase]
          have : hd ∈ as := by apply contains_all; simp
          simp [this]
          apply Nat.lt_of_succ_lt_succ
          rw [Nat.succ_eq_add_one]
          rw [Nat.sub_one_add_one]
          . rw [List.length_cons] at len_lt
            exact len_lt
          . intro contra
            rw [List.length_eq_zero_iff] at contra
            rw [contra] at this
            simp at this
        . intro e e_mem
          rw [List.mem_erase_of_ne]
          . apply contains_all
            simp [e_mem]
          . intro contra
            rw [contra] at e_mem
            contradiction
        . exact contra.right

  theorem filter_eq_of_eq {as bs : List α} : as = bs -> ∀ (f : α -> Bool), as.filter f = bs.filter f := by intro h f; rw [h]

  theorem map_eq_of_eq {as bs : List α} : as = bs -> ∀ (f : α -> β), as.map f = bs.map f := by intro h f; rw [h]

  theorem flatten_eq_of_eq {as bs : List (List α)} : as = bs -> as.flatten = bs.flatten := by intro h; rw [h]

  theorem getElem_eq_getElem_of_idx_eq {l : List α} {i j : Nat} {i_lt : i < l.length} (idx_eq : i = j) : l[i] = l[j] := by simp [idx_eq]

  theorem getElem_idxOf_of_mem [BEq α] [LawfulBEq α] {l : List α} {e : α} (mem : e ∈ l) : l[l.idxOf e]'(by apply List.idxOf_lt_length_of_mem; exact mem) = e := by
    induction l with
    | nil => simp at mem
    | cons hd tl ih =>
      unfold List.idxOf
      simp only [List.findIdx_cons]
      cases Decidable.em (hd == e) with
      | inl eq => simp only [eq, cond_true]; rw [List.getElem_cons_zero]; apply LawfulBEq.eq_of_beq eq
      | inr neq =>
        simp only [neq, cond_false]
        rw [List.getElem_cons_succ]
        apply ih
        rw [List.mem_cons] at mem
        cases mem with
        | inl mem => rw [mem] at neq; simp at neq
        | inr mem => exact mem

  theorem idxOf_getElem [DecidableEq α] {l : List α} {i : Nat} {lt : i < l.length} (nodup : l.Nodup) : l.idxOf l[i] = i := by
    induction l generalizing i with
    | nil => simp at lt
    | cons hd tl ih =>
      rw [List.getElem_cons, List.idxOf_cons]
      cases Decidable.em (i = 0) with
      | inl i_eq => simp [i_eq]
      | inr i_eq =>
        rw [List.nodup_cons] at nodup
        simp only [i_eq, ↓reduceDIte]
        have i_lt_tl : i - 1 < tl.length := by
          apply Nat.sub_one_lt_of_le
          . apply Nat.zero_lt_of_ne_zero; exact i_eq
          . apply Nat.le_of_lt_succ; exact lt
        have : hd ≠ tl[i-1] := by
          intro contra
          apply nodup.left
          rw [contra]
          apply List.getElem_mem
        have : ¬ hd == tl[i-1] := by
          intro beq
          apply this
          apply LawfulBEq.eq_of_beq
          exact beq
        simp only [this, cond_false]
        rw [ih]
        . apply Nat.sub_one_add_one; exact i_eq
        . exact nodup.right

end List

