import BasicLeanDatastructures.Set.Basic
import BasicLeanDatastructures.Option

namespace List
  def toSet : List α -> Set α
  | .nil => ∅
  | .cons h tail => (fun e => e = h) ∪ (List.toSet tail)

  theorem mem_toSet {l : List α} {e : α} : e ∈ l.toSet ↔ e ∈ l := by
    induction l with
    | nil => constructor <;> (intros; contradiction)
    | cons a as ih =>
      constructor
      . intro h_in; simp; cases h_in with
        | inl h_in_head => left; unfold Set.element at h_in_head; rw [h_in_head]
        | inr h_in_tail => right; rw [← ih]; exact h_in_tail
      . intro h_in; simp at h_in; cases h_in with
        | inl h_in_head => left; unfold Set.element; rw [h_in_head]
        | inr h_in_tail => right; rw [ih]; exact h_in_tail

  theorem get_mem_toSet (l : List α) (i : Fin l.length) : l[i] ∈ l.toSet := by rw [mem_toSet]; simp

  theorem mem_toSet_map_of_mem_toSet {l : List α} {e : α} {f : α -> β} : e ∈ l.toSet -> f e ∈ (l.map f).toSet := by
    intro h
    rw [mem_toSet] at h
    rw [mem_toSet]
    rw [List.mem_map]
    exists e

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

  def idx_of_with_count [DecidableEq α] {l : List α} {e : α} (e_in_l : e ∈ l) (c : Nat) : Fin (c + l.length) :=
    match l with
    | .nil => by contradiction
    | .cons h tail => if eq : e == h then ⟨c, by simp⟩ else
      let res := tail.idx_of_with_count (by cases e_in_l; simp at eq; assumption) (c + 1)
      ⟨res.val, by simp [length]; rw [@Nat.add_comm tail.length 1, ← Nat.add_assoc]; exact res.isLt⟩

  theorem idx_of_with_count_succ [DecidableEq α] {l : List α} {e : α} (e_in_l : e ∈ l) (c : Nat) : (idx_of_with_count e_in_l (c + 1)).val = (idx_of_with_count e_in_l c).val + 1 := by
    induction l generalizing c with
    | nil => contradiction
    | cons b bs ih =>
      unfold idx_of_with_count
      by_cases e == b
      case pos hl => simp [hl]
      case neg hr => simp [hr]; apply ih

  def idx_of [DecidableEq α] {l : List α} {e : α} (e_in_l : e ∈ l) : Fin l.length :=
    let tmp_fin := l.idx_of_with_count e_in_l 0
    have tmp_fin_isLt := tmp_fin.isLt
    ⟨tmp_fin.val, by simp at tmp_fin_isLt; exact tmp_fin_isLt⟩

  theorem get_prepend_succ [DecidableEq α] (l : List α) (a : α) (i : Fin l.length) (j : Fin (a::l).length) (h : j = Fin.succ i) : l.get i = (a::l).get j := by rw [h]; simp [get]

  theorem idx_of_prepend_succ [DecidableEq α] {l : List α} {e a : α} (e_in_l : e ∈ l) (h : e ≠ a) : ((a::l).idx_of (by right; trivial)) = Fin.succ (l.idx_of e_in_l) := by
    simp [idx_of, idx_of_with_count, h, Fin.succ]
    apply idx_of_with_count_succ

  theorem idx_of_get [DecidableEq α] {l : List α} {e : α} (e_in_l : e ∈ l) (isLt : (l.idx_of e_in_l < l.length)) : e = l.get ⟨(l.idx_of e_in_l).val, isLt⟩ := by
    induction l with
    | nil => contradiction
    | cons a as ih =>
      by_cases h : e = a
      . simp [get, h, idx_of, idx_of_with_count]
      . have e_in_as : e ∈ as := by
          cases e_in_l
          . contradiction
          . trivial
        have isLt_as : (as.idx_of e_in_as).val < as.length := by
          exact (as.idx_of e_in_as).isLt
        have ih_plugged_in := ih e_in_as isLt_as
        apply Eq.trans
        exact ih_plugged_in
        rw [get_prepend_succ as a (as.idx_of e_in_as) ((a::as).idx_of e_in_l) (idx_of_prepend_succ e_in_as h)]

  theorem idx_of_with_count_eq_of_list_eq [DecidableEq α] {l l' : List α} (h : l = l') {e : α} (he : e ∈ l) : ∀ c, (l.idx_of_with_count he c).val = (l'.idx_of_with_count (by rw [← h]; exact he) c).val := by
    cases l with
    | nil => cases l'; simp; contradiction
    | cons head tail => cases l' with
      | nil => contradiction
      | cons head' tail' =>
        have heads_eq : head = head' := by injection h
        have tails_eq : tail = tail' := by injection h
        simp [idx_of_with_count]
        split
        case isTrue he => simp [he, heads_eq]
        case isFalse he => simp [heads_eq] at he; simp [he]; intro c; apply idx_of_with_count_eq_of_list_eq; apply tails_eq

  theorem idx_of_eq_of_list_eq [DecidableEq α] {l l' : List α} (h : l = l') {e : α} (he : e ∈ l) : (l.idx_of he).val = (l'.idx_of (by rw [← h]; exact he)).val := by
    apply idx_of_with_count_eq_of_list_eq
    apply h

  theorem idx_of_with_count_eq_under_map [DecidableEq α] [DecidableEq β] {l : List α} {e : α} (he : e ∈ l) (f : α -> β) (hf : ∀ e', e' ∈ l.toSet ∧ f e = f e' -> e = e') : ∀ c, (l.idx_of_with_count he c).val = ((l.map f).idx_of_with_count (by rw [List.mem_map]; exists e) c).val := by
    induction l with
    | nil => contradiction
    | cons head tail ih =>
      intro c
      simp [idx_of_with_count]
      split
      case isTrue he => simp [he]
      case isFalse he =>
        have : ¬ f e = f head := by
          intro hcontra;
          have : e = head := by apply hf; constructor; unfold toSet; apply Or.inl; rfl; apply hcontra
          contradiction
        simp [this]
        apply ih
        intro e' ⟨e'InTail, feEqfe'⟩
        apply hf
        constructor
        apply Or.inr
        apply e'InTail
        apply feEqfe'

  theorem idx_of_eq_under_map [DecidableEq α] [DecidableEq β] {l : List α} {e : α} (he : e ∈ l) (f : α -> β) (hf : ∀ e', e' ∈ l.toSet ∧ f e = f e' -> e = e') : (l.idx_of he).val = ((l.map f).idx_of (by rw [List.mem_map]; exists e)).val := by
    apply idx_of_with_count_eq_under_map
    apply hf

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

  theorem get_eq_of_eq {as bs : List α} (h : as = bs) (idx : Fin as.length) : as.get idx = bs.get ⟨idx.val, (by rw [← h]; exact idx.isLt)⟩ := by
    cases h; rfl

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
        apply Subtype.eq
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

end List

