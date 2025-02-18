def List.repeat (val : α) : Nat -> List α
| .zero => []
| .succ n => val :: List.repeat val n

theorem List.length_repeat (val : α) : ∀ n, (List.repeat val n).length = n := by
  intro n
  induction n with
  | zero => simp [List.repeat]
  | succ n ih => simp [List.repeat]; exact ih

theorem List.mem_repeat (val : α) (n : Nat) : ∀ val', val' ∈ (List.repeat val n) -> val' = val := by
  induction n with
  | zero => simp [List.repeat]
  | succ n ih => simp [List.repeat]; exact ih

theorem List.repeat_eq_iff_all_val (val : α) (n : Nat) (l : List α) : (List.repeat val n) = l ↔ (l.length = n ∧ ∀ e, e ∈ l -> e = val) := by
  induction n generalizing l with
  | zero => simp [List.repeat]; intro eq _; simp [eq]
  | succ n ih =>
    simp [List.repeat]
    constructor
    . intro h
      rw [← h]
      simp
      apply (ih (List.repeat val n)).mp
      rfl
    . intro h
      cases l with
      | nil => simp at h
      | cons hd tl =>
        rw [List.cons_eq_cons]
        constructor
        . apply Eq.symm; apply h.right; simp
        . apply (ih tl).mpr
          constructor
          . have := h.left
            simp at this
            exact this
          . intro e e_mem
            apply h.right
            simp [e_mem]

theorem List.all_eq_val_repeat [DecidableEq α] (val : α) : ∀ n, (List.repeat val n).all (fun e => e = val) = true := by
  intro n
  induction n with
  | zero => simp [List.repeat]
  | succ n ih =>
    unfold List.repeat
    rw [List.all_cons, ih]
    simp

theorem List.repeat_split : ∀ (n k l : Nat), n = k + l -> List.repeat val n = List.repeat val k ++ List.repeat val l := by
  intro n k l h
  induction k generalizing n with
  | zero => simp [h, List.repeat]
  | succ k ih =>
    conv => right; left; unfold List.repeat
    simp
    specialize ih (k+l) rfl
    rw [← ih]
    conv at h => right; rw [Nat.add_assoc, Nat.add_comm 1 l, ← Nat.add_assoc]
    cases n with
    | zero => simp at h
    | succ n =>
      conv => left; unfold List.repeat
      simp at h
      rw [h]

