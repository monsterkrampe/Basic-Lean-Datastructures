/-
Copyright 2026 Lukas Gerlach
Released under Apache 2.0 license as described in the file LICENSE.
-/

module

public import BasicLeanDatastructures.Function.InjectiveSurjective

/-!
# Repetition of Functions

We define what it means to apply a function a given number of times.
This only works for function where the types of domain and image coincide.
-/

public section

namespace Function

variable {α : Type u}

/-- Repetition of a Function defined in the obvious way. Repeating zero times is defined as the id function. -/
@[expose]
def repeat_fun (f : α -> α) : Nat -> α -> α
| .zero => id
| .succ j => f ∘ (repeat_fun f j)

/-- Applying a zero-times repetition yields the original value. -/
theorem repeat_zero {f : α -> α} : ∀ {e}, f.repeat_fun 0 e = e := by simp [repeat_fun]

/-- Applying a n+1-times repetition means applying the function to the result of the n-times repetition. -/
theorem repeat_succ {f : α -> α} {i : Nat} : ∀ {e}, f.repeat_fun i.succ e = f (f.repeat_fun i e) := by simp [repeat_fun]

/-- Repeating a function once yields exactly the function. -/
@[simp, grind =]
theorem repeat_once {f : α -> α} : f.repeat_fun 1 = f := by simp [repeat_fun]

/-- It does not matter if we add another repetition on the left or the right. -/
theorem repeat_swap_one {f : α -> α} {i : Nat} : ∀ e, f (f.repeat_fun i e) = (f.repeat_fun i) (f e) := by
  fun_induction f.repeat_fun i <;> grind

/-- It does not matter if we add another repetition on the left or the right. -/
theorem repeat_swap_one' {f : α -> α} {i : Nat} : f ∘ (f.repeat_fun i) = (f.repeat_fun i) ∘ f := by
  apply funext; exact repeat_swap_one

/-- The numbers of two composed repetitions can be swapped. -/
theorem repeat_swap {f : α -> α} {i j : Nat} : ∀ e, f.repeat_fun i (f.repeat_fun j e) = f.repeat_fun j (f.repeat_fun i e) := by
  fun_induction f.repeat_fun j generalizing i with
  | case1 => simp
  | case2 j ih =>
    simp only [Function.comp_apply]
    intro e
    rw [← repeat_swap_one (f.repeat_fun j e)]
    rw [ih]

/-- The numbers of two composed repetitions can be swapped. -/
theorem repeat_swap' {f : α -> α} {i j : Nat} : f.repeat_fun i ∘ (f.repeat_fun j) = f.repeat_fun j ∘ (f.repeat_fun i) := by
  apply funext; exact repeat_swap

/-- A (i+j)-times repetition can be split into the composition of an j-times repetition followed by an i-times repetition. -/
@[simp, grind =]
theorem repeat_add {f : α -> α} {i j : Nat} : ∀ e, f.repeat_fun (i + j) e = f.repeat_fun i (f.repeat_fun j e) := by
  induction j with
  | zero => simp [repeat_fun]
  | succ j ih =>
    intro _
    conv => left; unfold repeat_fun
    conv => right; right; unfold repeat_fun
    simp [ih, f.repeat_swap_one]

/-- A (i+j)-times repetition can be split into the composition of an j-times repetition followed by an i-times repetition. -/
@[simp, grind =]
theorem repeat_add' {f : α -> α} {i j : Nat} : f.repeat_fun (i + j) = f.repeat_fun i ∘ (f.repeat_fun j) := by
  apply funext; exact repeat_add

/-- If a repetition maps a value to itself, then each multiple of the repetition must also map the value to itself. -/
theorem repeat_cycle_mul {f : α -> α} (e : α) (i : Nat) (cycle : f.repeat_fun i e = e) : ∀ j, f.repeat_fun (i * j) e = e := by
  intro j
  induction j with
  | zero => simp [repeat_fun]
  | succ j ih => rw [Nat.mul_add, repeat_add]; simp [cycle, ih]

/-- If some repetition maps a value to itself, then each other value that is part of this loop is also mapped to itself. -/
theorem repeat_move_cycle (f : α -> α) (e : α) (i : Nat) (cycle : f.repeat_fun i e = e) :
    ∀ e' j, f.repeat_fun j e = e' -> f.repeat_fun i e' = e' := by
  intro e' j e_reaches_e'
  induction j generalizing e with
  | zero => simp only [repeat_fun, id_eq] at e_reaches_e'; rw [← e_reaches_e']; exact cycle
  | succ m ih =>
    apply ih (f e)
    . rw [← f.repeat_swap_one, cycle]
    . rw [← f.repeat_swap_one]; exact e_reaches_e'

/--
Consider a list of values. If each value is reachable by some non-zero number of repetitions from some value,
then, for each value in the list, there is a non-zero number of repetitions that maps the value to itself.
Intuitively this holds by a pigeonhole argument: if for each value you need to pick a value from that you can reach it,
but only finitely many values are available, then eventually you need to complete a cycle.
-/
theorem repeat_each_reaches_self_of_each_reachable
    {f : α -> α}
    (vs : List α)
    (each_reachable : ∀ v ∈ vs, ∃ k, 1 ≤ k ∧ ∃ u ∈ vs, (f.repeat_fun k) u = v) :
    (∀ u ∈ vs, ∃ l, 1 ≤ l ∧ f.repeat_fun l u = u) := by
  induction vs with
  | nil => simp
  | cons hd tl ih =>
    specialize ih (by
      intro v v_mem
      rcases each_reachable v (by simp [v_mem]) with ⟨k, k_le, u, u_mem, u_eq⟩
      rw [List.mem_cons] at u_mem
      cases u_mem with
      | inr u_mem => exists k; constructor; exact k_le; exists u
      | inl u_mem =>
        rcases each_reachable u (by simp [u_mem]) with ⟨l, l_le, w, w_mem, w_eq⟩
        rw [List.mem_cons] at w_mem
        cases w_mem with
        | inl w_mem =>
          exists (((k / l) + 1) * l)
          constructor
          . grind
          . exists v
            constructor
            . exact v_mem
            . apply f.repeat_move_cycle u
              . rw [Nat.mul_comm]
                apply f.repeat_cycle_mul
                rw [w_mem, ← u_mem] at w_eq
                exact w_eq
              . exact u_eq
        | inr w_mem =>
          exists (k + l)
          grind)
    intro u u_mem
    rw [List.mem_cons] at u_mem
    cases u_mem with
    | inl u_mem =>
      rcases each_reachable u (by rw [u_mem]; simp) with ⟨k, k_le, v, v_mem, v_eq⟩
      rw [List.mem_cons] at v_mem
      cases v_mem with
      | inl v_mem => exists k; constructor; exact k_le; rw [v_mem, ← u_mem] at v_eq; exact v_eq
      | inr v_mem =>
        rcases ih v v_mem with ⟨l, l_le, ih⟩
        exists l
        constructor
        . exact l_le
        . apply f.repeat_move_cycle v
          . exact ih
          . exact v_eq
    | inr u_mem => exact ih _ u_mem

/--
If each value from a (finite) list is mapped to itself after some number of repetitions,
then there is a global repetition number that maps each value from the list to itself.
Basically any common multiple of the individual repetition numbers works.
-/
theorem repeat_globally_cyclic_of_each_cyclic
    {f : α -> α}
    (vs : List α)
    (each_repeats : ∀ v ∈ vs, ∃ l, 1 ≤ l ∧ f.repeat_fun l v = v) :
    ∃ l, 1 ≤ l ∧ ∀ v ∈ vs, f.repeat_fun l v = v := by
  induction vs with
  | nil => exists 1; simp
  | cons hd tl ih =>
    rcases ih (by intro v v_mem; apply each_repeats; simp [v_mem]) with ⟨l_ih, l_ih_le, ih⟩
    rcases each_repeats hd (by simp) with ⟨l_hd, l_hd_le, each_repeats⟩
    exists l_hd * l_ih
    constructor
    . apply Nat.le_trans; exact l_hd_le; apply Nat.le_mul_of_pos_right; apply Nat.lt_of_succ_le; exact l_ih_le
    . intro v v_mem
      simp only [List.mem_cons] at v_mem
      cases v_mem with
      | inl v_mem => rw [v_mem, f.repeat_cycle_mul]; exact each_repeats
      | inr v_mem => specialize ih v v_mem; rw [Nat.mul_comm, f.repeat_cycle_mul]; exact ih

/--
If a mapping is surjective for a given list of values,
then there exists a repetition count $k$ such that repeating $k+1$ times maps each value from the list to itself.
Note that we use $k+1$ repetitions as otherwise the result would be trivial for zero repetitions, which correspond to the id function by definition.
-/
theorem exists_repetition_that_is_inverse_of_surj
    {f : α -> α}
    (vs : List α)
    (surj : f.surjectiveList vs vs) :
    ∃ k, ∀ v ∈ vs, f.repeat_fun k (f v) = v := by
  suffices ∃ k, 1 ≤ k ∧ ∀ v ∈ vs, f.repeat_fun k v = v by
    rcases this with ⟨k, le, repeats_globally⟩
    exists k-1
    intro v v_mem
    suffices f.repeat_fun ((k-1)+1) v = v by rw [repeat_add, repeat_once] at this; exact this
    grind
  apply f.repeat_globally_cyclic_of_each_cyclic
  apply f.repeat_each_reaches_self_of_each_reachable
  intro v v_mem
  exists 1
  constructor
  . simp
  . rw [repeat_once]; apply surj v v_mem

end Function


