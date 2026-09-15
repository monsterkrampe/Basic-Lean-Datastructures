/-
Copyright 2026 Lukas Gerlach
Released under Apache 2.0 license as described in the file LICENSE.
-/

module

/-!
# Non-Empty Lists

Here, we define non-empty lists based on regular lists.
-/

public section

/-- Basically a `NonEmptyList` is a `List` without the nil constructor. -/
inductive NonEmptyList (α : Type u) where
| cons (hd : α) (tl : List α) : NonEmptyList α

namespace NonEmptyList

variable {α : Type u}

/-- We can convert a `NonEmptyList` to a regular `List` in the obvious way. -/
@[expose]
def toList : NonEmptyList α -> List α
| .cons hd tl => .cons hd tl

/-- A `List` obtained from a `NonEmptyList` is not empty as expected. -/
theorem toList_ne_nil {l : NonEmptyList α} : l.toList ≠ [] := by simp [toList]

/-- We can build a `NonEmptyList` from a regular `List` as long as we know that the list is not empty. -/
@[expose]
def from_ne_nil (l : List α) (ne_nil : l ≠ []) : NonEmptyList α := match l with
| .nil => False.elim (ne_nil rfl)
| .cons a as => .cons a as

/-- Construct a `NonEmptyList` from a single element. -/
@[expose, match_pattern]
def singleton (a : α) : NonEmptyList α := .cons a []

/-- Transforming a singleton into a list yields a singleton list. -/
@[simp, grind =]
theorem toList_singleton {a : α} : (singleton a).toList = [a] := by simp [toList]

/-- Construct a `NonEmptyList` from a single element and a `NonEmptyList`. -/
@[expose]
def cons' (a : α) (as : NonEmptyList α) : NonEmptyList α := .cons a as.toList

/-- Transforming a cons' into a list yields the expected list. -/
@[simp, grind =]
theorem toList_cons' {a : α} {as : NonEmptyList α} : (cons' a as).toList = a :: as.toList := by simp [cons', toList]

/-- Alternative cases eliminator. -/
@[elab_as_elim]
def cases
    {motive : NonEmptyList α -> Sort v}
    (l : NonEmptyList α)
    (singleton : (a : α) -> motive (.singleton a))
    (cons' : (a : α) -> (as : NonEmptyList α) -> motive (.cons' a as)) :
    motive l := match l with
  | .singleton a => singleton a
  | .cons a (a' :: as) => cons' a (.cons a' as)

/-- Alternative induction principle. -/
@[elab_as_elim]
def rec'
    {motive : NonEmptyList α -> Sort v}
    (l : NonEmptyList α)
    (singleton : (a : α) -> motive (.singleton a))
    (cons' : (a : α) -> (as : NonEmptyList α) -> (motive as) -> motive (.cons' a as)) :
    motive l := match l with
  | .singleton a => singleton a
  | .cons a (a' :: as) => cons' a (.cons a' as) (rec' (.cons a' as) singleton cons')

/-- Extract first element from `NonEmptyList`. -/
@[expose]
def head : NonEmptyList α -> α
| .cons a _ => a

/-- We can express `head` in terms of the regular list obtained through `toList`. -/
theorem head_eq {l : NonEmptyList α} : l.head = l.toList.head l.toList_ne_nil := by simp [head, toList]

/-- Extract all but the first element from `NonEmptyList`. This returns a plain `List`. -/
@[expose]
def tail : NonEmptyList α -> List α
| .cons _ as => as

/-- We can express `tail` in terms of the regular list obtained through `toList`. -/
theorem tail_eq {l : NonEmptyList α} : l.tail = l.toList.tail := by simp [tail, toList]

end NonEmptyList

