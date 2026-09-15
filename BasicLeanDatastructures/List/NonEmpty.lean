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

/-- Construct a `NonEmptyList` from a single element and a `NonEmptyList`. -/
@[expose]
def cons' (a : α) (as : NonEmptyList α) : NonEmptyList α := .cons a as.toList

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

end NonEmptyList

