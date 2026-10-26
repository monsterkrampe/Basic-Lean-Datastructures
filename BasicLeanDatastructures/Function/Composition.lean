/-
Copyright 2026 Lukas Gerlach
Released under Apache 2.0 license as described in the file LICENSE.
-/

module

namespace CustomBasicDatastructures

/-!
# Function Composition

We show come convenience results for function composition.
For now this comes down to comp_assoc, which also exists in Mathlib.
-/

public section

namespace Function

variable {α : Sort u1} {β : Sort u2} {γ : Sort u3} {δ : Sort u4}

/-- Function composition is associative. -/
theorem comp_assoc {f : α -> β} {g : β -> γ} {h : γ -> δ} : (h ∘ g) ∘ f = h ∘ g ∘ f := by apply funext; simp

end Function

