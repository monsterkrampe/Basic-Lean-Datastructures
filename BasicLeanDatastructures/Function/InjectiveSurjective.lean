/-
Copyright 2026 Lukas Gerlach
Released under Apache 2.0 license as described in the file LICENSE.
-/

module

import BasicLeanDatastructures.List.Basic
import BasicLeanDatastructures.List.Nodup
public import BasicLeanDatastructures.Function.Image

/-!
# Flexible Injectivity and Surjectivity

We define what it means for a function to be injective or surjective restricted to a given domain and image, given as either a list or set.
Intuitively, results involving the list versions most likely have an implicit requirement for domain and image being finite whereas results stated for the set version do not have this requirement. In this sense the set results can be seen as most general. The list and set definitions are also shown to be equivalent in cases where the domains and images can be converted between lists and sets.

We found the approach of stating domains and images explicitely more suitable than using `Function.Injective` and `Function.Surjective`
because this would require us to consider appropriate subtypes and also since
there barely seem to be theorems in the standard library (outside Mathlib).
-/

public section

namespace Function

variable {α : Type u} {β : Type v} {γ : Type w}

section SetBasedDefinitions

/-- A function is injective on a given domain set if for each two elements of the given domain, the mapping of both elements being the same implies the elements being the same. -/
@[expose]
def injectiveSet (f : α -> β) (domain : Set α) : Prop := ∀ a a', a ∈ domain -> a' ∈ domain -> f a = f a' -> a = a'

/-- A function is surjective on a given domain set and image set if for each element of the image, there exists an element in the domain that maps to the desired image element. -/
@[expose]
def surjectiveSet (f : α -> β) (domain : Set α) (image : Set β) : Prop := ∀ b, b ∈ image -> ∃ a, a ∈ domain ∧ f a = b

/-- A function over a type is closed for a given domain if the image of every domain element is mapped to an element that is again in the domain. -/
@[expose]
def closedSet (f : α -> α) (domain : Set α) : Prop := ∀ a ∈ domain, f a ∈ domain

/-- If a mapping is injective for a domain, then the same holds for any subset of the domain. -/
theorem injectiveSet_of_injectiveSet_of_subset {f : α -> β} {domain : Set α} :
    f.injectiveSet domain -> ∀ domain', domain' ⊆ domain -> f.injectiveSet domain' := by
  intro inj dom' dom'_sub a a' a_mem a'_mem
  apply inj <;> (apply dom'_sub; assumption)

/-- If a mapping is surjective for a domain and image, then the same holds for any superset of the domain. -/
theorem surjectiveSet_of_surjectiveSet_of_superset {f : α -> β} {domain : Set α} {image : Set β} :
    f.surjectiveSet domain image -> ∀ domain', domain ⊆ domain' -> f.surjectiveSet domain' image := by
  intro surj dom' dom'_sub b b_mem
  rcases surj b b_mem with ⟨a, a_mem, a_eq⟩
  exists a
  constructor
  . apply dom'_sub; exact a_mem
  . exact a_eq

/-- If the composition of two mappings is injective, then the first one must be injective. -/
theorem injectiveSet_of_injectiveSet_compose {f : α -> β} {g : β -> γ} {domain : Set α} :
    injectiveSet (g ∘ f) domain -> injectiveSet f domain := by
  intro inj a a' a_dom a'_dom image_eq
  apply inj a a' a_dom a'_dom
  simp [image_eq]

/-- If the composition of two mappings is surjective for a domain and image, then the second one must be surjective on the same image and the domain that is the image of the first function. -/
theorem surjectiveSet_of_surjectiveSet_compose {f : α -> β} {g : β -> γ} {domain : Set α} {image : Set γ} :
    surjectiveSet (g ∘ f) domain image -> surjectiveSet g (f.imageSet domain) image := by
  intro surj b b_mem
  rcases surj b b_mem with ⟨a, a_mem, a_eq⟩
  exists f a
  constructor
  . exact mapping_mem_imageSet_of_mem a_mem
  . exact a_eq

/-- Every mapping is always surjective on its own `imageSet`. -/
theorem surjective_on_own_imageSet (f : α -> β) (domain : Set α) : f.surjectiveSet domain (imageSet f domain) := by
  intro b b_mem; simp only [imageSet, Set.mem_map] at b_mem; exact b_mem

/-- If a mapping is closed, then its image is fully contained in its domain. -/
theorem imageSet_contained_of_closed
    {f : α -> α} {domain : Set α} (closed : f.closedSet domain) :
    imageSet f domain ⊆ domain := by
  intro b b_mem
  rcases surjective_on_own_imageSet f domain b b_mem with ⟨a, a_mem, a_eq⟩
  unfold closedSet at closed
  grind

/-- A mapping is surjective on a given domain and image if and only if the given image is contained in the actual image of the mapping. -/
theorem surjective_on_target_iff_all_in_imageSet {f : α -> β} {domain : Set α} {target_image : Set β} :
    f.surjectiveSet domain target_image ↔ ∀ b, b ∈ target_image -> b ∈ imageSet f domain := by
  constructor
  . intro surj b b_mem
    specialize surj b b_mem
    rcases surj with ⟨a, a_mem, a_eq⟩
    rw [← a_eq]
    apply mapping_mem_imageSet_of_mem
    exact a_mem
  . intro h b b_mem
    apply surjective_on_own_imageSet
    apply h
    exact b_mem

end SetBasedDefinitions

section ListBasedDefinitions

/-- A function is injective on a given domain list if for each two elements of the given domain, the mapping of both elements being the same implies the elements being the same. -/
@[expose]
def injectiveList (f : α -> β) (domain : List α) : Prop := ∀ a a', a ∈ domain -> a' ∈ domain -> f a = f a' -> a = a'

/-- A function is surjective on a given domain list and image list if for each element of the image, there exists an element in the domain that maps to the desired image element. -/
@[expose]
def surjectiveList (f : α -> β) (domain : List α) (image : List β) : Prop := ∀ b, b ∈ image -> ∃ a, a ∈ domain ∧ f a = b

/-- A function over a type is closed for a given domain if the image of every domain element is mapped to an element that is again in the domain. -/
@[expose]
def closedList (f : α -> α) (domain : List α) : Prop := ∀ a ∈ domain, f a ∈ domain

/-- The injectivity definitions for set and list are interchangeable. -/
theorem injective_set_list_equiv {f : α -> β} {domain_set : Set α} {domain_list : List α} (eq : ∀ e, e ∈ domain_set ↔ e ∈ domain_list) :
    f.injectiveSet domain_set ↔ f.injectiveList domain_list := by
  constructor <;> (
    intro h a a' a_mem a'_mem f_eq
    apply h <;> grind
  )

/-- The surjectivity definitions for set and list are interchangeable. -/
theorem surjective_set_list_equiv {f : α -> β}
    {domain_set : Set α} {domain_list : List α} (eq_domain : ∀ e, e ∈ domain_set ↔ e ∈ domain_list)
    {image_set : Set β} {image_list : List β} (eq_image : ∀ e, e ∈ image_set ↔ e ∈ image_list) :
    f.surjectiveSet domain_set image_set ↔ f.surjectiveList domain_list image_list := by
  constructor <;> (
    intro h b b_mem
    rcases h b (by grind) with ⟨a, a_mem, a_eq⟩
    exists a; grind
  )

/-- If a mapping is injective on a domain of the form `hd::tl`, then it is injective on `tl`. -/
theorem injectiveList_cons {f : α -> β} {hd : α} {tl : List α} : f.injectiveList (hd::tl) -> f.injectiveList tl := by
  rw [← injective_set_list_equiv (fun _ => (hd::tl).mem_toSet)]
  rw [← injective_set_list_equiv (fun _ => tl.mem_toSet)]
  intro inj
  apply injectiveSet_of_injectiveSet_of_subset inj
  intro _; grind

/-- If a mapping is surjective on a domain `tl`, then it is surjective on any domain `hd::tl`. -/
theorem surjectiveList_cons {f : α -> β} {hd : α} {tl : List α} {image : List β} : f.surjectiveList tl image -> f.surjectiveList (hd::tl) image := by
  rw [← surjective_set_list_equiv (fun _ => tl.mem_toSet) (fun _ => image.mem_toSet)]
  rw [← surjective_set_list_equiv (fun _ => (hd::tl).mem_toSet) (fun _ => image.mem_toSet)]
  intro surj
  apply surjectiveSet_of_surjectiveSet_of_superset surj
  intro _; grind

/-- Every mapping is always surjective on its own `imageList`. -/
theorem surjective_on_own_imageList [DecidableEq β] (f : α -> β) (domain : List α) : f.surjectiveList domain (imageList f domain) := by
  intro b b_mem; simp only [imageList, List.mem_eraseDupsKeepRight, List.mem_map] at b_mem; exact b_mem

/-- If a mapping is closed, then its image is fully contained in its domain. -/
theorem imageList_contained_of_closed [DecidableEq α]
    {f : α -> α} {domain : List α} (closed : f.closedList domain) :
    imageList f domain ⊆ domain := by
  intro b b_mem
  rcases surjective_on_own_imageList f domain b b_mem with ⟨a, a_mem, a_eq⟩
  unfold closedList at closed
  grind

/-- Given a mapping and a domain list without duplicates, the mapping in injective on the domain if and only if the `imageList` contains the same number of elements as the domain.  -/
theorem injectiveList_iff_length_imageList_eq_of_nodup [DecidableEq β] {f : α -> β} {domain : List α} (nodup : domain.Nodup) :
    f.injectiveList domain ↔ (imageList f domain).length = domain.length := by
  constructor
  . intro inj
    suffices domain_nodup : (domain.map f).Nodup by
      unfold imageList; simp [domain_nodup]
    induction domain with
    | nil => simp
    | cons hd tl ih =>
      rw [List.nodup_cons] at nodup
      rw [List.map_cons, List.nodup_cons]
      constructor
      . intro hd_mem_tl
        apply nodup.left
        rcases surjective_on_own_imageList f tl (f hd) (by unfold imageList; rw [List.mem_eraseDupsKeepRight]; exact hd_mem_tl) with ⟨a, a_mem, a_eq⟩
        specialize inj a hd (by simp [a_mem]) (by simp) a_eq
        rw [← inj]
        exact a_mem
      . apply ih; exact nodup.right; apply injectiveList_cons; exact inj
  . intro length_eq
    suffices (domain.map f).Nodup by
      induction domain with
      | nil => simp [injectiveList]
      | cons hd tl ih =>
        rw [List.map_cons, List.nodup_cons] at this
        intro a a' a_mem a'_mem eq
        rw [List.mem_cons] at a_mem
        rw [List.mem_cons] at a'_mem
        cases a_mem with
        | inl a_mem => grind
        | inr a_mem =>
          cases a'_mem with
          | inl a'_mem => grind
          | inr a'_mem =>
            simp only [List.nodup_cons] at nodup
            specialize ih nodup.right (by simp [imageList, this.right]) this.right
            apply ih <;> assumption
    apply List.nodup_of_length_eraseDupsKeepRight_same
    unfold imageList at length_eq
    rw [length_eq]
    simp

/-- A mapping is surjective on a given domain and image if and only if the given image is contained in the actual image of the mapping. -/
theorem surjective_on_target_iff_all_in_imageList [DecidableEq β] {f : α -> β} {domain : List α} {target_image : List β} :
    f.surjectiveList domain target_image ↔ ∀ b, b ∈ target_image -> b ∈ imageList f domain := by
  rw [← surjective_set_list_equiv (fun _ => domain.mem_toSet) (fun _ => target_image.mem_toSet)]
  rw [surjective_on_target_iff_all_in_imageSet]
  simp [imageList, imageSet]

/-- Given a single list without duplicates that represents both domain and image, if a mapping is surjective, then it is injective. -/
theorem injective_of_surjective_of_nodup [DecidableEq α] {f : α -> α} {l : List α} (nodup : l.Nodup) :
    f.surjectiveList l l -> f.injectiveList l := by
  intro surj
  rw [surjective_on_target_iff_all_in_imageList] at surj
  rw [injectiveList_iff_length_imageList_eq_of_nodup nodup]
  rw [Nat.eq_iff_le_and_ge]
  constructor
  . exact length_imageList
  . exact List.length_le_of_nodup_of_all_mem l (imageList f l) nodup surj

/-- Given a single list without duplicates that represents both domain and image, if a mapping closed on the list, then the mapping is injective if and only if it is surjective. -/
theorem injective_iff_surjective_of_nodup_of_closed [DecidableEq α] {f : α -> α} {l : List α}
    (nodup : l.Nodup) (closed : f.closedList l) : f.injectiveList l ↔ f.surjectiveList l l := by
  constructor
  . intro inj
    suffices ∀ e, e ∈ imageList f l ↔ e ∈ l by
      rw [surjective_on_target_iff_all_in_imageList]
      intro b
      apply (this b).mpr
    apply List.equiv_of_nodup_of_length_eq_of_all_mem
    . exact nodup_imageList
    . rw [injectiveList_iff_length_imageList_eq_of_nodup] at inj
      rw [inj]
      exact nodup
    . intro e e_mem
      apply imageList_contained_of_closed
      . exact closed
      . exact e_mem
  . apply injective_of_surjective_of_nodup; exact nodup

/-- Given a single list without duplicates that represents both domain and image, if a mapping both injective and surjective, then is must be closed on the list. -/
theorem closed_of_injective_of_surjective_of_nodup [DecidableEq α] {f : α -> α} {l : List α} (nodup : l.Nodup) :
    f.injectiveList l -> f.surjectiveList l l -> f.closedList l := by
  intro inj surj
  intro e e_mem
  rw [List.equiv_of_nodup_of_length_eq_of_all_mem l (imageList f l) nodup]
  . apply mapping_mem_imageList_of_mem; exact e_mem
  . rw [(injectiveList_iff_length_imageList_eq_of_nodup nodup).mp inj]
  . exact surjective_on_target_iff_all_in_imageList.mp surj

end ListBasedDefinitions

end Function

