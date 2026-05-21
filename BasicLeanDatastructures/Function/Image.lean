/-
Copyright 2026 Lukas Gerlach
Released under Apache 2.0 license as described in the file LICENSE.
-/

module

public import BasicLeanDatastructures.List.EraseDupsKeepRight
import BasicLeanDatastructures.List.Nodup
public import BasicLeanDatastructures.Set.Basic

/-!
# Function Images

We define the image of a given function as all elements that can be reached from a given domain.
We provide a list and a set version.
-/

public section

namespace Function

variable {α : Type u} {β : Type v}

section ImageSet

/-- The image of a function for a given domain set. -/
@[expose]
def imageSet (f : α -> β) (A : Set α) : Set β := A.map f

/-- The mapping of each domain element occurs in the image. -/
theorem mapping_mem_imageSet_of_mem
    {f : α -> β} {domain : Set α} : ∀ {a}, a ∈ domain -> f a ∈ (imageSet f domain) := by
  intro a a_mem; apply Set.mem_map_of_mem; exact a_mem

end ImageSet

section ImageList

/-- The image of a function for a given domain list. -/
@[expose]
def imageList [DecidableEq β] (f : α -> β) (l : List α) : List β := (l.map f).eraseDupsKeepRight

/-- The mapping of each domain element occurs in the image. -/
theorem mapping_mem_imageList_of_mem [DecidableEq β]
    {f : α -> β} {domain : List α} : ∀ {a}, a ∈ domain -> f a ∈ (imageList f domain) := by
  intro a a_mem; apply (List.mem_eraseDupsKeepRight _ _).mpr; apply List.mem_map_of_mem; exact a_mem

/-- The `image` has no duplicates. -/
theorem nodup_imageList [DecidableEq β]
    {f : α -> β} {domain : List α} : (imageList f domain).Nodup := by
  apply List.nodup_eraseDupsKeepRight

/-- The `image` has at most as many elements as the domain. -/
theorem length_imageList [DecidableEq β]
    {f : α -> β} {domain : List α} : (imageList f domain).length ≤ domain.length := by
  suffices domain.length = (domain.map f).length by
    rw [this]
    apply List.length_le_of_nodup_of_all_mem
    . apply nodup_imageList
    . simp [imageList, List.mem_eraseDupsKeepRight]
  rw [List.length_map]

end ImageList

end Function

