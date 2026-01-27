import BasicLeanDatastructures.List.Basic

/-!
# Finite Trees

This file defines finite trees as a nested inductive type `FiniteTree`.
The tree can have different types for the contents of its leafs and inner nodes.
-/


/-- An `InductiveTree` is either a leaf or a node that features a list of children that are again trees. -/
inductive FiniteTree (α : Type u) (β : Type v) where
| leaf : β -> FiniteTree α β
| inner : α -> List (FiniteTree α β) -> FiniteTree α β

/-- A simplified recursor for proving properties of finite trees via induction. (The default recursor generated for the nested inductive type was not very useful for me.) -/
@[elab_as_elim, induction_eliminator]
def FiniteTree.rec'
    {motive : FiniteTree α β -> Sort u}
    (leaf : (l : β) -> motive (FiniteTree.leaf l))
    (inner : (label : α) -> (ts : List (FiniteTree α β)) -> (∀ t, t ∈ ts -> motive t) -> motive (FiniteTree.inner label ts))
    (t : FiniteTree α β) :
    motive t :=
  match eq : t with
  | .leaf l => eq ▸ leaf l
  | .inner label ts => eq ▸ (inner label ts (fun t _ => rec' leaf inner t))

-- NOTE: We cannot make use of the fact that List equality is already decidable because this would require us to have DecidableEq for FiniteTree already in place. At least I do not see how we could get this in the recursive definition. Therefore this is still a mutual induction.
mutual
  def finiteTreeEq [DecidableEq α] [DecidableEq β] (a b : FiniteTree α β) : Decidable (a = b) :=
    match a with
      | .leaf la => match b with
        | .leaf lb => if eq_ls : la = lb
          then isTrue (by simp [eq_ls])
          else isFalse (by
            let unwrap := fun (x : FiniteTree α β) (hx : ∀ a b, x ≠ FiniteTree.inner a b) => match x with
              | FiniteTree.leaf lx => lx
              | FiniteTree.inner a b => absurd rfl (hx a b)
            intro contra
            have : la = lb := by
              have ha : la = unwrap (FiniteTree.leaf la) (by intro _ _ contra; simp at contra) := by rfl
              have hb : lb = unwrap (FiniteTree.leaf lb) (by intro _ _ contra; simp at contra) := by rfl
              rw [ha, hb]
              simp [contra]
            contradiction
          )
        | .inner _ _ => isFalse (by intro contra; simp at contra)
      | .inner la ca => match b with
        | .leaf lb => isFalse (by intro contra; simp at contra)
        | .inner lb cb => if eq_ls : la = lb
          then match finiteTreeListEq ca cb with
            | .isTrue p => isTrue (by simp [eq_ls, p])
            | .isFalse np => isFalse (by
            let unwrap := fun (x : FiniteTree α β) (hx : ∀ a, x ≠ FiniteTree.leaf a) => match x with
              | FiniteTree.leaf a => absurd rfl (hx a)
              | FiniteTree.inner _ b => b
            intro contra
            have : ca = cb := by
              have ha : ca = unwrap (FiniteTree.inner la ca) (by intro _ contra; simp at contra) := by rfl
              have hb : cb = unwrap (FiniteTree.inner lb cb) (by intro _ contra; simp at contra) := by rfl
              rw [ha, hb]
              simp [contra]
            contradiction
          )
          else isFalse (by
            let unwrap := fun (x : FiniteTree α β) (hx : ∀ a, x ≠ FiniteTree.leaf a) => match x with
              | FiniteTree.leaf a => absurd rfl (hx a)
              | FiniteTree.inner a _ => a
            intro contra
            have : la = lb := by
              have ha : la = unwrap (FiniteTree.inner la ca) (by intro _ contra; simp at contra) := by rfl
              have hb : lb = unwrap (FiniteTree.inner lb cb) (by intro _ contra; simp at contra) := by rfl
              rw [ha, hb]
              simp [contra]
            contradiction
          )

  def finiteTreeListEq [DecidableEq α] [DecidableEq β] (a b : List (FiniteTree α β)) : Decidable (a = b) :=
    match a with
      | .nil => match b with
        | .nil => isTrue (by rfl)
        | .cons _ _ => isFalse (by intro contra; simp at contra)
      | .cons ta la => match b with
        | .nil => isFalse (by intro contra; simp at contra)
        | .cons tb lb => match finiteTreeEq ta tb with
          | .isTrue tp => match finiteTreeListEq la lb with
            | .isTrue lp => isTrue (by simp [tp, lp])
            | .isFalse lnp => isFalse (by
              let unwrap := fun (x : List (FiniteTree α β)) (hx : x ≠ []) => match x with
                | .nil => absurd rfl hx
                | .cons _ b => b
              intro contra
              have : la = lb := by
                have ha : la = unwrap (.cons ta la) (by intro contra; simp at contra) := by rfl
                have hb : lb = unwrap (.cons tb lb) (by intro contra; simp at contra) := by rfl
                rw [ha, hb]
                simp [contra]
              contradiction
            )
          | .isFalse tnp => isFalse (by
            let unwrap := fun (x : List (FiniteTree α β)) (hx : x ≠ []) => match x with
              | .nil => absurd rfl hx
              | .cons a _ => a
            intro contra
            have : ta = tb := by
              have ha : ta = unwrap (.cons ta la) (by intro contra; simp at contra) := by rfl
              have hb : tb = unwrap (.cons tb lb) (by intro contra; simp at contra) := by rfl
              rw [ha, hb]
              simp [contra]
            contradiction
          )
end

instance [DecidableEq α] [DecidableEq β] (a b : FiniteTree α β) : Decidable (a = b) := finiteTreeEq a b


namespace FiniteTree

  /-- Returns the `depth` of the tree where a leaf is defined to have depth 1. -/
  def depth : FiniteTree α β -> Nat
  | FiniteTree.leaf _ => 1
  | FiniteTree.inner _ ts => 1 + (ts.map depth).max?.getD 1

  /-- Returns all leaf nodes of the tree as a single list. (Intuitively you simply read all leaves from left to right). -/
  def leaves : FiniteTree α β -> List β
  | FiniteTree.leaf b => List.cons b List.nil
  | FiniteTree.inner _ ts => ts.flatMap leaves

  /-- Returns all nodes that are not leaves as a single list. You can imagine going branch by branch from left to right while avoiding using the same node twice. -/
  def innerLabels : FiniteTree α β -> List α
  | .leaf _ => []
  | .inner a ts => a :: ts.flatMap innerLabels

  /-- Returns the tree there we leaf nodes have been replaced according to the function `f`. -/
  def mapLeaves (f : β -> FiniteTree α γ) : FiniteTree α β -> FiniteTree α γ
  | FiniteTree.leaf b => f b
  | FiniteTree.inner a ts => FiniteTree.inner a (ts.map (mapLeaves f))

  /-- The trees resulting from two different leaf mappings are the same of applying the functions only on the list of leaves yields the same list. -/
  theorem mapLeaves_eq_of_map_leaves_eq {f : β -> FiniteTree α γ} {g : β -> FiniteTree α γ} {t : FiniteTree α β} : t.leaves.map f = t.leaves.map g -> t.mapLeaves f = t.mapLeaves g := by
    induction t with
    | leaf _ => simp [leaves, mapLeaves]
    | inner label ts ih =>
      simp only [leaves, mapLeaves]
      intro h
      rw [FiniteTree.inner.injEq]
      constructor
      . rfl
      . apply List.map_congr_left
        intro t t_mem
        apply ih
        . exact t_mem
        . rw [List.map_flatMap, List.map_flatMap] at h
          unfold List.flatMap at h
          have : ts.map (fun t => t.leaves.map f) = ts.map (fun t => t.leaves.map g) := by
            apply List.eq_iff_flatten_eq.mpr
            constructor
            . exact h
            . rw [List.map_map, List.map_map]
              apply List.map_congr_left
              intro t t_mem
              simp only [Function.comp_apply, List.length_map]
          rw [List.map_inj_left] at this
          apply this
          exact t_mem

  /-- Returns the root label of a given tree. This only works if the types for leaf and inner nodes are the same. -/
  def nodeLabel : FiniteTree α α -> α
  | FiniteTree.leaf a => a
  | FiniteTree.inner a _ => a

  /-- Check that `f` holds for each subtree of a given tree. -/
  def forEach (f : (FiniteTree α β) -> Prop) : FiniteTree α β -> Prop
  | FiniteTree.leaf c => f (.leaf c)
  | FiniteTree.inner a ts => (f (.inner a ts)) ∧ (∀ t ∈ ts, f t)

  private def privateTreesInDepth (t : FiniteTree α β) (depth : Nat) (currentDepth : Nat) : List (FiniteTree α β) :=
    if (currentDepth > depth) then [] else
      if (currentDepth = depth) then [t] else
        match t with
        | FiniteTree.leaf _ => [t]
        | FiniteTree.inner _ ts => ts.flatMap (fun t => t.privateTreesInDepth depth (currentDepth + 1))

  /-- For a given depth, returns all subtrees of the given tree `t` that have their root at this depth in `t`. -/
  def treesInDepth (t : FiniteTree α β) (depth : Nat) : List (FiniteTree α β) := t.privateTreesInDepth depth 0

  /-- A tree cannot occur as its own child. -/
  theorem tree_eq_while_contained_is_impossible [DecidableEq α] [DecidableEq β]
      (t : FiniteTree α β) (ts : List (FiniteTree α β)) (a : α) (h_eq : FiniteTree.inner a ts = t) (h_contains : t ∈ ts) : False := by
    induction t with
    | leaf _ => contradiction
    | inner label children ih =>
      apply ih (.inner label children)
      . injection h_eq with _ children_eq
        rw [children_eq] at h_contains
        exact h_contains
      . exact h_eq
      . exact h_contains

end FiniteTree

