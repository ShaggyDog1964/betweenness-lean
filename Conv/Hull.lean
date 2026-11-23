import Conv.Statement

/-!
# Hull basics

Elementary facts about `hull C`: it lies in `C`, contains its argument, is the least member
of `C` above it, is monotone and idempotent, and absorbs points already in the hull.
-/

namespace Conv

universe u

variable {α : Type u} {C : Set (Set α)} {S T U : Set α}

/-- `Set.univ` is convex: the intersection of the empty subfamily. -/
theorem univ_mem (hC : IsConvexity C) : Set.univ ∈ C := by
  simpa using hC ∅ (Set.empty_subset _)

/-- The hull is convex: it is the intersection of a subfamily of `C`. -/
theorem hull_mem (hC : IsConvexity C) (S : Set α) : hull C S ∈ C :=
  hC _ fun _ hU => hU.1

/-- Every set lies in its hull. -/
theorem subset_hull (C : Set (Set α)) (S : Set α) : S ⊆ hull C S :=
  Set.subset_sInter fun _ hU => hU.2

/-- The hull lies in every convex set containing the set. -/
theorem hull_min (hU : U ∈ C) (h : S ⊆ U) : hull C S ⊆ U :=
  Set.sInter_subset_of_mem ⟨hU, h⟩

/-- The hull is monotone. -/
theorem hull_mono (h : S ⊆ T) : hull C S ⊆ hull C T :=
  Set.subset_sInter fun _ hU => Set.sInter_subset_of_mem ⟨hU.1, h.trans hU.2⟩

/-- A convex set is its own hull. -/
theorem hull_eq_self (_hC : IsConvexity C) (hU : U ∈ C) : hull C U = U :=
  (hull_min hU subset_rfl).antisymm (subset_hull C U)

/-- The hull is idempotent. -/
theorem hull_hull (hC : IsConvexity C) : hull C (hull C S) = hull C S :=
  hull_eq_self hC (hull_mem hC S)

/-- Adding a point already in the hull does not change the hull. -/
theorem mem_hull_insert_iff_absorb (hC : IsConvexity C) {a : α} (ha : a ∈ hull C S) :
    hull C (insert a S) = hull C S :=
  (hull_min (hull_mem hC S) (Set.insert_subset ha (subset_hull C S))).antisymm
    (hull_mono (Set.subset_insert a S))

end Conv
