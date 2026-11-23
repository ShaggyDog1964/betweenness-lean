import Conv.Locality

/-!
# Sanity checks for locality

The discrete convexity on `ℕ` (every set convex) has Carathéodory bound `1`, so
R(UCC univ) is `2`-local.
-/

namespace Conv

/-- The discrete convexity: every set is convex. -/
theorem isConvexity_univ : IsConvexity (Set.univ : Set (Set ℕ)) :=
  fun _ _ => Set.mem_univ _

/-- In the discrete convexity every point of a hull is already a point of the set, so the
Carathéodory bound is `1`. -/
example : CaraBound (Set.univ : Set (Set ℕ)) 1 := by
  intro A p hp
  have hpA : p ∈ A := hull_min (Set.mem_univ (↑A : Set ℕ)) subset_rfl hp
  exact ⟨{p}, by simpa using hpA, by simp, subset_hull _ _ (by simp)⟩

/-- The discrete convexity gives a `2`-local R(UCC univ). -/
example : IsLocal (α := ℕ) (UCC (Set.univ : Set (Set ℕ))) 2 := by
  refine (locality ℕ _ isConvexity_univ 2 le_rfl).2 fun A p hp => ?_
  have hpA : p ∈ A := hull_min (Set.mem_univ (↑A : Set ℕ)) subset_rfl hp
  exact ⟨{p}, by simpa using hpA, by simp, subset_hull _ _ (by simp)⟩

end Conv
