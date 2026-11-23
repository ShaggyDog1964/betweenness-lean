import Q1.OrthMono

namespace Q1

/-- The deletion chain increases.
Sketch: for `t ≤ t'`, `orth (min t i) ⊆ orth (min t' i)` by `orth_mono`, and the endpoint
part grows (`j ≤ t ≤ t'`). `Set.union_subset_union`. -/
theorem critU_mono (i : ℕ) : Monotone (critU i) := by
  intro t t' h
  unfold critU
  refine Set.union_subset_union (orth_mono (min_le_min_right i h)) ?_
  rintro x ⟨j, hij, hjt, rfl⟩
  exact ⟨j, hij, le_trans hjt h, rfl⟩

end Q1
