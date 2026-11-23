import Q1.OrthConv
import Q1.OrthLtEnd
import Q1.EndCoordNe
import Q1.IsolatedUnion

namespace Q1

/-- Each set of the deletion chain is orthogonally convex.
Sketch: `isolated_union_conv` with `B = orth (min t i)` (`orth_conv`). For `s = a_j`
(`i < j ≤ t`) and `u ≠ s` in the union: if `u ∈ orth (min t i)`, then `min t i ≤ i < j`
and `orth_lt_endPt` gives `u.1 < s.1`, `u.2 < s.2`. If `u = a_{j'}` with `i < j' ≤ t`,
then `j' ≠ j` (else `u = s`) and both are `≥ 1`; apply `endPt_coord_ne` to
`min j j' < max j j'` (two cases `j < j'`, `j' < j`, using `Ne.symm`). -/
theorem critU_conv (i t : ℕ) : HConv (critU i t) ∧ VConv (critU i t) := by
  obtain ⟨hH, hV⟩ := orth_conv (min t i)
  refine isolated_union_conv hH hV ?_
  rintro s ⟨j, hij, hjt, rfl⟩ u hu hne
  rcases hu with hB | ⟨j', hij', hj't, rfl⟩
  · obtain ⟨a, b⟩ := orth_lt_endPt (show min t i < j by omega) u hB
    exact ⟨ne_of_lt a, ne_of_lt b⟩
  · have hjj : j' ≠ j := by rintro rfl; exact hne rfl
    rcases Nat.lt_or_gt_of_ne hjj with h | h
    · exact endPt_coord_ne (by omega) h
    · obtain ⟨a, b⟩ := endPt_coord_ne (by omega : 1 ≤ j) h
      exact ⟨Ne.symm a, Ne.symm b⟩

end Q1
