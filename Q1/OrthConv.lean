import Q1.Defs

namespace Q1

/-- Quadrants are orthogonally convex.
Sketch: `orth 0 = ∅` is vacuous. For `orth (m+1)`: `w.1 ∈ uIcc y.1 z.1` gives
`w.1 ≤ max y.1 z.1 ≤ bound` (`Set.mem_uIcc`), and `w.2 = y.2 ≤ bound`; VConv symmetric. -/
theorem orth_conv (t : ℕ) : HConv (orth t) ∧ VConv (orth t) := by
  cases t with
  | zero =>
    refine ⟨?_, ?_⟩ <;> intro y z w hy <;> exact absurd hy (by simp [orth])
  | succ m =>
    refine ⟨?_, ?_⟩
    · intro y z w hy hz _ hw2 hw1
      simp only [orth, Set.mem_ofPred_eq] at hy hz ⊢
      refine ⟨?_, by rw [hw2]; exact hy.2⟩
      rcases Set.mem_uIcc.mp hw1 with h | h
      · exact le_trans h.2 hz.1
      · exact le_trans h.2 hy.1
    · intro y z w hy hz _ hw1 hw2
      simp only [orth, Set.mem_ofPred_eq] at hy hz ⊢
      refine ⟨by rw [hw1]; exact hy.1, ?_⟩
      rcases Set.mem_uIcc.mp hw2 with h | h
      · exact le_trans h.2 hz.2
      · exact le_trans h.2 hy.2

end Q1
