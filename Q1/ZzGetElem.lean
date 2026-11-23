import Q1.Defs

namespace Q1

/-- Entries of the zigzag list.
Sketch: `List.getElem_append_left` / `List.getElem_append_right` with `List.getElem_map`,
`List.getElem_range`, `List.getElem_singleton`; the mapped part has length `n + 1`. -/
theorem zigzagList_getElem (n s : ℕ) (h : s < (zigzagList n).length) :
    (zigzagList n)[s] = if s ≤ n then toPt (endPt s) else toPt (midPt n) := by
  unfold zigzagList at h ⊢
  by_cases hs : s ≤ n
  · rw [if_pos hs, List.getElem_append_left (by simp; omega)]
    simp
  · rw [if_neg hs]
    have hl : s = n + 1 := by simp at h; omega
    subst hl
    rw [List.getElem_append_right (by simp)]
    simp

end Q1
