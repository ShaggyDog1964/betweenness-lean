import Q1.Defs

namespace Q1

/-- Sketch: `simp [zigzagList]`. -/
theorem zigzagList_length (n : ℕ) : (zigzagList n).length = n + 2 := by
  simp [zigzagList]

end Q1
