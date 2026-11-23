import Q1.Defs

namespace Q1

/-- `p_t ∉ orth t`.
Sketch: `t = 0`: empty. `t = m + 1`: `midPt (m+1) = midPt m + halfStep (m+1)` exceeds the
bound `(midPt m).i + m` by `1` in the moving coordinate `i` (`.1` if `m+1` odd, else `.2`). -/
theorem midPt_not_mem_orth (t : ℕ) : toPt (midPt t) ∉ orth t := by
  cases t with
  | zero => simp [orth]
  | succ m =>
    rintro ⟨h1, h2⟩
    have e1 : (midPt (m + 1)).1 = (midPt m).1 + (halfStep (m + 1)).1 := rfl
    have e2 : (midPt (m + 1)).2 = (midPt m).2 + (halfStep (m + 1)).2 := rfl
    simp only [toPt] at h1 h2
    have h1' : (midPt (m + 1)).1 ≤ (midPt m).1 + (m : ℤ) := by exact_mod_cast h1
    have h2' : (midPt (m + 1)).2 ≤ (midPt m).2 + (m : ℤ) := by exact_mod_cast h2
    rw [e1] at h1'
    rw [e2] at h2'
    unfold halfStep at h1' h2'
    split_ifs at h1' h2' <;> simp at h1' h2'

end Q1
