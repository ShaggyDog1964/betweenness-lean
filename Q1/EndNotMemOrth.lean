import Q1.Defs

namespace Q1

/-- `a_t ∉ orth t`.
Sketch: `t = 0`: empty. `t = m + 1`: if `m + 1` is odd,
`(endPt (m+1)).1 = (midPt m).1 + 2(m+1) > (midPt m).1 + m`; if even, the same for `.2`. -/
theorem endPt_not_mem_orth (t : ℕ) : toPt (endPt t) ∉ orth t := by
  cases t with
  | zero => simp [orth]
  | succ m =>
    intro hmem
    simp only [orth, toPt, Set.mem_ofPred_eq] at hmem
    obtain ⟨h1, h2⟩ := hmem
    have h1' : (endPt (m + 1)).1 ≤ (midPt m).1 + (m : ℤ) := by exact_mod_cast h1
    have h2' : (endPt (m + 1)).2 ≤ (midPt m).2 + (m : ℤ) := by exact_mod_cast h2
    have e1 : (endPt (m + 1)).1 = (midPt m).1 + 2 * (halfStep (m + 1)).1 := rfl
    have e2 : (endPt (m + 1)).2 = (midPt m).2 + 2 * (halfStep (m + 1)).2 := rfl
    rw [e1] at h1'
    rw [e2] at h2'
    unfold halfStep at h1' h2'
    split_ifs at h1' h2' <;> simp at h1' h2' <;> omega

end Q1
