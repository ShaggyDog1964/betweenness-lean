import Q1.Defs

namespace Q1

/-- `p_n ≠ a_n` for `n ≥ 1`.
Sketch: `n = m + 1`; `p_n = midPt m + h`, `a_n = midPt m + 2h`, `h = halfStep (m+1)`,
whose moving entry is `m + 1 ≠ 0`. Compare that coordinate. -/
theorem midPt_ne_endPt {n : ℕ} (hn : 1 ≤ n) : toPt (midPt n) ≠ toPt (endPt n) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  intro h
  simp only [toPt, Prod.mk.injEq] at h
  obtain ⟨h1, h2⟩ := h
  have h1' : (midPt (m + 1)).1 = (endPt (m + 1)).1 := by exact_mod_cast h1
  have h2' : (midPt (m + 1)).2 = (endPt (m + 1)).2 := by exact_mod_cast h2
  have e1 : (midPt (m + 1)).1 = (midPt m).1 + (halfStep (m + 1)).1 := rfl
  have e2 : (midPt (m + 1)).2 = (midPt m).2 + (halfStep (m + 1)).2 := rfl
  have f1 : (endPt (m + 1)).1 = (midPt m).1 + 2 * (halfStep (m + 1)).1 := rfl
  have f2 : (endPt (m + 1)).2 = (midPt m).2 + 2 * (halfStep (m + 1)).2 := rfl
  rw [e1, f1] at h1'
  rw [e2, f2] at h2'
  unfold halfStep at h1' h2'
  split_ifs at h1' h2' <;> simp at h1' h2' <;> omega

end Q1
