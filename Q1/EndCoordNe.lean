import Q1.EndMemOrth
import Q1.OrthLtEnd

namespace Q1

private lemma endPt_succ_coord_ne (k : ℕ) :
    (endPt (k + 1)).1 ≠ (endPt (k + 2)).1 ∧ (endPt (k + 1)).2 ≠ (endPt (k + 2)).2 := by
  have f1 : (endPt (k + 1)).1 = (midPt k).1 + 2 * (halfStep (k + 1)).1 := rfl
  have f2 : (endPt (k + 1)).2 = (midPt k).2 + 2 * (halfStep (k + 1)).2 := rfl
  have g1 : (endPt (k + 2)).1 =
      (midPt k).1 + (halfStep (k + 1)).1 + 2 * (halfStep (k + 2)).1 := rfl
  have g2 : (endPt (k + 2)).2 =
      (midPt k).2 + (halfStep (k + 1)).2 + 2 * (halfStep (k + 2)).2 := rfl
  rw [f1, f2, g1, g2]
  unfold halfStep
  rcases Nat.mod_two_eq_zero_or_one k with hm | hm
  · have h1 : (k + 1) % 2 ≠ 0 := by omega
    have h2 : (k + 2) % 2 = 0 := by omega
    simp only [h1, h2, ite_true, ite_false]
    push_cast
    constructor <;> omega
  · have h1 : (k + 1) % 2 = 0 := by omega
    have h2 : (k + 2) % 2 ≠ 0 := by omega
    simp only [h1, h2, ite_true, ite_false]
    push_cast
    constructor <;> omega

/-- Distinct endpoints with indices `≥ 1` share no coordinate.
Sketch: if `j + 2 ≤ j'`: `a_j ∈ orth (j+1)` (`endPt_mem_orth`) and `orth_lt_endPt`
(`j + 1 < j'`) gives strict inequalities in both coordinates. If `j' = j + 1`: with
`p = midPt j`, `a_j = p + halfStep j` (as `j ≥ 1`) and `a_{j+1} = p + 2 • halfStep (j+1)`.
For odd `j`: `a_j = p + (j, 0)`, `a_{j+1} = p + (0, 2(j+1))`; first coordinates differ by
`j ≥ 1`, second by `2(j+1)`. Even `j` symmetric. Casts `ℤ → ℝ` are injective. -/
theorem endPt_coord_ne {j j' : ℕ} (hj : 1 ≤ j) (h : j < j') :
    (toPt (endPt j)).1 ≠ (toPt (endPt j')).1 ∧ (toPt (endPt j)).2 ≠ (toPt (endPt j')).2 := by
  rcases Nat.lt_or_ge (j + 1) j' with h2 | h2
  · obtain ⟨a, b⟩ := orth_lt_endPt h2 _ (endPt_mem_orth (Nat.lt_succ_self j))
    exact ⟨ne_of_lt a, ne_of_lt b⟩
  · obtain rfl : j' = j + 1 := by omega
    obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
    obtain ⟨a, b⟩ := endPt_succ_coord_ne k
    simp only [toPt]
    exact ⟨fun e => a (by exact_mod_cast e), fun e => b (by exact_mod_cast e)⟩

end Q1
