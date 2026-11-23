import Q1.Defs

namespace Q1

private lemma hs_nonneg (k : ℕ) : 0 ≤ (halfStep k).1 ∧ 0 ≤ (halfStep k).2 := by
  unfold halfStep
  split_ifs <;> simp

private lemma midPt_mono {m n : ℕ} (h : m ≤ n) :
    (midPt m).1 ≤ (midPt n).1 ∧ (midPt m).2 ≤ (midPt n).2 := by
  induction n, h using Nat.le_induction with
  | base => exact ⟨le_refl _, le_refl _⟩
  | succ n _ ih =>
    obtain ⟨a, b⟩ := hs_nonneg (n + 1)
    have e1 : (midPt (n + 1)).1 = (midPt n).1 + (halfStep (n + 1)).1 := rfl
    have e2 : (midPt (n + 1)).2 = (midPt n).2 + (halfStep (n + 1)).2 := rfl
    constructor <;> omega

private lemma midPt_two (m : ℕ) :
    (midPt m).1 + (m + 1) ≤ (midPt (m + 2)).1 ∧ (midPt m).2 + (m + 1) ≤ (midPt (m + 2)).2 := by
  have e1 : (midPt (m + 2)).1 = (midPt m).1 + (halfStep (m + 1)).1 + (halfStep (m + 2)).1 := rfl
  have e2 : (midPt (m + 2)).2 = (midPt m).2 + (halfStep (m + 1)).2 + (halfStep (m + 2)).2 := rfl
  rw [e1, e2]
  unfold halfStep
  rcases Nat.mod_two_eq_zero_or_one m with hm | hm
  · have h1 : (m + 1) % 2 ≠ 0 := by omega
    have h2 : (m + 2) % 2 = 0 := by omega
    simp only [h1, h2, ite_true, ite_false]
    push_cast
    constructor <;> omega
  · have h1 : (m + 1) % 2 = 0 := by omega
    have h2 : (m + 2) % 2 ≠ 0 := by omega
    simp only [h1, h2, ite_true, ite_false]
    push_cast
    constructor <;> omega

/-- Later midpoints exceed the quadrant strictly in both coordinates.
Sketch: as `orth_lt_endPt`, starting from `(midPt j).i ≥ (midPt (m+2)).i` (`j ≥ m + 2`). -/
theorem orth_lt_midPt {t j : ℕ} (h : t < j) :
    ∀ u ∈ orth t, u.1 < (toPt (midPt j)).1 ∧ u.2 < (toPt (midPt j)).2 := by
  intro u hu
  cases t with
  | zero => exact absurd hu (by simp [orth])
  | succ m =>
    obtain ⟨hu1, hu2⟩ := hu
    obtain ⟨b1, b2⟩ := midPt_mono (show m + 2 ≤ j by omega)
    obtain ⟨c1, c2⟩ := midPt_two m
    have d1 : (midPt m).1 + (m : ℤ) + 1 ≤ (midPt j).1 := by omega
    have d2 : (midPt m).2 + (m : ℤ) + 1 ≤ (midPt j).2 := by omega
    have r1 : ((midPt m).1 : ℝ) + (m : ℝ) + 1 ≤ ((midPt j).1 : ℝ) := by exact_mod_cast d1
    have r2 : ((midPt m).2 : ℝ) + (m : ℝ) + 1 ≤ ((midPt j).2 : ℝ) := by exact_mod_cast d2
    simp only [toPt]
    constructor <;> linarith

end Q1
