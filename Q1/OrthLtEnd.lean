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

private lemma endPt_ge_midPt (k : ℕ) :
    (midPt (k + 1)).1 ≤ (endPt (k + 1)).1 ∧ (midPt (k + 1)).2 ≤ (endPt (k + 1)).2 := by
  obtain ⟨a, b⟩ := hs_nonneg (k + 1)
  have e1 : (midPt (k + 1)).1 = (midPt k).1 + (halfStep (k + 1)).1 := rfl
  have e2 : (midPt (k + 1)).2 = (midPt k).2 + (halfStep (k + 1)).2 := rfl
  have f1 : (endPt (k + 1)).1 = (midPt k).1 + 2 * (halfStep (k + 1)).1 := rfl
  have f2 : (endPt (k + 1)).2 = (midPt k).2 + 2 * (halfStep (k + 1)).2 := rfl
  constructor <;> omega

/-- Later endpoints exceed the quadrant strictly in BOTH coordinates.
Sketch: `t = 0` vacuous. `t = m + 1 < j`, so `j ≥ m + 2`. In each coordinate `i`:
`(endPt j).i ≥ (midPt j).i ≥ (midPt (m+2)).i ≥ (midPt m).i + (m+1) > (midPt m).i + m ≥ u.i`.
First: `endPt j = midPt j + halfStep j` for `j ≥ 1`, entries `≥ 0`. Second: `midPt`
coordinates are nondecreasing. Third: `halfStep (m+1) + halfStep (m+2)` has entries
`≥ m + 1` in both coordinates, since exactly one of `m+1`, `m+2` is odd. -/
theorem orth_lt_endPt {t j : ℕ} (h : t < j) :
    ∀ u ∈ orth t, u.1 < (toPt (endPt j)).1 ∧ u.2 < (toPt (endPt j)).2 := by
  intro u hu
  cases t with
  | zero => exact absurd hu (by simp [orth])
  | succ m =>
    obtain ⟨hu1, hu2⟩ := hu
    obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
    obtain ⟨a1, a2⟩ := endPt_ge_midPt k
    obtain ⟨b1, b2⟩ := midPt_mono (show m + 2 ≤ k + 1 by omega)
    obtain ⟨c1, c2⟩ := midPt_two m
    have d1 : (midPt m).1 + (m : ℤ) + 1 ≤ (endPt (k + 1)).1 := by omega
    have d2 : (midPt m).2 + (m : ℤ) + 1 ≤ (endPt (k + 1)).2 := by omega
    have r1 : ((midPt m).1 : ℝ) + (m : ℝ) + 1 ≤ ((endPt (k + 1)).1 : ℝ) := by exact_mod_cast d1
    have r2 : ((midPt m).2 : ℝ) + (m : ℝ) + 1 ≤ ((endPt (k + 1)).2 : ℝ) := by exact_mod_cast d2
    simp only [toPt]
    constructor <;> linarith

end Q1
