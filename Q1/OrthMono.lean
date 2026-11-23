import Q1.Defs

namespace Q1

private lemma halfStep_nonneg (k : ℕ) : 0 ≤ (halfStep k).1 ∧ 0 ≤ (halfStep k).2 := by
  unfold halfStep
  split_ifs <;> simp

private lemma orth_succ_subset (m : ℕ) : orth (m + 1) ⊆ orth (m + 2) := by
  intro x hx
  obtain ⟨h1, h2⟩ := hx
  obtain ⟨n1, n2⟩ := halfStep_nonneg (m + 1)
  have e1 : (midPt (m + 1)).1 = (midPt m).1 + (halfStep (m + 1)).1 := rfl
  have e2 : (midPt (m + 1)).2 = (midPt m).2 + (halfStep (m + 1)).2 := rfl
  have c1 : ((midPt m).1 : ℝ) ≤ ((midPt (m + 1)).1 : ℝ) := by
    exact_mod_cast (by omega : (midPt m).1 ≤ (midPt (m + 1)).1)
  have c2 : ((midPt m).2 : ℝ) ≤ ((midPt (m + 1)).2 : ℝ) := by
    exact_mod_cast (by omega : (midPt m).2 ≤ (midPt (m + 1)).2)
  show x.1 ≤ ((midPt (m + 1)).1 : ℝ) + ((m + 1 : ℕ) : ℝ) ∧
    x.2 ≤ ((midPt (m + 1)).2 : ℝ) + ((m + 1 : ℕ) : ℝ)
  push_cast
  constructor <;> linarith

/-- The quadrants increase.
Sketch: `orth 0 = ∅`. For `m ≤ m'`, `(midPt m).i + m ≤ (midPt m').i + m'` in each coordinate,
since the coordinates of `midPt` are nondecreasing (`halfStep` has nonnegative entries;
induction). Use `monotone_nat_of_le_succ`. -/
theorem orth_mono : Monotone orth := by
  apply monotone_nat_of_le_succ
  intro n
  cases n with
  | zero => intro x hx; exact absurd hx (by simp [orth])
  | succ m => exact orth_succ_subset m

end Q1
