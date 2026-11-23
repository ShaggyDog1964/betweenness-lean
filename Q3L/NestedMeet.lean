/-
`nested_meet`: Lemma 44(2).
-/
import Q3L.Statement

namespace Q3L

open Classical in
/-- Lemma 44(2): `E` down-closed and `F` up-closed for labels `η` give
`w(E ∩ F) = max 0 (w E + w F - 1)`.
Sketch. Write `w(S) := ∑ i, if S i then w i else 0`. Inclusion–exclusion termwise:
`[E ∧ F] + [E ∨ F] = [E] + [F]` (`split_ifs`), so `w(E∧F) = w E + w F - w(E∨F)`.
Case `∀ i, E i ∨ F i`: `w(E∨F) = ∑ w = 1`, so `w(E∧F) = w E + w F - 1`, and it is `≥ 0`
(sum of nonnegative terms), so it equals the `max`.
Case some `i₀` has `¬ E i₀ ∧ ¬ F i₀`: then no `j` has `E j ∧ F j` (if `η i₀ ≤ η j` then `E i₀`
by `hE`; else `η j ≤ η i₀` and `F i₀` by `hF`), so `w(E∧F) = 0`; and
`w E + w F = w(E∧F) + w(E∨F) = w(E∨F) ≤ ∑ w = 1`, so the `max` is `0`. -/
theorem nested_meet {n : ℕ} (w : Fin n → ℝ) (hw0 : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1)
    (η : Fin n → ℝ) (E F : Fin n → Prop)
    (hE : ∀ i j, η j ≤ η i → E i → E j) (hF : ∀ i j, η i ≤ η j → F i → F j) :
    (∑ i, if E i ∧ F i then w i else 0) =
      max 0 ((∑ i, if E i then w i else 0) + (∑ i, if F i then w i else 0) - 1) := by
  have hsplit : (∑ i, if E i ∧ F i then w i else 0) + (∑ i, if E i ∨ F i then w i else 0) =
      (∑ i, if E i then w i else 0) + (∑ i, if F i then w i else 0) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases h1 : E i <;> by_cases h2 : F i <;> simp [h1, h2]
  have hor_le : (∑ i, if E i ∨ F i then w i else 0) ≤ 1 := by
    rw [← hw1]
    refine Finset.sum_le_sum fun i _ => ?_
    split_ifs
    · exact le_rfl
    · exact hw0 i
  have hand_nn : 0 ≤ (∑ i, if E i ∧ F i then w i else 0) := by
    refine Finset.sum_nonneg fun i _ => ?_
    split_ifs
    · exact hw0 i
    · exact le_rfl
  by_cases hcov : ∀ i, E i ∨ F i
  · have hor : (∑ i, if E i ∨ F i then w i else 0) = 1 := by
      rw [← hw1]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp [hcov i]
    rw [max_eq_right (by linarith)]
    linarith
  · obtain ⟨i₀, hi₀⟩ := not_forall.mp hcov
    have hi₀E : ¬ E i₀ := fun h => hi₀ (Or.inl h)
    have hi₀F : ¬ F i₀ := fun h => hi₀ (Or.inr h)
    have hempty : ∀ j, ¬ (E j ∧ F j) := by
      rintro j ⟨hj1, hj2⟩
      rcases le_total (η i₀) (η j) with h | h
      · exact hi₀E (hE j i₀ h hj1)
      · exact hi₀F (hF j i₀ h hj2)
    have hand : (∑ i, if E i ∧ F i then w i else 0) = 0 := by
      refine Finset.sum_eq_zero fun i _ => ?_
      simp [hempty i]
    rw [max_eq_left (by linarith), hand]

end Q3L
