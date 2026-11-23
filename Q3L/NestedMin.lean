/-
`nested_min_down`: Lemma 44(1), down-closed case.
-/
import Q3L.Statement

namespace Q3L

open K4 (Lot)

open Classical in
/-- Lemma 44(1), down-closed version: if each set `{i | P c i}` (`c ∈ S`) is
down-closed for the labels `η`, the weight of their intersection is the minimum of their
weights (empty intersection = everything, empty minimum = `1`).
Sketch. Write `m(c) := ∑ i, if P c i then w i else 0`. If `S = ∅`: both sides are `1`
(`hw1`; `minOr1` of `∅` is `1`). Otherwise the sets are totally ordered by inclusion: for
`c, c' ∈ S`, either `∀ i, P c i → P c' i` or `∀ i, P c' i → P c i` (if `i` has
`P c i ∧ ¬ P c' i` and `j` has `P c' j ∧ ¬ P c j`, then `η j ≤ η i` gives `P c j` and
`η i < η j` gives `P c' i`, both impossible). Inclusion makes `m` monotone
(`Finset.sum_le_sum`, `hw0`).
Prove, for nonempty `S`, the statement `∃ c₀ ∈ S, (∀ i, (∀ c ∈ S, P c i) ↔ P c₀ i) ∧
∀ c ∈ S, m c₀ ≤ m c` by `Finset.Nonempty.cons_induction` (or `Finset.induction_on`): for a
singleton take `c₀ = c`; when inserting `c` into `S` with witness `c₀`, compare `{P c}` and
`{P c₀}` by nestedness and keep the smaller one. Then the left side is `m c₀`, and
`minOr1 S m = S.inf' _ m = m c₀` (`dif_pos`, `Finset.inf'_le`, `Finset.le_inf'`,
`le_antisymm`). -/
theorem nested_min_down {K n : ℕ} (w : Fin n → ℝ) (hw0 : ∀ i, 0 ≤ w i)
    (hw1 : ∑ i, w i = 1) (η : Fin n → ℝ) (S : Finset (Lot K)) (P : Lot K → Fin n → Prop)
    (hP : ∀ c ∈ S, ∀ i j, η j ≤ η i → P c i → P c j) :
    (∑ i, if (∀ c ∈ S, P c i) then w i else 0) =
      minOr1 S (fun c => ∑ i, if P c i then w i else 0) := by
  classical
  by_cases hS : S.Nonempty
  swap
  · rw [Finset.not_nonempty_iff_eq_empty] at hS
    subst hS
    simp [minOr1, hw1]
  have nest : ∀ c ∈ S, ∀ c' ∈ S, (∀ i, P c i → P c' i) ∨ (∀ i, P c' i → P c i) := by
    intro c hc c' hc'
    by_contra h
    push_neg at h
    obtain ⟨⟨i, hi, hi'⟩, ⟨j, hj, hj'⟩⟩ := h
    rcases le_total (η j) (η i) with hij | hij
    · exact hj' (hP c hc i j hij hi)
    · exact hi' (hP c' hc' j i hij hj)
  obtain ⟨c₀, hc₀, hmin⟩ := S.exists_min_image
    (fun c => (Finset.univ.filter (fun i => P c i)).card) hS
  have key : ∀ i, (∀ c ∈ S, P c i) ↔ P c₀ i := by
    intro i
    refine ⟨fun h => h c₀ hc₀, fun h c hc => ?_⟩
    rcases nest c₀ hc₀ c hc with h1 | h1
    · exact h1 i h
    · have hsub : (Finset.univ.filter (fun i => P c i)) ⊆
          (Finset.univ.filter (fun i => P c₀ i)) := by
        intro x hx
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
        exact h1 x hx
      have heq := Finset.eq_of_subset_of_card_le hsub (hmin c hc)
      have : i ∈ Finset.univ.filter (fun i => P c i) := by
        rw [heq]; simp [h]
      simpa using this
  have hL : (∑ i, if (∀ c ∈ S, P c i) then w i else 0) =
      ∑ i, if P c₀ i then w i else 0 := by
    apply Finset.sum_congr rfl
    intro i _
    simp only [key i]
  rw [hL]
  unfold minOr1
  rw [dif_pos hS]
  apply le_antisymm
  · apply Finset.le_inf'
    intro c hc
    apply Finset.sum_le_sum
    intro i _
    by_cases h0 : P c₀ i
    · have : P c i := (key i).2 h0 c hc
      simp [h0, this]
    · simp only [h0, if_false]
      split_ifs
      · exact hw0 i
      · exact le_refl _
  · exact Finset.inf'_le _ hc₀

end Q3L
