/-
`atMostTwo_of_line`: at most two rankings on a collinear `X`.
-/
import Q3L.Statement
import Q3L.LineRanking

namespace Q3L

open K4 (Lot Simplex)

/-- On a collinear `X`, among any three betweenness preferences strict on `X`, two rank `X`
identically.
Sketch. `line_ranking` puts each `R i` (`i : Fin 3`) in alternative `A₁` (increasing `φ`) or
`A₂` (decreasing). By pigeonhole two indices `i ≠ j` share an alternative (case split on the
three disjunctions: 8 cases, each picks a pair among `0,1,2`). Then for `x, y ∈ X`,
`SPref (R i) x y ↔ (φ-comparison) ↔ SPref (R j) x y`. -/
theorem atMostTwo_of_line {K : ℕ} {X : Finset (Lot K)} (hXs : (↑X : Set (Lot K)) ⊆ Simplex K)
    {x0 d : Lot K} {φ : Lot K → ℝ} (hrep : ∀ x ∈ X, x = x0 + φ x • d) :
    AtMostTwoRankings X := by
  intro R hR
  have h := fun i => line_ranking hXs hrep (hR i).1 (hR i).2
  have key : ∀ i j : Fin 3, i ≠ j →
      ((∀ x ∈ X, ∀ y ∈ X, (K4.SPref (R i) x y ↔ φ x < φ y)) ∧
        (∀ x ∈ X, ∀ y ∈ X, (K4.SPref (R j) x y ↔ φ x < φ y)) ∨
       (∀ x ∈ X, ∀ y ∈ X, (K4.SPref (R i) x y ↔ φ y < φ x)) ∧
        (∀ x ∈ X, ∀ y ∈ X, (K4.SPref (R j) x y ↔ φ y < φ x))) →
      ∃ i j : Fin 3, i ≠ j ∧ ∀ x ∈ X, ∀ y ∈ X,
        (K4.SPref (R i) x y ↔ K4.SPref (R j) x y) := by
    intro i j hij hc
    refine ⟨i, j, hij, fun x hx y hy => ?_⟩
    rcases hc with ⟨a, b⟩ | ⟨a, b⟩
    · rw [a x hx y hy, b x hx y hy]
    · rw [a x hx y hy, b x hx y hy]
  rcases h 0 with h0 | h0 <;> rcases h 1 with h1 | h1
  · exact key 0 1 (by decide) (Or.inl ⟨h0, h1⟩)
  · rcases h 2 with h2 | h2
    · exact key 0 2 (by decide) (Or.inl ⟨h0, h2⟩)
    · exact key 1 2 (by decide) (Or.inr ⟨h1, h2⟩)
  · rcases h 2 with h2 | h2
    · exact key 1 2 (by decide) (Or.inl ⟨h1, h2⟩)
    · exact key 0 2 (by decide) (Or.inr ⟨h0, h2⟩)
  · exact key 0 1 (by decide) (Or.inr ⟨h0, h1⟩)

end Q3L
