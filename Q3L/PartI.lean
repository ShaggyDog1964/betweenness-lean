/-
`part_i`: Theorem 36(1).
-/
import Q3L.Statement
import Q3L.PlanarFormula
import Q3L.BinRedFormula

namespace Q3L

/-- Theorem 36(1).
Sketch. Intro `K hK X hXs hdim d0 hd0V hd0D hd0 g hgV hind`. `0 < K` from `3 ≤ K` (`omega`).
First conjunct: `fun ρ hρ => planar_formula _ hXs hdim hd0V hd0D hd0 hgV hind ρ hρ`.
Second: `binaryReduction_of_formula` applied to that function. -/
theorem part_i : part_i_stmt := by
  intro K hK X hXs hdim d0 hd0V hd0D hd0 g hgV hind
  have hK0 : 0 < K := by omega
  have h : ∀ ρ : RandomChoiceRule X, IsMixture K4.IsBetweennessPref X ρ → PlanarFormula X ρ d0 g :=
    fun ρ hρ => planar_formula hK0 hXs hdim hd0V hd0D hd0 hgV hind ρ hρ
  exact ⟨h, binaryReduction_of_formula h⟩

end Q3L
