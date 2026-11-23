/-
`binaryReduction_of_formula`: formula (1) implies a binary reduction.
-/
import Q3L.Statement
import Q3L.MinOr1Congr

namespace Q3L

open K4 (Lot IsBetweennessPref)

/-- If every mixture of betweenness preferences on `X` satisfies formula (1) in a fixed frame,
a binary reduction holds on `X`.
Sketch. Given `ρ, ρ'` mixtures with equal binary probabilities, `A ⊆ X` nonempty and `x ∈ A`:
rewrite both `ρ.p x A` and `ρ'.p x A` by `h` (`PlanarFormula`). The sets `AS d0 g A x` and
`AN d0 g A x` are the same on both sides and are subsets of `A ⊆ X`
(`Finset.filter_subset`). For `y` in them, `x ∈ X`, `y ∈ X`, so the binary hypothesis gives
`ρ.p x {x, y} = ρ'.p x {x, y}`; `minOr1_congr` finishes. -/
theorem binaryReduction_of_formula {K : ℕ} {X : Finset (Lot K)} {d0 g : Lot K}
    (h : ∀ ρ : RandomChoiceRule X, IsMixture IsBetweennessPref X ρ → PlanarFormula X ρ d0 g) :
    BinaryReduction X := by
  classical
  intro ρ ρ' hρ hρ' hbin A hA _ x hx
  have hxX : x ∈ X := hA hx
  rw [h ρ hρ A hA x hx, h ρ' hρ' A hA x hx]
  have hS : ∀ y ∈ AS d0 g A x, ρ.p x {x, y} = ρ'.p x {x, y} := by
    intro y hy
    unfold AS at hy
    exact hbin x hxX y (hA (Finset.mem_of_mem_filter _ hy))
  have hN : ∀ y ∈ AN d0 g A x, ρ.p x {x, y} = ρ'.p x {x, y} := by
    intro y hy
    unfold AN at hy
    exact hbin x hxX y (hA (Finset.mem_of_mem_filter _ hy))
  rw [minOr1_congr hS, minOr1_congr hN]

end Q3L
