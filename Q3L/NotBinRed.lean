/-
`not_binaryReduction`.
-/
import Q3L.Statement

namespace Q3L

open K4 (Lot IsBetweennessPref)

/-- Two mixtures of betweenness preferences with all binary probabilities `½` that differ on
some menu refute the binary reduction.
Sketch. Assume `h : BinaryReduction X`. Binary agreement: for `x ≠ y` both values are `1/2`
(`hbin`); for `x = y`, `{x, x} = {x}` (`Finset.pair_self` / `Finset.insert_eq_of_mem`) and
`ρ.p x {x} = 1 = ρ'.p x {x}` (`sum_one` with `Finset.sum_singleton`, `{x} ⊆ X`). So `h ρ ρ'`
gives agreement on the menu `A` from `hdiff` (nonempty because it contains `x`),
contradiction. -/
theorem not_binaryReduction {K : ℕ} {X : Finset (Lot K)} (ρ ρ' : RandomChoiceRule X)
    (hρ : IsMixture IsBetweennessPref X ρ) (hρ' : IsMixture IsBetweennessPref X ρ')
    (hbin : ∀ x ∈ X, ∀ y ∈ X, x ≠ y → ρ.p x {x, y} = 1 / 2 ∧ ρ'.p x {x, y} = 1 / 2)
    (hdiff : ∃ A ⊆ X, ∃ x ∈ A, ρ.p x A ≠ ρ'.p x A) : ¬ BinaryReduction X := by
  intro h
  obtain ⟨A, hA, x, hx, hne⟩ := hdiff
  have hsing : ∀ (σ : RandomChoiceRule X) (z : Lot K), z ∈ X → σ.p z {z} = 1 := by
    intro σ z hz
    have := σ.sum_one {z} (Finset.singleton_subset_iff.2 hz) (Finset.singleton_nonempty z)
    rwa [Finset.sum_singleton] at this
  refine hne (h ρ ρ' hρ hρ' ?_ A hA ⟨x, hx⟩ x hx)
  intro a ha b hb
  by_cases hab : a = b
  · subst hab
    rw [Finset.insert_eq_of_mem (Finset.mem_singleton_self a), hsing ρ a ha, hsing ρ' a ha]
  · rw [(hbin a ha b hb hab).1, (hbin a ha b hb hab).2]

end Q3L
