/-
`exists_coords`: differences of points of `X` have coordinates in the frame
`(d0, g)`.
-/
import Q3L.Statement

namespace Q3L

open K4 (Lot)

/-- If `dim V = 2` and `d0, g ∈ V` are linearly independent, every `x - y` (`x, y ∈ X`) is
`α d0 + β g`.
Sketch. `S := Submodule.span ℝ {d0, g} ≤ dirSpace X` (`Submodule.span_le`). `finrank S = 2`
(`finrank_span_eq_card` for `![d0, g]`, `Set.range ![d0,g] = {d0, g}` via `Matrix.range_cons`
or `Fin.range_cons`; or `LinearIndependent.finrank_span_eq_card`). With
`finrank (dirSpace X) = 2` (finite-dimensional since `Lot K` is), `Submodule.eq_of_le_of_finrank_eq`
gives `S = dirSpace X`. `x - y = x -ᵥ y ∈ vectorSpan ℝ X` (`vsub_mem_vectorSpan`), so
`x - y ∈ S` and `Submodule.mem_span_pair` gives `α, β` with `α • d0 + β • g = x - y`. -/
theorem exists_coords {K : ℕ} {X : Finset (Lot K)} (hdim : Module.finrank ℝ (dirSpace X) = 2)
    {d0 g : Lot K} (hd0 : d0 ∈ dirSpace X) (hg : g ∈ dirSpace X)
    (hind : LinearIndependent ℝ ![d0, g]) :
    ∀ x ∈ X, ∀ y ∈ X, ∃ α β : ℝ, x - y = α • d0 + β • g := by
  intro x hx y hy
  have hle : Submodule.span ℝ {d0, g} ≤ dirSpace X := by
    rw [Submodule.span_le]
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl
    · exact hd0
    · exact hg
  have hS : Module.finrank ℝ (Submodule.span ℝ ({d0, g} : Set (Lot K))) = 2 := by
    have h := finrank_span_eq_card hind
    have hr : Set.range ![d0, g] = {d0, g} := by
      rw [Matrix.range_cons, Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union]
    rw [hr] at h
    simpa using h
  have heq : Submodule.span ℝ {d0, g} = dirSpace X :=
    Submodule.eq_of_le_of_finrank_eq hle (by rw [hS, hdim])
  have hmem : x - y ∈ dirSpace X :=
    vsub_mem_vectorSpan ℝ (show x ∈ (↑X : Set (Lot K)) from hx)
      (show y ∈ (↑X : Set (Lot K)) from hy)
  rw [← heq, Submodule.mem_span_pair] at hmem
  obtain ⟨a, b, hab⟩ := hmem
  exact ⟨a, b, hab.symm⟩

end Q3L
