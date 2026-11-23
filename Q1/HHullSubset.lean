import Q1.Defs

namespace Q1

/-- `hHull` is monotone in the member set. Sketch: reuse the same witnesses `y`, `z`. -/
theorem hHull_subset {l₁ l₂ : List Pt} (h : ∀ x ∈ l₁, x ∈ l₂) : hHull l₁ ⊆ hHull l₂ := by
  rintro w ⟨y, hy, z, hz, h1, h2, h3⟩
  exact ⟨y, h y hy, z, h z hz, h1, h2, h3⟩

end Q1
