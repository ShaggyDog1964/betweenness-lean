import Q1.Defs

namespace Q1

private lemma hHull_lo {S : List Pt} {y : Pt} (hy : y ∈ hHull S) :
    ∃ a ∈ S, a.2 = y.2 ∧ a.1 ≤ y.1 := by
  obtain ⟨p, hp, q, hq, h1, h2, h3⟩ := hy
  rw [Set.mem_uIcc] at h3
  rcases h3 with ⟨h, _⟩ | ⟨h, _⟩
  · exact ⟨p, hp, h2.symm, h⟩
  · exact ⟨q, hq, by rw [h2, h1], h⟩

private lemma hHull_hi {S : List Pt} {y : Pt} (hy : y ∈ hHull S) :
    ∃ a ∈ S, a.2 = y.2 ∧ y.1 ≤ a.1 := by
  obtain ⟨p, hp, q, hq, h1, h2, h3⟩ := hy
  rw [Set.mem_uIcc] at h3
  rcases h3 with ⟨_, h⟩ | ⟨_, h⟩
  · exact ⟨q, hq, by rw [h2, h1], h⟩
  · exact ⟨p, hp, h2.symm, h⟩

/-- The horizontal hull is horizontally convex.
Sketch: some witness of `y` or `z` lies weakly left of `w`, and some witness lies weakly
right of `w`, all on the horizontal line through `w`; those two witnesses certify `w`. -/
theorem hHull_hconv (S : List Pt) : HConv (hHull S) := by
  intro y z w hy hz hyz hwy hw
  have lo : ∃ a ∈ S, a.2 = w.2 ∧ a.1 ≤ w.1 := by
    rw [Set.mem_uIcc] at hw
    rcases hw with ⟨h, _⟩ | ⟨h, _⟩
    · obtain ⟨a, ha, h2, h1⟩ := hHull_lo hy
      exact ⟨a, ha, by rw [h2, hwy], le_trans h1 h⟩
    · obtain ⟨a, ha, h2, h1⟩ := hHull_lo hz
      exact ⟨a, ha, by rw [h2, hwy, hyz], le_trans h1 h⟩
  have hi : ∃ b ∈ S, b.2 = w.2 ∧ w.1 ≤ b.1 := by
    rw [Set.mem_uIcc] at hw
    rcases hw with ⟨_, h⟩ | ⟨_, h⟩
    · obtain ⟨a, ha, h2, h1⟩ := hHull_hi hz
      exact ⟨a, ha, by rw [h2, hwy, hyz], le_trans h h1⟩
    · obtain ⟨a, ha, h2, h1⟩ := hHull_hi hy
      exact ⟨a, ha, by rw [h2, hwy], le_trans h h1⟩
  obtain ⟨a, ha, ha2, ha1⟩ := lo
  obtain ⟨b, hb, hb2, hb1⟩ := hi
  exact ⟨a, ha, b, hb, by rw [ha2, hb2], ha2.symm, Set.mem_uIcc.2 (Or.inl ⟨ha1, hb1⟩)⟩

end Q1
