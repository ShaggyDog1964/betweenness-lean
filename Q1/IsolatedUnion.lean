import Q1.Defs

namespace Q1

/-- Adding points whose row and column meet nothing else keeps orthogonal convexity.
Sketch (HConv): let `y, z ∈ B ∪ S`, `y.2 = z.2`, `w` between them on that line. If `y ∈ S`
and `z ≠ y`, `hiso y _ z _` gives `z.2 ≠ y.2`, contradiction; so `z = y`, then
`w.1 = y.1` (`Set.uIcc_self`), `w.2 = y.2`, `w = y ∈ B ∪ S`. Symmetric if `z ∈ S`.
Otherwise `y, z ∈ B` and `hH` applies. VConv is identical with coordinates swapped. -/
theorem isolated_union_conv {B S : Set Pt} (hH : HConv B) (hV : VConv B)
    (hiso : ∀ s ∈ S, ∀ u ∈ B ∪ S, u ≠ s → u.1 ≠ s.1 ∧ u.2 ≠ s.2) :
    HConv (B ∪ S) ∧ VConv (B ∪ S) := by
  constructor
  · intro y z w hy hz hyz hw hw1
    have key : ∀ s u : Pt, s ∈ S → u ∈ B ∪ S → s.2 = u.2 → u = s := by
      intro s u hs hu he
      by_contra hne
      exact (hiso s hs u hu hne).2 he.symm
    have fin : z = y → w ∈ B ∪ S := by
      intro h
      subst h
      rw [Set.uIcc_self, Set.mem_singleton_iff] at hw1
      have : w = z := Prod.ext hw1 hw
      rw [this]; exact hy
    rcases hy with hyB | hyS
    · rcases hz with hzB | hzS
      · exact Or.inl (hH y z w hyB hzB hyz hw hw1)
      · exact fin (key z y hzS (Or.inl hyB) hyz.symm).symm
    · exact fin (key y z hyS hz hyz)
  · intro y z w hy hz hyz hw hw2
    have key : ∀ s u : Pt, s ∈ S → u ∈ B ∪ S → s.1 = u.1 → u = s := by
      intro s u hs hu he
      by_contra hne
      exact (hiso s hs u hu hne).1 he.symm
    have fin : z = y → w ∈ B ∪ S := by
      intro h
      subst h
      rw [Set.uIcc_self, Set.mem_singleton_iff] at hw2
      have : w = z := Prod.ext hw hw2
      rw [this]; exact hy
    rcases hy with hyB | hyS
    · rcases hz with hzB | hzS
      · exact Or.inl (hV y z w hyB hzB hyz hw hw2)
      · exact fin (key z y hzS (Or.inl hyB) hyz.symm).symm
    · exact fin (key y z hyS hz hyz)

end Q1
