import Q1.Defs

namespace Q1

/-- Two distinct members of a list occur as a length-2 sublist, in one of the two orders.
Sketch: induction on `l`. For `a :: l`: if `y = a` then `z ∈ l` (as `z ≠ y`), so
`[y, z] <+ a :: l` by `Sublist.cons₂` of `[z] <+ l`; symmetric if `z = a`; otherwise both
lie in `l`: apply the IH and `Sublist.cons`. -/
theorem pair_sublist_of_mem {l : List Pt} {y z : Pt} (hy : y ∈ l) (hz : z ∈ l) (hne : y ≠ z) :
    [y, z].Sublist l ∨ [z, y].Sublist l := by
  induction l with
  | nil => exact absurd hy List.not_mem_nil
  | cons a l ih =>
    rcases List.mem_cons.mp hy with rfl | hy'
    · have hz' : z ∈ l := by
        rcases List.mem_cons.mp hz with h | h
        · exact absurd h.symm hne
        · exact h
      exact Or.inl ((List.singleton_sublist.mpr hz').cons_cons y)
    · rcases List.mem_cons.mp hz with rfl | hz'
      · exact Or.inr ((List.singleton_sublist.mpr hy').cons_cons z)
      · rcases ih hy' hz' with h | h
        · exact Or.inl (h.cons a)
        · exact Or.inr (h.cons a)

end Q1
