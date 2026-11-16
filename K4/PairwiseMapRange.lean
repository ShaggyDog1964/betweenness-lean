import K4.Defs

namespace K4

/-- Pairwise relations on `(List.range n).map f` are relations between indices.
Sketch: `List.pairwise_map`, then `List.pairwise_iff_getElem` (or induction on `n` with
`List.range_succ`, `List.pairwise_append`), `List.getElem_range`, `List.mem_range`. -/
theorem pairwise_map_range_iff {α : Type*} (r : α → α → Prop) (f : ℕ → α) (n : ℕ) :
    ((List.range n).map f).Pairwise r ↔ ∀ i j, i < j → j < n → r (f i) (f j) := by
  rw [List.pairwise_map]
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.pairwise_append, ih]
    simp only [List.pairwise_singleton, List.mem_range, List.mem_singleton, true_and]
    constructor
    · rintro ⟨h1, h2⟩ i j hij hj
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
      · exact h1 i j hij hj
      · exact h2 i (by omega) j rfl
    · intro h
      refine ⟨fun i j hij hj => h i j hij (by omega), ?_⟩
      rintro i hi j hj
      subst hj
      exact h i _ hi (by omega)

end K4
