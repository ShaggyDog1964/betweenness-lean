import K4.Defs

namespace K4

/-- A relation that is transitive on `S` and holds between consecutive entries holds
pairwise.
Sketch: by `List.pairwise_map` and `List.pairwise_iff_getElem` (or induction on `m`
with `List.range_succ`, `List.pairwise_append`) reduce to `∀ i < j < m, r (g i) (g j)`;
prove it by induction on `j - i` (or on `j`), chaining `hstep` with `htrans`. -/
theorem pairwise_range_of_chain {α : Type*} (S : Set α) (r : α → α → Prop)
    (htrans : ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, r a b → r b c → r a c)
    (g : ℕ → α) (m : ℕ) (hg : ∀ i, i < m → g i ∈ S)
    (hstep : ∀ i, i + 1 < m → r (g i) (g (i + 1))) :
    ((List.range m).map g).Pairwise r := by
  have key : ∀ i j, i < j → j < m → r (g i) (g j) := by
    intro i j hij
    induction j, hij using Nat.le_induction with
    | base => exact fun hjm => hstep i hjm
    | succ k hk ih =>
      intro hjm
      have hkm : k < m := by omega
      exact htrans _ (hg i (by omega)) _ (hg k hkm) _ (hg (k + 1) hjm)
        (ih hkm) (hstep k hjm)
  rw [List.pairwise_map]
  have h := List.pairwise_lt_range (n := m)
  rw [List.pairwise_iff_getElem] at h ⊢
  intro i j hi hj hij
  have := h i j hi hj hij
  simp only [List.getElem_range] at this ⊢
  exact key i j this (by simpa using hj)

end K4
