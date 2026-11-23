/-
`mixture_pair`: equation (12).
-/
import Q3L.Statement

namespace Q3L

open K4 (Lot Rel SPref)

open Classical in
/-- Equation (12): for distinct `x, y ∈ X`, `ρ(x, {x,y})` is the total weight of the `i` with
`x ≻_i y`.
Sketch. Apply `hform` to `A = {x, y}` (`⊆ X`, nonempty, contains `x`). Termwise,
`IsMaxIn (R i) x {x, y} ↔ SPref (R i) x y`: unfold `IsMaxIn`; `x ∈ {x,y}`; the elements `z` of
`{x, y}` with `z ≠ x` are exactly `y` (`Finset.mem_insert`, `Finset.mem_singleton`, `hxy`).
Then `Finset.sum_congr rfl` with `if_congr`/`by simp`. -/
theorem mixture_pair {K n : ℕ} {X : Finset (Lot K)} {ρ : RandomChoiceRule X}
    {R : Fin n → Rel K} {w : Fin n → ℝ}
    (hform : ∀ A ⊆ X, A.Nonempty → ∀ x ∈ A,
      ρ.p x A = ∑ i, if IsMaxIn (R i) x A then w i else 0)
    {x y : Lot K} (hx : x ∈ X) (hy : y ∈ X) (hxy : x ≠ y) :
    ρ.p x {x, y} = ∑ i, if SPref (R i) x y then w i else 0 := by
  have hsub : ({x, y} : Finset (Lot K)) ⊆ X := by
    intro z hz
    rcases Finset.mem_insert.mp hz with h | h
    · exact h ▸ hx
    · exact (Finset.mem_singleton.mp h) ▸ hy
  rw [hform {x, y} hsub (Finset.insert_nonempty _ _) x (Finset.mem_insert_self _ _)]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hiff : IsMaxIn (R i) x {x, y} ↔ SPref (R i) x y := by
    constructor
    · rintro ⟨_, h⟩
      exact h y (Finset.mem_insert_of_mem (Finset.mem_singleton_self _)) (Ne.symm hxy)
    · intro h
      refine ⟨Finset.mem_insert_self _ _, fun z hz hzx => ?_⟩
      rcases Finset.mem_insert.mp hz with h' | h'
      · exact absurd h' hzx
      · rw [Finset.mem_singleton.mp h']; exact h
  exact if_congr hiff rfl rfl

end Q3L
