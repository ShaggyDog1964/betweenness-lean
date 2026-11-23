import Q1.Defs

namespace Q1

/-- The chain preference of a monotone chain is a weak order.
Sketch: transitivity is composition of implications. Completeness: if not `chainRel U x y`,
pick `k` with `y ∈ U k`, `x ∉ U k`; for any `k'` with `x ∈ U k'`, `k' ≤ k` is impossible
(monotonicity would put `x ∈ U k`), so `k ≤ k'` and `y ∈ U k ⊆ U k'`. -/
theorem chainRel_weakOrder {U : ℕ → Set Pt} (hU : Monotone U) : IsWeakOrder (chainRel U) := by
  refine ⟨fun x y => ?_, fun x y z hxy hyz k hz => hxy k (hyz k hz)⟩
  by_cases h : chainRel U x y
  · exact Or.inl h
  · right
    simp only [chainRel, not_forall] at h
    obtain ⟨k, hyk, hxk⟩ := h
    intro k' hxk'
    rcases le_total k' k with hle | hle
    · exact absurd (hU hle hxk') hxk
    · exact hU hle hyk

end Q1
