import Conv.Hull

/-!
# Chain preferences

A chain `U : ℕ → Set α` induces the preference "x ≽ y iff x lies in every member of the
chain containing y". For a monotone chain of convex sets this is a quasi-concave weak order,
and it ranks a list strictly when each entry enters the chain at its own position.
-/

namespace Conv

universe u

variable {α : Type u} {C : Set (Set α)} {U : ℕ → Set α}

/-- The chain preference: `x ≽ y` iff every member of the chain containing `y` contains `x`. -/
def chainRel (U : ℕ → Set α) : Rel α := fun x y => ∀ k, y ∈ U k → x ∈ U k

/-- The chain preference of a monotone chain is a weak order.
Sketch: transitivity composes implications. Completeness: if not `x ≽ y`, pick `k` with
`y ∈ U k`, `x ∉ U k`; any `k'` with `x ∈ U k'` has `k ≤ k'`, so `y ∈ U k'`. -/
theorem chainRel_weakOrder (hU : Monotone U) : IsWeakOrder (chainRel U) := by
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

/-- The chain preference of a chain of convex sets is quasi-concave: the upper set of `x` is
`⋂₀ {U k | x ∈ U k}`, an intersection of a subfamily of `C`. -/
theorem chainRel_ucc (hC : IsConvexity C) (hU : ∀ k, U k ∈ C) : UCC C (chainRel U) := by
  intro x
  have h : {y | chainRel U y x} = ⋂₀ {S | ∃ k, x ∈ U k ∧ U k = S} := by
    ext y
    simp only [chainRel, Set.mem_ofPred_eq, Set.mem_sInter]
    constructor
    · rintro h S ⟨k, hk, rfl⟩
      exact h k hk
    · intro h k hk
      exact h _ ⟨k, hk, rfl⟩
  rw [h]
  exact hC _ (by rintro S ⟨k, -, rfl⟩; exact hU k)

/-- Strictness of the chain preference along a list: if `L[i] ∈ U i` for all `i` and
`L[j] ∉ U (j - 1)` for `j > 0`, the chain preference ranks `L` strictly.
Sketch: for `i < j`, (≽) if `L[j] ∈ U k` then `j ≤ k`, so `L[i] ∈ U i ⊆ U k`; (not ≼)
`L[i] ∈ U i` but `L[j] ∉ U i ⊆ U (j - 1)`. -/
theorem chainRel_pairwise (hU : Monotone U) (L : List α)
    (hmem : ∀ i (h : i < L.length), L[i] ∈ U i)
    (hnot : ∀ j (h : j < L.length), 0 < j → L[j] ∉ U (j - 1)) :
    L.Pairwise (SPref (chainRel U)) := by
  rw [List.pairwise_iff_getElem]
  intro i j hi hj hij
  refine ⟨?_, ?_⟩
  · intro k hk
    have hjk : j ≤ k := by
      by_contra hc
      exact hnot j hj (by omega) (hU (show k ≤ j - 1 by omega) hk)
    exact hU (show i ≤ k by omega) (hmem i hi)
  · intro h
    exact hnot j hj (by omega) (hU (show i ≤ j - 1 by omega) (h i (hmem i hi)))

end Conv
