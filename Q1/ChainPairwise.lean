import Q1.Defs

namespace Q1

/-- Strictness of the chain preference along a list.
Sketch: fix `i < j`. (≽) if `L[j] ∈ U k` then `k > j` (else `U k ⊆ U j ∌ L[j]`), so
`i + 1 ≤ k` and `L[i] ∈ U (i+1) ⊆ U k` (note `i + 1 < L.length` as `i < j`). (not ≼) take
`k = i + 1`: `L[i] ∈ U (i+1)`, and `L[j] ∉ U (i+1)` since `U (i+1) ⊆ U j`. Conclude with
`List.pairwise_iff_getElem`. -/
theorem chainRel_pairwise {U : ℕ → Set Pt} (hU : Monotone U) (L : List Pt)
    (hmem : ∀ j (h : j + 1 < L.length), L[j] ∈ U (j + 1))
    (hnot : ∀ j (h : j < L.length), L[j] ∉ U j) :
    L.Pairwise (SPref (chainRel U)) := by
  rw [List.pairwise_iff_getElem]
  intro i j hi hj hij
  have hi1 : i + 1 < L.length := by omega
  refine ⟨?_, ?_⟩
  · intro k hk
    have hkj : j < k := by
      by_contra hc
      exact hnot j hj (hU (Nat.le_of_not_lt hc) hk)
    exact hU (show i + 1 ≤ k by omega) (hmem i hi1)
  · intro h
    exact hnot j hj (hU (show i + 1 ≤ j by omega) (h (i + 1) (hmem i hi1)))

end Q1
