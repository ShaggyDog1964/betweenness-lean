/-
`vtx_fosd`: the best vertex weakly dominates every lottery, and every lottery
weakly dominates the worst vertex.
-/
import Q3L.Statement
import K4.Defs

namespace Q3L

open K4 (Lot Simplex tail)

/-- `δ_{K-1}` weakly FOSD-dominates every lottery; every lottery weakly dominates `δ_0`.
Sketch. `tail (K4.vtx K (K-1)) k = 1` for every `k : Fin K` (the only nonzero entry is at
index `K-1 ≥ k`; `Finset.sum_ite_eq`), and `tail y k ≤ ∑ i, y i = 1`
(`Finset.sum_le_sum_of_subset_of_nonneg`, `y ≥ 0`). For `δ_0`: `tail (K4.vtx K 0) k` is `1` if
`k = 0` and `0` otherwise; `tail y 0 = ∑ y = 1` (the filter `0 ≤ i` is everything) and
`tail y k ≥ 0`. -/
theorem vtx_fosd {K : ℕ} (hK : 0 < K) {y : Lot K} (hy : y ∈ Simplex K) :
    K4.FOSD (K4.vtx K (K - 1)) y ∧ K4.FOSD y (K4.vtx K 0) := by
  obtain ⟨hnn, hsum⟩ := hy
  have hle : ∀ k : Fin K, tail y k ≤ 1 := by
    intro k
    rw [← hsum]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun i _ _ => hnn i)
  have hge : ∀ k : Fin K, 0 ≤ tail y k := fun k =>
    Finset.sum_nonneg (fun i _ => hnn i)
  constructor
  · intro k
    have : tail (K4.vtx K (K - 1)) k = 1 := by
      unfold tail K4.vtx
      rw [Finset.sum_eq_single ⟨K - 1, by omega⟩]
      · simp
      · intro b _ hb
        have : b.val ≠ K - 1 := fun h => hb (Fin.ext h)
        simp [this]
      · intro h
        exfalso; apply h
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        rw [Fin.le_def]; simp; omega
    rw [this]; exact hle k
  · intro k
    by_cases hk : k.val = 0
    · have h1 : tail y k = 1 := by
        rw [← hsum]; unfold tail
        congr 1
        ext i; simp [Fin.le_def, hk]
      rw [h1]
      unfold tail K4.vtx
      rw [Finset.sum_eq_single ⟨0, hK⟩]
      · simp
      · intro b _ hb
        have : b.val ≠ 0 := fun h => hb (Fin.ext h)
        simp [this]
      · intro h
        exfalso; apply h
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.le_def]
        omega
    · have : tail (K4.vtx K 0) k = 0 := by
        unfold tail K4.vtx
        apply Finset.sum_eq_zero
        intro i hi
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.le_def] at hi
        have : i.val ≠ 0 := by omega
        simp [this]
      rw [this]; exact hge k

end Q3L
