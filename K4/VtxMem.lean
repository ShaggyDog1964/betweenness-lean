import K4.Defs

namespace K4

/-- A vertex lies in the simplex. Sketch: entries are `0` or `1`, exactly one entry
(index `⟨i, hi⟩`) is `1`, so the sum is `1` (`Finset.sum_ite_eq'`). -/
theorem vtx_mem_simplex {K i : ℕ} (hi : i < K) : vtx K i ∈ Simplex K := by
  show (∀ k, 0 ≤ vtx K i k) ∧ ∑ k, vtx K i k = 1
  refine ⟨fun k => ?_, ?_⟩
  · simp only [vtx]
    split_ifs <;> norm_num
  · have h0 : ∀ b ∈ (Finset.univ : Finset (Fin K)), b ≠ ⟨i, hi⟩ → vtx K i b = 0 := by
      intro b _ hb
      have hne : b.val ≠ i := fun h => hb (Fin.ext h)
      simp [vtx, hne]
    rw [Finset.sum_eq_single_of_mem _ (Finset.mem_univ _) h0]
    simp [vtx]

end K4
