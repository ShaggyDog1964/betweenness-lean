import K4.Defs

namespace K4

/-- The simplex is convex. Sketch: `mix t q r k = t * q k + (1 - t) * r k ≥ 0`, and
`∑ (t q k + (1-t) r k) = t + (1 - t) = 1` (`Finset.sum_add_distrib`, `Finset.mul_sum`). -/
theorem mix_mem_simplex {K : ℕ} {q r : Lot K} (hq : q ∈ Simplex K) (hr : r ∈ Simplex K)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : mix t q r ∈ Simplex K := by
  obtain ⟨hq0, hq1⟩ := hq
  obtain ⟨hr0, hr1⟩ := hr
  have h1t : 0 ≤ 1 - t := by linarith
  have h : ∀ i, mix t q r i = t * q i + (1 - t) * r i := fun i => rfl
  show (∀ i, 0 ≤ mix t q r i) ∧ ∑ i, mix t q r i = 1
  refine ⟨fun i => ?_, ?_⟩
  · rw [h i]
    exact add_nonneg (mul_nonneg ht0 (hq0 i)) (mul_nonneg h1t (hr0 i))
  · rw [Finset.sum_congr rfl (fun i _ => h i), Finset.sum_add_distrib,
      ← Finset.mul_sum, ← Finset.mul_sum, hq1, hr1]
    ring

end K4
