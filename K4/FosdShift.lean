import K4.Defs

namespace K4

/-- The upper tail at `k` of the vertex on prize `m` is `1` when `k ≤ m`. -/
private lemma sum_vtx_filter {K m : ℕ} (hm : m < K) (k : Fin K) (hk : k.val ≤ m) :
    ∑ x ∈ Finset.univ.filter (fun x : Fin K => k ≤ x), vtx K m x = 1 := by
  rw [Finset.sum_eq_single_of_mem (⟨m, hm⟩ : Fin K)]
  · simp [vtx]
  · rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, hk⟩
  · intro b _ hb
    have hbm : b.val ≠ m := fun h => hb (Fin.ext h)
    simp [vtx, hbm]

/-- Moving mass `δ > 0` from prize `i` to a better prize `j > i` is a strict FOSD
improvement (no simplex hypothesis needed).
Sketch: `tail (p + δ•(e_j - e_i)) k = tail p k + δ * ([k ≤ j] - [k ≤ i])`
(`Finset.sum_add_distrib`, `Finset.sum_ite`), and `[k ≤ i] ≤ [k ≤ j]` since `i < j`.
Inequality of functions: evaluate at index `⟨j, hj⟩`, where the value rises by `δ`
(because `j ≠ i`). -/
theorem strictFOSD_shift {K i j : ℕ} (hij : i < j) (hj : j < K) (p : Lot K) {δ : ℝ}
    (hδ : 0 < δ) : StrictFOSD (p + δ • (vtx K j - vtx K i)) p := by
  have hji : j ≠ i := by omega
  have hi : i < K := by omega
  refine ⟨fun k => ?_, fun h => ?_⟩
  · unfold tail
    simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    rw [Finset.sum_add_distrib]
    have hnn : 0 ≤ ∑ x ∈ Finset.univ.filter (fun x : Fin K => k ≤ x),
        δ * (vtx K j x - vtx K i x) := by
      by_cases hki : k.val ≤ i
      · rw [← Finset.mul_sum, Finset.sum_sub_distrib, sum_vtx_filter hj k (by omega),
          sum_vtx_filter hi k hki]
        simp
      · apply Finset.sum_nonneg
        intro x hx
        rw [Finset.mem_filter] at hx
        have hxk : k.val ≤ x.val := hx.2
        have hxi : x.val ≠ i := by omega
        have h1 : vtx K i x = 0 := by simp [vtx, hxi]
        have h2 : 0 ≤ vtx K j x := by
          by_cases hxj : x.val = j <;> simp [vtx, hxj]
        rw [h1]
        exact mul_nonneg hδ.le (by linarith)
    linarith
  · have a : vtx K j ⟨j, hj⟩ = 1 := by simp [vtx]
    have b : vtx K i ⟨j, hj⟩ = 0 := by simp [vtx, hji]
    have hv : (p + δ • (vtx K j - vtx K i)) ⟨j, hj⟩ = p ⟨j, hj⟩ + δ := by
      simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, a, b]
      ring
    have h3 := congrFun h ⟨j, hj⟩
    rw [hv] at h3
    linarith

end K4
