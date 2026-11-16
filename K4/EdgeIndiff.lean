import K4.Defs
import K4.SegmentIVT
import K4.VtxMem

namespace K4

/-- On the edge from a worse vertex `i` to a better vertex `j`, a level strictly between
the two vertices has an indifferent point with a positive finite odds ratio.
Sketch: `exists_indiff_on_segment` with `q = vtx K j`, `r = vtx K i` (membership by
`vtx_mem_simplex`) gives `t ∈ [0,1]` with `mix t (vtx j) (vtx i) ∼ l`. `t ≠ 0`, since
`mix 0 = vtx i` and `vtx i ∼ l` contradicts `hli.2`; `t ≠ 1`, since `mix 1 = vtx j` and
`l ≽ vtx j` contradicts `hjl.2`. With `x = (1 - t)/t > 0`,
`mix t (vtx j) (vtx i) = rLot K i j x` (funext; coordinate `i` is `1 - t = x/(x+1)`,
coordinate `j` is `t = 1/(x+1)`, others `0`; uses `i ≠ j`). -/
theorem exists_edge_indiff {K : ℕ} {R : Rel K} (hR : IsBetweennessPref R) {i j : ℕ}
    (hij : i < j) (hj : j < K) {l : Lot K} (hl : l ∈ Simplex K)
    (hjl : SPref R (vtx K j) l) (hli : SPref R l (vtx K i)) :
    ∃ x : ℝ, 0 < x ∧ Indiff R (rLot K i j x) l := by
  obtain ⟨t, ⟨ht0, ht1⟩, hti⟩ := exists_indiff_on_segment hR (vtx_mem_simplex hj)
    (vtx_mem_simplex (lt_trans hij hj)) hl hjl.1 hli.1
  have htne0 : t ≠ 0 := by
    rintro rfl
    have : mix 0 (vtx K j) (vtx K i) = vtx K i := by simp [mix]
    rw [this] at hti
    exact hli.2 hti.1
  have htne1 : t ≠ 1 := by
    rintro rfl
    have : mix 1 (vtx K j) (vtx K i) = vtx K j := by simp [mix]
    rw [this] at hti
    exact hjl.2 hti.2
  have htpos : 0 < t := lt_of_le_of_ne ht0 (Ne.symm htne0)
  have htlt : t < 1 := lt_of_le_of_ne ht1 htne1
  refine ⟨(1 - t) / t, div_pos (by linarith) htpos, ?_⟩
  have hx1 : (1 - t) / t + 1 = 1 / t := by field_simp; ring
  have heq : rLot K i j ((1 - t) / t) = mix t (vtx K j) (vtx K i) := by
    funext k
    have hne : i ≠ j := Nat.ne_of_lt hij
    simp only [rLot, mix, vtx, hx1, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    by_cases hki : k.val = i
    · have hkj : ¬ k.val = j := by omega
      rw [if_pos hki, if_neg hkj, if_pos hki]
      field_simp
      ring
    · by_cases hkj : k.val = j
      · rw [if_neg hki, if_pos hkj, if_pos hkj, if_neg hki]
        field_simp
        ring
      · rw [if_neg hki, if_neg hkj, if_neg hkj, if_neg hki]
        ring
  rw [heq]
  exact hti

end K4
