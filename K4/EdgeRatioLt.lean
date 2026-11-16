import K4.Defs
import K4.FosdShift
import K4.RLotMem

namespace K4

/-- Along an edge, a strictly preferred point has a strictly smaller odds ratio
(less mass on the worse prize `i`).
Sketch: by contradiction assume `y ≤ x`. If `y = x`, `h` is `SPref R a a`, impossible.
If `y < x`: `rLot K i j y = rLot K i j x + δ • (vtx K j - vtx K i)` with
`δ = x/(x+1) - y/(y+1) = (x - y)/((x+1)(y+1)) > 0` (funext, `field_simp`), so
`strictFOSD_shift` and `hR.strictMono` (memberships by `rLot_mem_simplex`) give
`SPref R (rLot y) (rLot x)`, whose first component contradicts `h.2`. -/
theorem edge_ratio_lt {K : ℕ} {R : Rel K} (hR : IsBetweennessPref R) {i j : ℕ}
    (hij : i < j) (hj : j < K) {x y : ℝ} (hx : 0 < x) (hy : 0 < y)
    (h : SPref R (rLot K i j x) (rLot K i j y)) : x < y := by
  by_contra hxy'
  have hxy : y ≤ x := not_lt.mp hxy'
  rcases hxy.lt_or_eq with hlt | heq
  · have hx1 : 0 < x + 1 := by linarith
    have hy1 : 0 < y + 1 := by linarith
    set δ : ℝ := x / (x + 1) - y / (y + 1) with hδdef
    have hδ : 0 < δ := by
      rw [hδdef, div_sub_div _ _ hx1.ne' hy1.ne']
      apply div_pos _ (mul_pos hx1 hy1)
      nlinarith
    have hji : j ≠ i := by omega
    have heq' : rLot K i j y = rLot K i j x + δ • (vtx K j - vtx K i) := by
      funext k
      simp only [rLot, vtx, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
      by_cases h1 : k.val = i
      · have h2 : k.val ≠ j := by omega
        simp only [h1, hij.ne, ↓reduceIte, hδdef]
        ring
      · simp only [h1, ↓reduceIte]
        by_cases h2 : k.val = j
        · simp only [h2, ↓reduceIte, hδdef]
          field_simp
          ring
        · simp only [h2, ↓reduceIte]
          ring
    have hmx := rLot_mem_simplex (K := K) (Ne.symm hji) (by omega) hj hx.le
    have hmy := rLot_mem_simplex (K := K) (Ne.symm hji) (by omega) hj hy.le
    have hs := strictFOSD_shift hij hj (rLot K i j x) hδ
    rw [← heq'] at hs
    exact h.2 (hR.strictMono _ hmy _ hmx hs).1
  · rw [heq] at h
    exact h.2 h.1

end K4
