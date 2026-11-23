/-
`label_exists`: the real label `η_i` in the proof of Theorem 36(1).
-/
import Q3L.Statement
import Q3L.DotEq
import Q3L.DotPosCone
import Q3L.Compare

namespace Q3L

open K4 (Lot Simplex Rel SPref IsBetweennessPref)

/-- For a betweenness preference `R`, a lottery `x`, a nonzero weak-FOSD direction `d0` and any
`g`, there is `η` such that whenever `x - y = α d0 + β g` (`y` in the simplex),
`x ≻ y ↔ α + β η > 0`.
Sketch. `comparison_frame hK hR hx` gives strictly increasing `W` with
`SPref R x y ↔ 0 < dot W (x - y)`. `dot_pos_of_cone hK` gives `c := dot W d0 > 0`. Put
`η := dot W g / c`. If `x - y = α • d0 + β • g` then
`dot W (x - y) = α * c + β * dot W g = c * (α + β * η)` (`dot_eq_dotProduct`, linearity,
`field_simp`), positive iff `α + β * η > 0` since `c > 0`. -/
theorem label_exists {K : ℕ} (hK : 0 < K) {R : Rel K} (hR : IsBetweennessPref R) {x : Lot K}
    (hx : x ∈ Simplex K) {d0 : Lot K} (hd0D : d0 ∈ FOSDCone K) (hd0 : d0 ≠ 0) (g : Lot K) :
    ∃ η : ℝ, ∀ y ∈ Simplex K, ∀ α β : ℝ, x - y = α • d0 + β • g →
      (SPref R x y ↔ 0 < α + β * η) := by
  obtain ⟨W, hW, hcmp⟩ := comparison_frame hK hR hx
  have hc := dot_pos_of_cone hK hW hd0D hd0
  refine ⟨dot W g / dot W d0, ?_⟩
  intro y hy α β hxy
  have hlin : dot W (x - y) = α * dot W d0 + β * dot W g := by
    rw [hxy, dot_eq_dotProduct, dot_eq_dotProduct, dot_eq_dotProduct, dotProduct_add,
      dotProduct_smul, dotProduct_smul, smul_eq_mul, smul_eq_mul]
  have he : α * dot W d0 + β * dot W g = dot W d0 * (α + β * (dot W g / dot W d0)) := by
    field_simp
  rw [hcmp y hy, hlin, he]
  exact ⟨fun h => pos_of_mul_pos_right h hc.le, fun h => mul_pos hc h⟩

end Q3L
