/-
`mix_of_param`: the middle point of three on a line is a mixture of the
other two.
-/
import Q3L.Statement

namespace Q3L

open K4 (Lot)

/-- If `x, y, z` lie on the line `x₀ + s d` with parameters `φ x < φ y < φ z`, then
`y = mix t x z` for some `t ∈ (0,1)`.
Sketch. `t := (φ z - φ y) / (φ z - φ x) ∈ (0,1)`. `K4.mix t x z = t • x + (1 - t) • z =
x₀ + (t * φ x + (1 - t) * φ z) • d` (substitute `hx`, `hz`; `module`), and
`t * φ x + (1 - t) * φ z = φ y` (`field_simp`, `ring`). Rewrite with `hy`. -/
theorem mix_of_param {K : ℕ} {x0 d x y z : Lot K} {φ : Lot K → ℝ}
    (hx : x = x0 + φ x • d) (hy : y = x0 + φ y • d) (hz : z = x0 + φ z • d)
    (hxy : φ x < φ y) (hyz : φ y < φ z) : ∃ t ∈ Set.Ioo (0 : ℝ) 1, y = K4.mix t x z := by
  set a := φ x
  set b := φ y
  set c := φ z
  clear_value a b c
  subst hx hy hz
  have hca : 0 < c - a := by linarith
  refine ⟨(c - b) / (c - a), ⟨div_pos (by linarith) hca, (div_lt_one hca).2 (by linarith)⟩, ?_⟩
  have key : (c - b) / (c - a) * a + (1 - (c - b) / (c - a)) * c = b := by
    field_simp
    ring
  unfold K4.mix
  funext i
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  linear_combination (-(d i)) * key

end Q3L
