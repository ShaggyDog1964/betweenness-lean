/-
`exists_pos_zero`: a positive point on the hyperplane `dot W = 0`.
-/
import Q3L.Statement
import Q3L.DotEq
import K4.MixMem

namespace Q3L

open K4 (Lot Simplex)

/-- Between a positive simplex point with `dot W < 0` and one with `dot W > 0` there is a
positive simplex point with `dot W = 0`.
Sketch (explicit, no IVT). Let `a := dot W z < 0 < b := dot W z'` and `s := b / (b - a) ∈
(0,1)`. Put `p := K4.mix s z z' = s • z + (1 - s) • z'`. Then `p ∈ Simplex`
(`K4.mix_mem_simplex`), `p k = s * z k + (1 - s) * z' k > 0`, and
`dot W p = s * a + (1 - s) * b = (b * a - a * b) / (b - a) = 0` (`dot_eq_dotProduct`,
linearity, `field_simp`). -/
theorem exists_pos_zero {K : ℕ} {W z z' : Lot K} (hz : z ∈ Simplex K) (hzp : ∀ k, 0 < z k)
    (hz' : z' ∈ Simplex K) (hz'p : ∀ k, 0 < z' k) (h1 : dot W z < 0) (h2 : 0 < dot W z') :
    ∃ p ∈ Simplex K, (∀ k, 0 < p k) ∧ dot W p = 0 := by
  have hba : 0 < dot W z' - dot W z := by linarith
  have hs0 : 0 < dot W z' / (dot W z' - dot W z) := div_pos h2 hba
  have hs1 : dot W z' / (dot W z' - dot W z) < 1 := by
    rw [div_lt_one hba]; linarith
  have hmix : ∀ i, K4.mix (dot W z' / (dot W z' - dot W z)) z z' i
      = dot W z' / (dot W z' - dot W z) * z i
        + (1 - dot W z' / (dot W z' - dot W z)) * z' i := fun i => rfl
  refine ⟨K4.mix (dot W z' / (dot W z' - dot W z)) z z',
    K4.mix_mem_simplex hz hz' hs0.le hs1.le, fun k => ?_, ?_⟩
  · rw [hmix k]
    have : 0 < 1 - dot W z' / (dot W z' - dot W z) := by linarith
    have := hzp k
    have := hz'p k
    positivity
  · have hd : ∀ t : ℝ, dot W (K4.mix t z z') = t * dot W z + (1 - t) * dot W z' := by
      intro t
      have hm : ∀ i, K4.mix t z z' i = t * z i + (1 - t) * z' i := fun i => rfl
      simp only [dot, hm, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
      congr 1 <;> exact Finset.sum_congr rfl (fun i _ => by ring)
    rw [hd]
    field_simp
    ring

end Q3L
