/-
`exists_pos_mem_open`: a relatively open set meeting the simplex contains a
point with all coordinates positive.
-/
import Q3L.Statement
import Q3L.MixNear
import K4.MixMem

namespace Q3L

open K4 (Lot Simplex)

/-- If `x ∈ Simplex ∩ G` (`G` open), some `z ∈ Simplex ∩ G` has all coordinates positive.
Sketch. `c := fun _ => 1/K` is in the simplex with positive entries (`0 < K`).
`exists_mix_mem_open hG hxG c` gives `s₀ > 0`; take `s := s₀ / 2` and `z := K4.mix s c x`.
Then `z ∈ G`, `z ∈ Simplex` (`K4.mix_mem_simplex`, `s ∈ [0,1]`), and
`z k = s / K + (1 - s) * x k ≥ s / K > 0`. -/
theorem exists_pos_mem_open {K : ℕ} (hK : 0 < K) {G : Set (Lot K)} (hG : IsOpen G)
    {x : Lot K} (hx : x ∈ Simplex K) (hxG : x ∈ G) :
    ∃ z ∈ Simplex K, z ∈ G ∧ ∀ k, 0 < z k := by
  set c : Lot K := fun _ => 1 / (K : ℝ) with hc
  have hKpos : (0 : ℝ) < K := by exact_mod_cast hK
  have hcS : c ∈ Simplex K := by
    refine ⟨fun i => by simp only [hc]; positivity, ?_⟩
    simp only [hc, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
  obtain ⟨s₀, hs₀, hs₁, hmix⟩ := exists_mix_mem_open hG hxG c
  have hs : 0 < s₀ / 2 := by positivity
  refine ⟨K4.mix (s₀ / 2) c x, K4.mix_mem_simplex hcS hx hs.le (by linarith),
    hmix _ hs.le (by linarith), fun k => ?_⟩
  have hxk : 0 ≤ x k := hx.1 k
  have h1 : 0 ≤ 1 - s₀ / 2 := by linarith
  show 0 < (s₀ / 2) * c k + (1 - s₀ / 2) * x k
  have : 0 < (s₀ / 2) * c k := by simp only [hc]; positivity
  nlinarith [mul_nonneg h1 hxk]

end Q3L
