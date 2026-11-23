/-
`exists_mix_mem_open`: small mixtures toward any point stay in an open set.
-/
import Q3L.Statement

namespace Q3L

open K4 (Lot)

/-- If `p ∈ G` with `G` open, then `K4.mix s z p ∈ G` for all `s ∈ [0, s₀)`, some
`s₀ ∈ (0, 1]`.
Sketch. `s ↦ K4.mix s z p = s • z + (1 - s) • p` is continuous (`continuity`/`fun_prop`) and
equals `p` at `s = 0`. Its preimage of `G` is an open set containing `0`, so it contains
`Metric.ball 0 ε` for some `ε > 0` (`Metric.isOpen_iff`). Take `s₀ := min ε 1`. -/
theorem exists_mix_mem_open {K : ℕ} {G : Set (Lot K)} (hG : IsOpen G) {p : Lot K}
    (hp : p ∈ G) (z : Lot K) :
    ∃ s₀ : ℝ, 0 < s₀ ∧ s₀ ≤ 1 ∧ ∀ s : ℝ, 0 ≤ s → s < s₀ → K4.mix s z p ∈ G := by
  have hc : Continuous (fun s : ℝ => K4.mix s z p) := by
    unfold K4.mix
    fun_prop
  have hO : IsOpen ((fun s : ℝ => K4.mix s z p) ⁻¹' G) := hG.preimage hc
  have h0 : (0 : ℝ) ∈ (fun s : ℝ => K4.mix s z p) ⁻¹' G := by
    simp [K4.mix, hp]
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hO 0 h0
  refine ⟨min ε 1, lt_min hε one_pos, min_le_right _ _, fun s hs hs₀ => ?_⟩
  apply hball
  rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_nonneg hs]
  exact lt_of_lt_of_le hs₀ (min_le_left _ _)

end Q3L
