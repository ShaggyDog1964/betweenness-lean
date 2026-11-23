import Odds.Defs

namespace Odds

/-- Every real `M > 1` is an `N`-th power of some real `b > 1` (`N ≥ 1`).
Sketch: `b = M ^ ((N : ℝ)⁻¹)` (`Real.rpow`). `b ^ N = M` by `Real.rpow_inv_natCast_pow`
(`0 ≤ M`, `N ≠ 0`). `1 < b` by `Real.one_lt_rpow hM (inv_pos.mpr (Nat.cast_pos.mpr _))`. -/
theorem exists_base_pow (M : ℝ) (hM : 1 < M) (N : ℕ) (hN : 1 ≤ N) :
    ∃ b : ℝ, 1 < b ∧ b ^ N = M := by
  have hN0 : N ≠ 0 := by omega
  refine ⟨M ^ ((N : ℝ)⁻¹), ?_, ?_⟩
  · exact Real.one_lt_rpow hM (inv_pos.mpr (Nat.cast_pos.mpr (by omega)))
  · exact Real.rpow_inv_natCast_pow (by linarith) hN0

end Odds
