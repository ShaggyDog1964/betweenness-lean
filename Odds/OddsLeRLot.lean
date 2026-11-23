import Odds.Defs

namespace Odds

open K4

/-- Odds of a two-point edge lottery with ratio `x ≥ 1`: `OddsLe M (rLot K i j x) ↔ x ≤ M`.
Sketch. Masses: `x/(x+1)` at `i`, `1/(x+1)` at `j`, `0` elsewhere; `x + 1 > 0`.
(→) Apply the hypothesis at the pair `(⟨i,hi⟩, ⟨j,hj⟩)`: `p j = 1/(x+1) > 0`, so
`x/(x+1) ≤ M * (1/(x+1))`; multiply by `x + 1` (`div_le_iff₀`, `field_simp`) to get
`x ≤ M`.
(←) Then `M ≥ x ≥ 1 > 0`. Take prizes `k, l` with `p l > 0`; `p l > 0` forces
`l.val = i` or `l.val = j` (otherwise `p l = 0`). Unfold `rLot` and `split_ifs` (using
`i ≠ j`):
`p k = 0`: `0 ≤ M * p l` (both nonnegative).
`k, l` same prize: `p ≤ M p` as `M ≥ 1`, `p ≥ 0`.
`k = i, l = j`: `x/(x+1) ≤ M/(x+1)` from `x ≤ M`.
`k = j, l = i`: `1/(x+1) ≤ M x/(x+1)` from `M x ≥ 1 * 1`.
(`div_le_div_of_nonneg_right`, `nlinarith`.) -/
theorem oddsLe_rLot {K i j : ℕ} (hij : i ≠ j) (hi : i < K) (hj : j < K) {x M : ℝ}
    (hx : 1 ≤ x) : OddsLe M (rLot K i j x) ↔ x ≤ M := by
  have hpos : (0 : ℝ) < x + 1 := by linarith
  constructor
  · intro h
    have h1 := h ⟨i, hi⟩ ⟨j, hj⟩
    have hji : j ≠ i := fun e => hij e.symm
    simp only [rLot, hji, ite_true, ite_false] at h1
    have h2 := h1 (by positivity)
    rw [mul_one_div, div_le_div_iff_of_pos_right hpos] at h2
    exact h2
  · intro hM k l hl
    simp only [rLot] at hl ⊢
    split_ifs at hl ⊢ <;>
      first
      | (exact absurd hl (lt_irrefl 0))
      | (rw [← mul_div_assoc, div_le_div_iff_of_pos_right hpos]; nlinarith)
      | (exact mul_nonneg (by linarith) hl.le)

end Odds
