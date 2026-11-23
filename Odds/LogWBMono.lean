import Odds.Defs

namespace Odds

open K4

/-- The base-`b` log tilt vector is coordinatewise monotone in `(-L1, -L2, L3, L4)`.
Sketch: copy `K4.logW_mono` (file `K4/LogWMono.lean`) with `2` replaced by `b`: `intro k`,
`unfold logWB`, `split_ifs`; `zpow_le_zpow_right₀ hb.le` and `neg_le_neg`,
`add_le_add_left`. -/
theorem logWB_mono {K : ℕ} {b : ℝ} (hb : 1 < b) {L1 L2 L3 L4 M1 M2 M3 M4 : ℤ}
    (h1 : M1 ≤ L1) (h2 : M2 ≤ L2) (h3 : L3 ≤ M3) (h4 : L4 ≤ M4) :
    logWB b K L1 L2 L3 L4 ≤ logWB b K M1 M2 M3 M4 := by
  have hble : (1 : ℝ) ≤ b := hb.le
  intro k
  unfold logWB
  split_ifs
  · exact neg_le_neg (zpow_le_zpow_right₀ hble h1)
  · exact neg_le_neg (zpow_le_zpow_right₀ hble h2)
  · exact zpow_le_zpow_right₀ hble h3
  · exact add_le_add_left (zpow_le_zpow_right₀ hble h4) _

end Odds
