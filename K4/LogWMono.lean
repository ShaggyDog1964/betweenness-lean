import K4.Defs

namespace K4

/-- The log tilt vector is coordinatewise monotone in `(-L1, -L2, L3, L4)`.
Sketch: `intro k`, unfold `logW`, split the `if`s; `zpow_le_zpow_right₀` (base `2 ≥ 1`)
and `neg_le_neg`. -/
theorem logW_mono {K : ℕ} {L1 L2 L3 L4 M1 M2 M3 M4 : ℤ} (h1 : M1 ≤ L1) (h2 : M2 ≤ L2)
    (h3 : L3 ≤ M3) (h4 : L4 ≤ M4) : logW K L1 L2 L3 L4 ≤ logW K M1 M2 M3 M4 := by
  have h2le : (1 : ℝ) ≤ 2 := by norm_num
  intro k
  unfold logW
  split_ifs
  · exact neg_le_neg (zpow_le_zpow_right₀ h2le h1)
  · exact neg_le_neg (zpow_le_zpow_right₀ h2le h2)
  · exact zpow_le_zpow_right₀ h2le h3
  · exact add_le_add_left (zpow_le_zpow_right₀ h2le h4) _

end K4
