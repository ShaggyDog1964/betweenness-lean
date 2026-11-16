import K4.Defs

namespace K4

/-- The log tilt vector as a function of a natural-number index. -/
private noncomputable def logWNat (L1 L2 L3 L4 : ℤ) (k : ℕ) : ℝ :=
  if k = 0 then -((2 : ℝ) ^ L1)
  else if k = 1 then -((2 : ℝ) ^ L2)
  else if k = 2 then (2 : ℝ) ^ L3
  else (2 : ℝ) ^ L4 + ((k : ℝ) - 3)

private theorem logWNat_strictMono {L1 L2 L3 L4 : ℤ} (h12 : L2 < L1) (h34 : L3 < L4) :
    StrictMono (logWNat L1 L2 L3 L4) := by
  apply strictMono_nat_of_lt_succ
  intro n
  have two : (1 : ℝ) < 2 := by norm_num
  have p2 : (0 : ℝ) < (2 : ℝ) ^ L2 := zpow_pos (by norm_num) _
  have p3 : (0 : ℝ) < (2 : ℝ) ^ L3 := zpow_pos (by norm_num) _
  have a12 : (2 : ℝ) ^ L2 < (2 : ℝ) ^ L1 := zpow_lt_zpow_right₀ two h12
  have a34 : (2 : ℝ) ^ L3 < (2 : ℝ) ^ L4 := zpow_lt_zpow_right₀ two h34
  unfold logWNat
  rcases n with _ | _ | _ | n
  · simp; linarith
  · simp; linarith
  · simp; linarith
  · have h1 : n + 1 + 1 + 1 ≠ 0 := by omega
    have h2 : n + 1 + 1 + 1 ≠ 1 := by omega
    have h3 : n + 1 + 1 + 1 ≠ 2 := by omega
    have h1' : n + 1 + 1 + 1 + 1 ≠ 0 := by omega
    have h2' : n + 1 + 1 + 1 + 1 ≠ 1 := by omega
    have h3' : n + 1 + 1 + 1 + 1 ≠ 2 := by omega
    simp only [h1, h2, h3, h1', h2', h3', ite_false]
    push_cast
    linarith

/-- The log tilt vector has strictly increasing coordinates when `L2 < L1` and `L3 < L4`.
Sketch: it suffices to compare consecutive indices (`Fin.strictMono_iff_lt_succ`). Values:
`-2^L1 < -2^L2` (`zpow_lt_zpow_right₀`, base `2 > 1`), `-2^L2 < 0 < 2^L3`,
`2^L3 < 2^L4 = 2^L4 + (3 - 3)`, and `2^L4 + (k - 3) < 2^L4 + (k + 1 - 3)` for `k ≥ 3`. -/
theorem logW_strictMono {K : ℕ} {L1 L2 L3 L4 : ℤ} (h12 : L2 < L1) (h34 : L3 < L4) :
    StrictMono (logW K L1 L2 L3 L4) := by
  intro a b hab
  have h := logWNat_strictMono h12 h34 (show a.val < b.val from hab)
  simpa [logW, logWNat] using h

end K4
