import Odds.Defs

namespace Odds

open K4

/-- The base-`b` log tilt vector as a function of a natural-number index. -/
private noncomputable def logWBNat (b : ℝ) (L1 L2 L3 L4 : ℤ) (k : ℕ) : ℝ :=
  if k = 0 then -(b ^ L1)
  else if k = 1 then -(b ^ L2)
  else if k = 2 then b ^ L3
  else b ^ L4 + ((k : ℝ) - 3)

private theorem logWBNat_strictMono {b : ℝ} (hb : 1 < b) {L1 L2 L3 L4 : ℤ} (h12 : L2 < L1)
    (h34 : L3 < L4) : StrictMono (logWBNat b L1 L2 L3 L4) := by
  apply strictMono_nat_of_lt_succ
  intro n
  have p2 : (0 : ℝ) < b ^ L2 := zpow_pos (by linarith) _
  have p3 : (0 : ℝ) < b ^ L3 := zpow_pos (by linarith) _
  have a12 : b ^ L2 < b ^ L1 := zpow_lt_zpow_right₀ hb h12
  have a34 : b ^ L3 < b ^ L4 := zpow_lt_zpow_right₀ hb h34
  unfold logWBNat
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

/-- The base-`b` log tilt vector has strictly increasing coordinates when `b > 1`,
`L2 < L1` and `L3 < L4`. -/
theorem logWB_strictMono {K : ℕ} {b : ℝ} (hb : 1 < b) {L1 L2 L3 L4 : ℤ} (h12 : L2 < L1)
    (h34 : L3 < L4) : StrictMono (logWB b K L1 L2 L3 L4) := by
  intro x y hxy
  have h := logWBNat_strictMono hb h12 h34 (show x.val < y.val from hxy)
  simpa [logWB, logWBNat] using h

end Odds
