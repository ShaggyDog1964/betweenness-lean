import Odds.Defs
import Odds.EdgeLotsBEq

namespace Odds

open K4

private theorem dot_rLotB_eq {K : ℕ} (w : Lot K) (i j : ℕ) (hi : i < K) (hj : j < K)
    (hij : i ≠ j) (x : ℝ) :
    dot w (rLot K i j x) = w ⟨i, hi⟩ * (x / (x + 1)) + w ⟨j, hj⟩ * (1 / (x + 1)) := by
  unfold dot
  rw [Finset.sum_eq_add (⟨i, hi⟩ : Fin K) ⟨j, hj⟩ (fun h => hij (congrArg Fin.val h))]
  · simp [rLot, Ne.symm hij]
  · intro k _ hk
    have h1 : k.val ≠ i := fun h => hk.1 (Fin.ext h)
    have h2 : k.val ≠ j := fun h => hk.2 (Fin.ext h)
    simp [rLot, h1, h2]
  · intro h; exact absurd (Finset.mem_univ _) h
  · intro h; exact absurd (Finset.mem_univ _) h

private theorem sign_keyB {b : ℝ} (hb : 1 < b) (X Y : ℤ) (c : ℕ) :
    (0 < -(b ^ Y) * (b ^ c / (b ^ c + 1)) + b ^ X * (1 / (b ^ c + 1)) ↔ (c : ℤ) < X - Y) ∧
      (-(b ^ Y) * (b ^ c / (b ^ c + 1)) + b ^ X * (1 / (b ^ c + 1)) < 0 ↔
        X - Y < (c : ℤ)) := by
  have hb0 : (0 : ℝ) < b := by linarith
  have hx : (0 : ℝ) < b ^ c + 1 := by positivity
  have heq : -(b ^ Y) * (b ^ c / (b ^ c + 1)) + b ^ X * (1 / (b ^ c + 1)) =
      (b ^ X - b ^ (Y + (c : ℤ))) / (b ^ c + 1) := by
    rw [zpow_add₀ hb0.ne', zpow_natCast]
    field_simp
    ring
  rw [heq]
  constructor
  · rw [div_pos_iff_of_pos_right hx, sub_pos, zpow_lt_zpow_iff_right₀ hb]
    omega
  · rw [div_neg_iff, sub_neg, zpow_lt_zpow_iff_right₀ hb]
    constructor
    · rintro (⟨_, h⟩ | ⟨h, _⟩)
      · exact absurd h (not_lt.mpr hx.le)
      · omega
    · intro h; exact Or.inr ⟨by omega, hx⟩

/-- Side of a base-`b` family lottery relative to a base-`b` log tilt (`b > 1`):
`P[c]` is above iff `c < L3 - L1`, `Q[c]` iff `c < L3 - L2`, `R[c]` iff `c < L4 - L2`, and
below iff the reverse strict inequality. -/
theorem dot_logWB_ekLotB {K : ℕ} (hK : 4 ≤ K) {b : ℝ} (hb : 1 < b) (L1 L2 L3 L4 : ℤ)
    (e : EK) (c : ℕ) :
    (0 < dot (logWB b K L1 L2 L3 L4) (ekLotB b K e c) ↔
        (c : ℤ) < ekSel e (L3 - L1) (L3 - L2) (L4 - L2)) ∧
      (dot (logWB b K L1 L2 L3 L4) (ekLotB b K e c) < 0 ↔
        ekSel e (L3 - L1) (L3 - L2) (L4 - L2) < (c : ℤ)) := by
  obtain ⟨hP, hQ, hR⟩ := edge_lotsB_eq_rLot b K c
  cases e with
  | P =>
    simp only [ekLotB, ekSel, hP]
    rw [dot_rLotB_eq _ 0 2 (by omega) (by omega) (by omega)]
    simpa [logWB] using sign_keyB hb L3 L1 c
  | Q =>
    simp only [ekLotB, ekSel, hQ]
    rw [dot_rLotB_eq _ 1 2 (by omega) (by omega) (by omega)]
    simpa [logWB] using sign_keyB hb L3 L2 c
  | R =>
    simp only [ekLotB, ekSel, hR]
    rw [dot_rLotB_eq _ 1 3 (by omega) (by omega) (by omega)]
    simpa [logWB] using sign_keyB hb L4 L2 c

end Odds
