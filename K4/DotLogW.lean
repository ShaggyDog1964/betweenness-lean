import K4.Defs
import K4.EdgeLotsEq

namespace K4

private theorem dot_rLot_eq {K : ℕ} (w : Lot K) (i j : ℕ) (hi : i < K) (hj : j < K)
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

private theorem sign_key (X Y : ℤ) (c : ℕ) :
    (0 < -((2 : ℝ) ^ Y) * ((2 : ℝ) ^ c / ((2 : ℝ) ^ c + 1)) +
        (2 : ℝ) ^ X * (1 / ((2 : ℝ) ^ c + 1)) ↔ (c : ℤ) < X - Y) ∧
      (-((2 : ℝ) ^ Y) * ((2 : ℝ) ^ c / ((2 : ℝ) ^ c + 1)) +
        (2 : ℝ) ^ X * (1 / ((2 : ℝ) ^ c + 1)) < 0 ↔ X - Y < (c : ℤ)) := by
  have hx : (0 : ℝ) < (2 : ℝ) ^ c + 1 := by positivity
  have heq : -((2 : ℝ) ^ Y) * ((2 : ℝ) ^ c / ((2 : ℝ) ^ c + 1)) +
      (2 : ℝ) ^ X * (1 / ((2 : ℝ) ^ c + 1)) =
      ((2 : ℝ) ^ X - (2 : ℝ) ^ (Y + (c : ℤ))) / ((2 : ℝ) ^ c + 1) := by
    rw [zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0), zpow_natCast]
    field_simp
    ring
  rw [heq]
  constructor
  · rw [div_pos_iff_of_pos_right hx, sub_pos,
      zpow_lt_zpow_iff_right₀ (by norm_num : (1 : ℝ) < 2)]
    omega
  · rw [div_neg_iff, sub_neg, zpow_lt_zpow_iff_right₀ (by norm_num : (1 : ℝ) < 2)]
    constructor
    · rintro (⟨_, h⟩ | ⟨h, _⟩)
      · exact absurd h (not_lt.mpr hx.le)
      · omega
    · intro h; exact Or.inr ⟨by omega, hx⟩

/-- Side of a family lottery relative to a log tilt: `P[c]` is above iff `c < L3 - L1`,
`Q[c]` iff `c < L3 - L2`, `R[c]` iff `c < L4 - L2` (and below iff the reverse strict
inequality).
Sketch: only two coordinates of `ekLot K e c` are nonzero, so (`Finset.sum_eq_add_of_mem`
style, or `Fin.sum_univ_succ` after `K = (K - 4) + 4`) e.g. for `P`:
`dot = (2^L3 - 2^L1 * 2^c) / (2^c + 1)`; its sign is that of `2^L3 - 2^(L1 + c)`
(`zpow_add₀`, `zpow_natCast`), i.e. of `L3 - (L1 + c)` (`zpow_lt_zpow_iff_right₀`).
`Q` uses coordinates 1, 2 and `R` uses 1, 3 (coordinate 3 of `logW` is `2^L4 + 0`). -/
theorem dot_logW_ekLot {K : ℕ} (hK : 4 ≤ K) (L1 L2 L3 L4 : ℤ) (e : EK) (c : ℕ) :
    (0 < dot (logW K L1 L2 L3 L4) (ekLot K e c) ↔
        (c : ℤ) < ekSel e (L3 - L1) (L3 - L2) (L4 - L2)) ∧
      (dot (logW K L1 L2 L3 L4) (ekLot K e c) < 0 ↔
        ekSel e (L3 - L1) (L3 - L2) (L4 - L2) < (c : ℤ)) := by
  obtain ⟨hP, hQ, hR⟩ := edge_lots_eq_rLot K c
  cases e with
  | P =>
    simp only [ekLot, ekSel, hP]
    rw [dot_rLot_eq _ 0 2 (by omega) (by omega) (by omega)]
    simpa [logW] using sign_key L3 L1 c
  | Q =>
    simp only [ekLot, ekSel, hQ]
    rw [dot_rLot_eq _ 1 2 (by omega) (by omega) (by omega)]
    simpa [logW] using sign_key L3 L2 c
  | R =>
    simp only [ekLot, ekSel, hR]
    rw [dot_rLot_eq _ 1 3 (by omega) (by omega) (by omega)]
    simpa [logW] using sign_key L4 L2 c

end K4
