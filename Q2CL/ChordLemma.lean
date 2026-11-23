import Q2CL.Defs

namespace Q2CL

open K4

private lemma chord_core (t1 t2 H1 H2 U S k : ℝ) (ht1 : 0 ≤ t1) (ht : t1 < t2) (ht2 : t2 ≤ 1)
    (hk : k * (t2 - t1) = H2 - H1)
    (hC0 : 0 < H1 - k * t1) (hC1 : 0 < H1 - k * t1 + k) :
    ((U * (1 - t1) + S * t1 < H1 → H2 < U * (1 - t2) + S * t2 →
      U * (H1 - k * t1 + k) < (H1 - k * t1) * S)) ∧
    ((H1 < U * (1 - t1) + S * t1 → U * (1 - t2) + S * t2 < H2 →
      (H1 - k * t1) * S < U * (H1 - k * t1 + k))) := by
  have hd : 0 < t2 - t1 := by linarith
  have hH1 : 0 < H1 := by nlinarith
  have hH2 : 0 < H2 := by nlinarith
  have hb : ((S - U) - k) * (t2 - t1) =
      (U * (1 - t2) + S * t2 - H2) - (U * (1 - t1) + S * t1 - H1) := by linear_combination (-1 : ℝ) * hk
  constructor
  · intro h1 h2
    have hbp : 0 < (S - U) - k := by
      by_contra hc; rw [not_lt] at hc; nlinarith [mul_nonpos_of_nonpos_of_nonneg hc hd.le]
    rcases le_or_gt 0 k with hk0 | hk0
    · nlinarith [mul_nonpos_of_nonpos_of_nonneg (by linarith : U * (1 - t1) + S * t1 - H1 ≤ 0) hk0,
        mul_pos hbp hH1]
    · nlinarith [mul_neg_of_pos_of_neg (by linarith : 0 < U * (1 - t2) + S * t2 - H2) hk0,
        mul_pos hbp hH2]
  · intro h1 h2
    have hbn : (S - U) - k < 0 := by
      by_contra hc; rw [not_lt] at hc; nlinarith [mul_nonneg hc hd.le]
    rcases le_or_gt 0 k with hk0 | hk0
    · nlinarith [mul_nonneg (by linarith : 0 ≤ U * (1 - t1) + S * t1 - H1) hk0,
        mul_neg_of_neg_of_pos hbn hH1]
    · nlinarith [mul_pos_of_neg_of_neg (by linarith : U * (1 - t2) + S * t2 - H2 < 0) hk0,
        mul_neg_of_neg_of_pos hbn hH2]

/-- Lemma 77 (chord lemma). `C` is the chord through `(t1, H1)`, `(t2, H2)`, written as
`C(t) = C0 (1-t) + C1 t`, positive at both ends; `L(t) = U(1-t) + S t` with `S > 0`. -/
theorem chord_lemma (t1 t2 H1 H2 U S : ℝ) (ht1 : 0 ≤ t1) (ht : t1 < t2) (ht2 : t2 ≤ 1)
    (hS : 0 < S)
    (hC0 : 0 < H1 - (H2 - H1) / (t2 - t1) * t1)
    (hC1 : 0 < H1 - (H2 - H1) / (t2 - t1) * t1 + (H2 - H1) / (t2 - t1)) :
    ((U * (1 - t1) + S * t1 < H1 → H2 < U * (1 - t2) + S * t2 →
      U / S < (H1 - (H2 - H1) / (t2 - t1) * t1) /
        (H1 - (H2 - H1) / (t2 - t1) * t1 + (H2 - H1) / (t2 - t1)))) ∧
    ((H1 < U * (1 - t1) + S * t1 → U * (1 - t2) + S * t2 < H2 →
      (H1 - (H2 - H1) / (t2 - t1) * t1) /
        (H1 - (H2 - H1) / (t2 - t1) * t1 + (H2 - H1) / (t2 - t1)) < U / S)) := by
  have hd : (t2 - t1) ≠ 0 := by linarith
  have hk : (H2 - H1) / (t2 - t1) * (t2 - t1) = H2 - H1 := div_mul_cancel₀ _ hd
  generalize (H2 - H1) / (t2 - t1) = k at hk hC0 hC1 ⊢
  obtain ⟨c1, c2⟩ := chord_core t1 t2 H1 H2 U S k ht1 ht ht2 hk hC0 hC1
  refine ⟨fun h1 h2 => ?_, fun h1 h2 => ?_⟩
  · rw [div_lt_div_iff₀ hS hC1]; exact c1 h1 h2
  · rw [div_lt_div_iff₀ hC1 hS]; linarith [c2 h1 h2]

end Q2CL
