import Q2CL.Defs

namespace Q2CL

open K4

private lemma dot_single' (w : Lot 4) (k : Fin 4) (c : ℝ) :
    dot w (Pi.single k c) = w k * c := by
  simp [dot, Pi.single_apply]

private lemma dot_add' (w p q : Lot 4) : dot w (p + q) = dot w p + dot w q := by
  simp [dot, mul_add, Finset.sum_add_distrib]

/-- Farkas step on the nonnegative orthant of `ℝ⁴`. -/
theorem farkas_step (W W' : Lot 4)
    (h : ∀ p : Lot 4, (∀ k, 0 ≤ p k) → 0 ≤ dot W p → 0 ≤ dot W' p)
    (hneg : ∃ p : Lot 4, (∀ k, 0 ≤ p k) ∧ dot W' p < 0) :
    ∃ a : ℝ, 0 < a ∧ ∀ k, a * W k ≤ W' k := by
  -- (A) nonnegative coordinates of W force nonnegative coordinates of W'
  have hA : ∀ k, 0 ≤ W k → 0 ≤ W' k := by
    intro k hk
    have hp : ∀ l, (0:ℝ) ≤ (Pi.single k (1:ℝ) : Lot 4) l := by
      intro l
      by_cases hl : l = k
      · subst hl; simp
      · simp [Pi.single_apply, hl]
    have := h _ hp (by rw [dot_single']; linarith)
    rw [dot_single'] at this
    linarith
  -- (B) pair inequality
  have hB : ∀ i j, W i < 0 → 0 < W j → W' j * W i ≤ W' i * W j := by
    intro i j hi hj
    have hij : i ≠ j := by
      intro e; subst e; linarith
    let p : Lot 4 := Pi.single i (W j) + Pi.single j (-W i)
    have hp : ∀ l, 0 ≤ p l := by
      intro l
      simp only [p, Pi.add_apply]
      by_cases hl : l = i
      · subst hl; simp [Pi.single_apply, hij]; linarith
      · by_cases hl2 : l = j
        · subst hl2; simp [Pi.single_apply, hl]; linarith
        · simp [Pi.single_apply, hl, hl2]
    have h0 : 0 ≤ dot W p := by
      simp only [p, dot_add', dot_single']; nlinarith
    have := h p hp h0
    simp only [p, dot_add', dot_single'] at this
    nlinarith
  -- (C) some coordinate of W' is negative
  have hC : ∃ k, W' k < 0 := by
    by_contra hc
    push_neg at hc
    obtain ⟨p, hp, hlt⟩ := hneg
    have : 0 ≤ dot W' p := Finset.sum_nonneg (fun k _ => mul_nonneg (hc k) (hp k))
    linarith
  obtain ⟨k0, hk0⟩ := hC
  have hWk0 : W k0 < 0 := by
    by_contra hc; push_neg at hc; linarith [hA k0 hc]
  have hne : (Finset.univ.filter (fun k => W k < 0)).Nonempty :=
    ⟨k0, by simp [hWk0]⟩
  obtain ⟨i0, hi0mem, hi0max⟩ :=
    Finset.exists_max_image (Finset.univ.filter (fun k => W k < 0))
      (fun k => W' k / W k) hne
  have hWi0 : W i0 < 0 := by simpa using hi0mem
  refine ⟨W' i0 / W i0, ?_, ?_⟩
  · have h1 : W' k0 / W k0 ≤ W' i0 / W i0 := hi0max k0 (by simp [hWk0])
    have h2 : 0 < W' k0 / W k0 := div_pos_of_neg_of_neg hk0 hWk0
    linarith
  · intro k
    rcases lt_trichotomy (W k) 0 with hk | hk | hk
    · have h1 : W' k / W k ≤ W' i0 / W i0 := hi0max k (by simp [hk])
      exact (div_le_iff_of_neg hk).1 h1
    · rw [hk, mul_zero]; exact hA k hk.ge
    · have hb := hB i0 k hWi0 hk
      rw [div_mul_eq_mul_div]
      exact (div_le_iff_of_neg hWi0).2 hb

end Q2CL
