import Q2CL.Defs

namespace Q2CL

open K4

set_option maxHeartbeats 4000000

/-- `P · 4 b D1 D2`, with `D1 = b - a'`, `D2 = b' - a`. -/
private noncomputable def PM (u δ : ℝ) : ℝ :=
  3 * fa' u δ * fb u * (fb' u δ - fa u) +
    (3 * fa' u δ * fb' u δ - 4 * fa u * fb u) * (fb u - fa' u δ)

private noncomputable def MM (u δ : ℝ) : ℝ :=
  4 * fb u * (fb u - fa' u δ) * (fb' u δ - fa u)

private lemma dens (u δ : ℝ) (h : GadDom u δ) :
    0 < fb u ∧ 0 < fb u - fa' u δ ∧ 0 < fb' u δ - fa u := by
  obtain ⟨h0, h1, h2, h3⟩ := h
  simp only [fa, fa', fb, fb']
  refine ⟨by linarith, by linarith, by linarith⟩

private lemma P_eq (u δ : ℝ) (h : GadDom u δ) : fP u δ * MM u δ = PM u δ := by
  obtain ⟨hb, hD1, hD2⟩ := dens u δ h
  unfold fP falpha fbeta fsA fsB feps MM PM
  field_simp
  ring

private lemma PM_pos (u δ : ℝ) (h : GadDom u δ) : 0 < PM u δ := by
  obtain ⟨h0, h1, h2, h3⟩ := h
  have h4 : 0 ≤ 1 - δ - u := by linarith
  have h5 : 0 ≤ 1/5 - δ := by linarith
  unfold PM
  simp only [fa, fa', fb, fb']
  nlinarith [mul_nonneg h0 h2, mul_nonneg h0 h4, mul_nonneg h2 h4, mul_nonneg h0 h5,
    mul_nonneg h2 h5, mul_nonneg h4 h5, mul_nonneg h0 h0, mul_nonneg h2 h2,
    mul_nonneg (mul_nonneg h0 h2) h4, mul_nonneg (mul_nonneg h0 h2) h5,
    mul_nonneg (mul_nonneg h0 h4) h5, mul_nonneg (mul_nonneg h2 h4) h5]

private lemma L2a_pos (u δ : ℝ) (h : GadDom u δ) : 0 < fL2a u δ := by
  obtain ⟨hb, hD1, hD2⟩ := dens u δ h
  have hM : 0 < MM u δ := by unfold MM; positivity
  have key : fL2a u δ * MM u δ =
      -3 * fa' u δ * (fb' u δ - fb u) * (fb' u δ - fa u) + MM u δ - 2 * KC * PM u δ := by
    rw [← P_eq u δ h]
    unfold fL2a falpha fsA feps MM
    field_simp
  have hN : 0 < -3 * fa' u δ * (fb' u δ - fb u) * (fb' u δ - fa u) + MM u δ - 2 * KC * PM u δ := by
    obtain ⟨h0, h1, h2, h3⟩ := h
    have h4 : 0 ≤ 1 - δ - u := by linarith
    have h5 : 0 ≤ 1/5 - δ := by linarith
    unfold MM PM KC
    simp only [fa, fa', fb, fb']
    nlinarith [mul_nonneg h0 h2, mul_nonneg h0 h4, mul_nonneg h2 h4, mul_nonneg h0 h5,
      mul_nonneg h2 h5, mul_nonneg h4 h5, mul_nonneg h0 h0, mul_nonneg h2 h2,
      mul_nonneg (mul_nonneg h0 h2) h4, mul_nonneg (mul_nonneg h0 h2) h5,
      mul_nonneg (mul_nonneg h0 h4) h5, mul_nonneg (mul_nonneg h2 h4) h5]
  rw [← key] at hN
  exact (mul_pos_iff_of_pos_right hM).mp hN

private lemma L2b_pos (u δ : ℝ) (h : GadDom u δ) : 0 < fL2b u δ := by
  obtain ⟨hb, hD1, hD2⟩ := dens u δ h
  have hM : 0 < MM u δ := by unfold MM; positivity
  have key : fL2b u δ * MM u δ =
      3 * fa' u δ * (fb u - fa u) * (fb' u δ - fa u) +
        3 * fa' u δ * (fb u - fa' u δ) * (fb' u δ - fa u) - 2 * KC * PM u δ := by
    rw [← P_eq u δ h]
    unfold fL2b falpha fsA feps MM
    field_simp
    ring
  have hN : 0 < 3 * fa' u δ * (fb u - fa u) * (fb' u δ - fa u) +
        3 * fa' u δ * (fb u - fa' u δ) * (fb' u δ - fa u) - 2 * KC * PM u δ := by
    obtain ⟨h0, h1, h2, h3⟩ := h
    have h4 : 0 ≤ 1 - δ - u := by linarith
    have h5 : 0 ≤ 1/5 - δ := by linarith
    unfold PM KC
    simp only [fa, fa', fb, fb']
    nlinarith [mul_nonneg h0 h2, mul_nonneg h0 h4, mul_nonneg h2 h4, mul_nonneg h0 h5,
      mul_nonneg h2 h5, mul_nonneg h4 h5, mul_nonneg h0 h0, mul_nonneg h2 h2,
      mul_nonneg (mul_nonneg h0 h2) h4, mul_nonneg (mul_nonneg h0 h2) h5,
      mul_nonneg (mul_nonneg h0 h4) h5, mul_nonneg (mul_nonneg h2 h4) h5]
  rw [← key] at hN
  exact (mul_pos_iff_of_pos_right hM).mp hN

private lemma L2d_pos (u δ : ℝ) (h : GadDom u δ) : 0 < fL2d u δ := by
  obtain ⟨hb, hD1, hD2⟩ := dens u δ h
  have hM : 0 < MM u δ := by unfold MM; positivity
  have key : fL2d u δ * MM u δ =
      MM u δ + (3 * fa' u δ - 4 * fb u) * (fb' u δ - fb u) * (fb u - fa' u δ)
        - 2 * KC * PM u δ := by
    rw [← P_eq u δ h]
    unfold fL2d fbeta fsB feps MM
    field_simp
    ring
  have hN : 0 < MM u δ + (3 * fa' u δ - 4 * fb u) * (fb' u δ - fb u) * (fb u - fa' u δ)
        - 2 * KC * PM u δ := by
    obtain ⟨h0, h1, h2, h3⟩ := h
    have h4 : 0 ≤ 1 - δ - u := by linarith
    have h5 : 0 ≤ 1/5 - δ := by linarith
    unfold MM PM KC
    simp only [fa, fa', fb, fb']
    nlinarith [mul_nonneg h0 h2, mul_nonneg h0 h4, mul_nonneg h2 h4, mul_nonneg h0 h5,
      mul_nonneg h2 h5, mul_nonneg h4 h5, mul_nonneg h0 h0, mul_nonneg h2 h2,
      mul_nonneg (mul_nonneg h0 h2) h4, mul_nonneg (mul_nonneg h0 h2) h5,
      mul_nonneg (mul_nonneg h0 h4) h5, mul_nonneg (mul_nonneg h2 h4) h5]
  rw [← key] at hN
  exact (mul_pos_iff_of_pos_right hM).mp hN

private lemma L2c_pos (u δ x : ℝ) (h : GadDom u δ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 75) :
    0 < fL2c u δ x := by
  obtain ⟨hb, hD1, hD2⟩ := dens u δ h
  have hM : 0 < 4 * fb u * MM u δ := by unfold MM; positivity
  have key : fL2c u δ x * (4 * fb u * MM u δ) =
      4 * fb u * (3 * fa' u δ * (fb u - fa' u δ) * (fb' u δ - fa u) + MM u δ +
        (3 * fa' u δ - 4 * fb u) * (fb' u δ - fa' u δ) * (fb u - fa' u δ))
        - KC * (8 * fb u + 3 * x * fa' u δ) * PM u δ := by
    rw [← P_eq u δ h]
    unfold fL2c fbeta fsB feps MM
    field_simp
    ring
  have hPM := PM_pos u δ h
  have hQ : 0 < 4 * fb u * (3 * fa' u δ * (fb u - fa' u δ) * (fb' u δ - fa u) + MM u δ +
        (3 * fa' u δ - 4 * fb u) * (fb' u δ - fa' u δ) * (fb u - fa' u δ))
        - KC * (8 * fb u + 3 * (1 / 75) * fa' u δ) * PM u δ := by
    obtain ⟨h0, h1, h2, h3⟩ := h
    have h4 : 0 ≤ 1 - δ - u := by linarith
    have h5 : 0 ≤ 1/5 - δ := by linarith
    unfold MM PM KC
    simp only [fa, fa', fb, fb']
    nlinarith [mul_nonneg h0 h2, mul_nonneg h0 h4, mul_nonneg h2 h4, mul_nonneg h0 h5,
      mul_nonneg h2 h5, mul_nonneg h4 h5, mul_nonneg h0 h0, mul_nonneg h2 h2,
      mul_nonneg (mul_nonneg h0 h2) h4, mul_nonneg (mul_nonneg h0 h2) h5,
      mul_nonneg (mul_nonneg h0 h4) h5, mul_nonneg (mul_nonneg h2 h4) h5]
  have ha' : 0 ≤ fa' u δ := by
    obtain ⟨h0, h1, h2, h3⟩ := h
    simp only [fa', fa]; linarith
  have hx : 0 ≤ (1 / 75 - x) * (fa' u δ * PM u δ) :=
    mul_nonneg (by linarith) (mul_nonneg ha' hPM.le)
  have hKC : KC = 39 / 88 := rfl
  have hN : 0 < fL2c u δ x * (4 * fb u * MM u δ) := by
    rw [key, hKC]
    rw [hKC] at hQ
    nlinarith
  exact (mul_pos_iff_of_pos_right hM).mp hN

/-- Lemma 83(1): L2a, L2b, L2c, L2d are positive. -/
theorem face_L2 (u δ x : ℝ) (h : GadDom u δ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 75) :
    0 < fL2a u δ ∧ 0 < fL2b u δ ∧ 0 < fL2c u δ x ∧ 0 < fL2d u δ :=
  ⟨L2a_pos u δ h, L2b_pos u δ h, L2c_pos u δ x h hx0 hx1, L2d_pos u δ h⟩

end Q2CL
