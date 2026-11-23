import Q2CL.Defs

namespace Q2CL

open K4

/-- Polynomial core of `BET(0) ≥ 13/250`. -/
private lemma bet0_poly (u δ : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1 / 5) (hu0 : 0 ≤ u)
    (hu1 : u ≤ 1 - δ) :
    0 < 3 * fa' u δ * (17 / 20 * (fb u - fa' u δ) * (fb' u δ - fa u) + (fb u - fa' u δ)
        + (fb' u δ - fa u))
      + 4 * fb u * (fb u - fa' u δ) * (1053 / 1000 * (fb' u δ - fa u) - 3 / 20
        - 17 / 20 * fb' u δ) := by
  unfold fa' fa fb' fb
  nlinarith [mul_nonneg hu0 hδ0, mul_nonneg hu0 hu0, mul_nonneg hδ0 hδ0,
    mul_nonneg (mul_nonneg hu0 hu0) hu0, mul_nonneg (mul_nonneg hu0 hu0) hδ0,
    mul_nonneg (mul_nonneg hu0 hδ0) hδ0, mul_nonneg (mul_nonneg hδ0 hδ0) hδ0,
    mul_nonneg hu0 (sub_nonneg.2 hδ1), mul_nonneg hδ0 (sub_nonneg.2 hδ1),
    mul_nonneg hu0 (sub_nonneg.2 hu1), mul_nonneg hδ0 (sub_nonneg.2 hu1)]

/-- Polynomial core of `c1 ≥ 51/100`. -/
private lemma c1_poly (u δ : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1 / 5) (hu0 : 0 ≤ u)
    (hu1 : u ≤ 1 - δ) :
    0 < (4 * fb u - 3 * fa' u δ) * (fb u - fa' u δ) - 3 * fa' u δ * (fb' u δ - fa u)
      - 51 / 100 * 4 * fb u * (fb u - fa' u δ) * (fb' u δ - fa u) := by
  unfold fa' fa fb' fb
  nlinarith [mul_nonneg hu0 hδ0, mul_nonneg hu0 hu0, mul_nonneg hδ0 hδ0,
    mul_nonneg (mul_nonneg hu0 hu0) hu0, mul_nonneg (mul_nonneg hu0 hu0) hδ0,
    mul_nonneg (mul_nonneg hu0 hδ0) hδ0, mul_nonneg (mul_nonneg hδ0 hδ0) hδ0,
    mul_nonneg hu0 (sub_nonneg.2 hδ1), mul_nonneg hδ0 (sub_nonneg.2 hδ1),
    mul_nonneg hu0 (sub_nonneg.2 hu1), mul_nonneg hδ0 (sub_nonneg.2 hu1)]

set_option maxHeartbeats 1000000 in
/-- Lemma 83(1): the rate bounds BET and KAP are positive. -/
theorem face_rate (u δ x : ℝ) (h : GadDom u δ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 75) :
    0 < fBET u δ x ∧ 0 < fKAP u δ x := by
  obtain ⟨hδ0, hδ1, hu0, hu1⟩ := h
  have hb : 31 / 50 ≤ fb u := by unfold fb; linarith
  have hb1 : fb u ≤ 49 / 50 := by unfold fb; linarith
  have hb'0 : 31 / 50 ≤ fb' u δ := by unfold fb' fb; linarith
  have hb'1 : fb' u δ ≤ 49 / 50 := by unfold fb' fb; linarith
  have ha0 : 0 ≤ fa u := by unfold fa; linarith
  have ha1 : fa u ≤ 3 / 10 := by unfold fa; linarith
  have ha'0 : 0 ≤ fa' u δ := by unfold fa' fa; linarith
  have ha'1 : fa' u δ ≤ 3 / 10 := by unfold fa' fa; linarith
  have h3a : 3 * fa' u δ ≤ fb u := by unfold fa' fa fb; linarith
  have hp : 68 / 125 ≤ fb u - fa' u δ := by unfold fb fa' fa; linarith
  have hq : 3 / 5 ≤ fb' u δ - fa u := by unfold fb' fb fa; linarith
  have hbq : fb' u δ = (fb' u δ - fa u) + fa u := by ring
  have hbpos : 0 < fb u := by linarith
  have hppos : 0 < fb u - fa' u δ := by linarith
  have hqpos : 0 < fb' u δ - fa u := by linarith
  set ε := feps u δ with hεdef
  have hεb : ε * fb u = 3 / 4 * fa' u δ := by
    rw [hεdef]; unfold feps; field_simp
  have hε0 : 0 ≤ ε := by nlinarith
  have hε1 : ε ≤ 1 / 4 := by nlinarith
  -- closed forms
  have eα0 : falpha u δ 0 = ε * fb u / (fb u - fa' u δ) := by
    unfold falpha fsA; rw [← hεdef]; field_simp; ring
  have eα1 : falpha u δ 1 = -(ε * (1 - fb u)) / (fb u - fa' u δ) := by
    unfold falpha fsA; rw [← hεdef]; field_simp
  have eβ0 : fbeta u δ 0 = -1 + (1 - ε) * fb' u δ / (fb' u δ - fa u) := by
    unfold fbeta fsB; rw [← hεdef]; field_simp; ring
  have eβ1 : fbeta u δ 1 = -1 - (1 - ε) * (1 - fb' u δ) / (fb' u δ - fa u) := by
    unfold fbeta fsB; rw [← hεdef]; field_simp; ring
  have ec1 : fc1 u δ = (1 - ε) / (fb' u δ - fa u) - ε / (fb u - fa' u δ) := by
    unfold fc1 fbeta falpha fsA fsB; rw [← hεdef]; field_simp; ring
  have ed : fd u δ = 13 / 10 + (1 - fb' u δ) / (fb' u δ - fa u) + ε := by
    unfold fd; rw [← hεdef]
  -- bounds
  have hA0 : 0 ≤ falpha u δ 0 := by rw [eα0]; positivity
  have hA0' : falpha u δ 0 ≤ 21 / 50 := by
    rw [eα0, div_le_iff₀ hppos, hεb]; nlinarith
  have hA1 : falpha u δ 1 ≤ 0 := by
    rw [eα1, neg_div]; apply neg_nonpos.2; apply div_nonneg _ hppos.le
    exact mul_nonneg hε0 (by linarith)
  have hA1' : -(9 / 50) ≤ falpha u δ 1 := by
    rw [eα1, neg_div, neg_le_neg_iff, div_le_iff₀ hppos]
    nlinarith [mul_le_mul hε1 (show 1 - fb u ≤ 19 / 50 by linarith) (by linarith) (by norm_num)]
  have hB0 : -(1 / 4) ≤ fbeta u δ 0 := by
    rw [eβ0]
    have : 3 / 4 ≤ (1 - ε) * fb' u δ / (fb' u δ - fa u) := by
      rw [le_div_iff₀ hqpos]; nlinarith
    linarith
  have hB0' : fbeta u δ 0 ≤ 1 / 2 := by
    rw [eβ0]
    have : (1 - ε) * fb' u δ / (fb' u δ - fa u) ≤ 3 / 2 := by
      rw [div_le_iff₀ hqpos]; nlinarith
    linarith
  have hB1 : fbeta u δ 1 ≤ -1 := by
    rw [eβ1]
    have : 0 ≤ (1 - ε) * (1 - fb' u δ) / (fb' u δ - fa u) := by
      apply div_nonneg _ hqpos.le; exact mul_nonneg (by linarith) (by linarith)
    linarith
  have hB1' : -(41 / 25) ≤ fbeta u δ 1 := by
    rw [eβ1]
    have : (1 - ε) * (1 - fb' u δ) / (fb' u δ - fa u) ≤ 16 / 25 := by
      rw [div_le_iff₀ hqpos]
      nlinarith [mul_nonneg hε0 (show 0 ≤ 1 - fb' u δ by linarith)]
    linarith
  have hD0 : 13 / 10 ≤ fd u δ := by
    rw [ed]
    have : 0 ≤ (1 - fb' u δ) / (fb' u δ - fa u) := div_nonneg (by linarith) hqpos.le
    linarith
  have hD1 : fd u δ ≤ 11 / 5 := by
    rw [ed]
    have : (1 - fb' u δ) / (fb' u δ - fa u) ≤ 16 / 25 := by
      rw [div_le_iff₀ hqpos]; nlinarith
    linarith
  have hc2 : fc2 u δ ≤ 37 / 50 := by
    unfold fc2; nlinarith [mul_nonneg (by linarith : 0 ≤ fbeta u δ 0 + 1 / 4) (neg_nonneg.2 hA1),
      mul_nonneg hA0 (by linarith : 0 ≤ fbeta u δ 1 + 41 / 25)]
  have hc2' : -(9 / 100) ≤ fc2 u δ := by
    unfold fc2; nlinarith [mul_nonneg (by linarith : 0 ≤ 1 / 2 - fbeta u δ 0) (neg_nonneg.2 hA1),
      mul_nonneg hA0 (by linarith : 0 ≤ -fbeta u δ 1)]
  -- the two polynomial facts
  have hBET0 : 13 / 250 ≤ 17 / 20 * fd u δ - fc1 u δ := by
    have hP := bet0_poly u δ hδ0 hδ1 hu0 hu1
    have hid : 17 / 20 * fd u δ - fc1 u δ - 13 / 250 =
        (3 * fa' u δ * (17 / 20 * (fb u - fa' u δ) * (fb' u δ - fa u) + (fb u - fa' u δ)
          + (fb' u δ - fa u))
        + 4 * fb u * (fb u - fa' u δ) * (1053 / 1000 * (fb' u δ - fa u) - 3 / 20
          - 17 / 20 * fb' u δ)) / (4 * fb u * (fb u - fa' u δ) * (fb' u δ - fa u)) := by
      rw [ed, ec1, hεdef]; unfold feps; field_simp; ring
    have : 0 ≤ 17 / 20 * fd u δ - fc1 u δ - 13 / 250 := by rw [hid]; positivity
    linarith
  have hC1 : 51 / 100 ≤ fc1 u δ := by
    have hP := c1_poly u δ hδ0 hδ1 hu0 hu1
    have hid : fc1 u δ - 51 / 100 =
        ((4 * fb u - 3 * fa' u δ) * (fb u - fa' u δ) - 3 * fa' u δ * (fb' u δ - fa u)
          - 51 / 100 * 4 * fb u * (fb u - fa' u δ) * (fb' u δ - fa u))
          / (4 * fb u * (fb u - fa' u δ) * (fb' u δ - fa u)) := by
      rw [ec1, hεdef]; unfold feps; field_simp
    have : 0 ≤ fc1 u δ - 51 / 100 := by rw [hid]; positivity
    linarith
  -- absorb the x-terms
  set A0 := falpha u δ 0
  set B1 := fbeta u δ 1
  set D := fd u δ
  have hxB : 0 ≤ 1 + x * B1 := by nlinarith
  have hQlo : 1 + x * B1 ≤ (1 + x * A0) * (1 + x * B1) := by
    nlinarith [mul_nonneg (mul_nonneg hx0 hA0) hxB]
  have hQhi : (1 + x * A0) * (1 + x * B1) ≤ 1 + x * A0 := by
    nlinarith [mul_nonneg (by nlinarith : 0 ≤ 1 + x * A0) (mul_nonneg hx0 (by linarith : 0 ≤ -B1))]
  constructor
  · unfold fBET
    have h1 : D * (1 + x * B1) ≤ D * ((1 + x * A0) * (1 + x * B1)) :=
      mul_le_mul_of_nonneg_left hQlo (by linarith)
    have h2 : D * (x * B1) ≥ -(11 / 5 * 41 / 25) * x := by
      nlinarith [mul_nonneg (mul_nonneg hx0 (by linarith : (0:ℝ) ≤ 11 / 5 - D))
        (by linarith : (0:ℝ) ≤ -B1), mul_nonneg hx0 (by linarith : 0 ≤ B1 + 41 / 25)]
    have h3 : x * fc2 u δ ≤ 37 / 50 * x := by nlinarith
    nlinarith
  · unfold fKAP
    have h3 : -(9 / 100) * x ≤ x * fc2 u δ := by nlinarith
    have h4 : x * A0 ≤ 21 / 50 * x := by nlinarith
    nlinarith

end Q2CL
