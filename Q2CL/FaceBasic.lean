import Q2CL.Defs

namespace Q2CL

open K4

private lemma fb_pos_of_scaled {s x y : ℝ} (hx : 0 < x) (hy : 0 < y) (h : 0 < s * x * y) :
    0 < s := by
  by_contra hc
  push Not at hc
  have hxy := mul_pos hx hy
  nlinarith [mul_nonneg (neg_nonneg.2 hc) hxy.le]

/-- Positivity of the cleared numerator of `P`, abstractly. -/
private lemma fb_P_num (A B δ : ℝ) (hd0 : 0 ≤ δ) (hA : 0 < A) (hB : 0 < B) (hBA : 0 < B - A)
    (hD1 : 0 < B - (A + 7 / 25 * δ)) :
    0 < 3 / 4 * (A + 7 / 25 * δ) * B * (B + 9 / 25 * δ - A)
          + (B - (A + 7 / 25 * δ)) * ((B + 9 / 25 * δ - A) * B - B * (B + 9 / 25 * δ)
            + 3 / 4 * (A + 7 / 25 * δ) * (B + 9 / 25 * δ)) := by
  have hI : 3 / 4 * (A + 7 / 25 * δ) * B * (B + 9 / 25 * δ - A)
      + (B - (A + 7 / 25 * δ)) * ((B + 9 / 25 * δ - A) * B - B * (B + 9 / 25 * δ)
        + 3 / 4 * (A + 7 / 25 * δ) * (B + 9 / 25 * δ))
      = 1 / 2 * A * B * (B - A)
        + 3 / 4 * B * ((7 / 25 * δ) * (B - A) + (7 / 25 * δ) * (9 / 25 * δ) + A * (9 / 25 * δ))
        + (B - (A + 7 / 25 * δ)) * (3 / 4 * (A * (9 / 25 * δ) + 7 / 25 * δ * B
          + 7 / 25 * δ * (9 / 25 * δ)))
        + 1 / 4 * A * B * (7 / 25 * δ) := by ring
  rw [hI]
  have t1 : 0 < 1 / 2 * A * B * (B - A) := by
    have := mul_pos (mul_pos hA hB) hBA; linarith
  have t2 : 0 ≤ 3 / 4 * B * ((7 / 25 * δ) * (B - A) + (7 / 25 * δ) * (9 / 25 * δ)
      + A * (9 / 25 * δ)) := by
    apply mul_nonneg (by positivity)
    have := mul_nonneg hd0 hBA.le
    have := mul_nonneg hA.le hd0
    have := mul_nonneg hd0 hd0
    linarith
  have t3 : 0 ≤ (B - (A + 7 / 25 * δ)) * (3 / 4 * (A * (9 / 25 * δ) + 7 / 25 * δ * B
      + 7 / 25 * δ * (9 / 25 * δ))) := by
    apply mul_nonneg hD1.le; positivity
  have t4 : 0 ≤ 1 / 4 * A * B * (7 / 25 * δ) := by positivity
  linarith

private lemma fb_dlo_num (u δ : ℝ) (hd0 : 0 ≤ δ) (hd1 : δ ≤ 1 / 5) (hu0 : 0 ≤ u)
    (hu1 : u ≤ 1 - δ) :
    0 < (1 - (31 / 50 + 9 / 25 * u + 9 / 25 * δ)) * (31 / 50 + 9 / 25 * u)
      + 3 / 4 * (1 / 50 + 7 / 25 * u + 7 / 25 * δ)
          * (31 / 50 + 9 / 25 * u + 9 / 25 * δ - (1 / 50 + 7 / 25 * u))
      - 1 / 5 * (31 / 50 + 9 / 25 * u + 9 / 25 * δ - (1 / 50 + 7 / 25 * u))
          * (31 / 50 + 9 / 25 * u) := by
  nlinarith [mul_nonneg hu0 hd0, mul_nonneg hu0 hu0, mul_nonneg hd0 hd0,
    mul_nonneg (sub_nonneg.2 hu1) hu0, mul_nonneg (sub_nonneg.2 hu1) hd0,
    mul_nonneg (sub_nonneg.2 hd1) hd0, mul_nonneg (sub_nonneg.2 hd1) hu0]

private lemma fb_dhi_num (u δ : ℝ) (hd0 : 0 ≤ δ) (hd1 : δ ≤ 1 / 5) (hu0 : 0 ≤ u)
    (hu1 : u ≤ 1 - δ) :
    0 < 4 / 5 * (31 / 50 + 9 / 25 * u + 9 / 25 * δ - (1 / 50 + 7 / 25 * u))
          * (31 / 50 + 9 / 25 * u)
      - (1 - (31 / 50 + 9 / 25 * u + 9 / 25 * δ)) * (31 / 50 + 9 / 25 * u)
      - 3 / 4 * (1 / 50 + 7 / 25 * u + 7 / 25 * δ)
          * (31 / 50 + 9 / 25 * u + 9 / 25 * δ - (1 / 50 + 7 / 25 * u)) := by
  nlinarith [mul_nonneg hu0 hd0, mul_nonneg hu0 hu0, mul_nonneg hd0 hd0,
    mul_nonneg (sub_nonneg.2 hu1) hu0, mul_nonneg (sub_nonneg.2 hu1) hd0,
    mul_nonneg (sub_nonneg.2 hd1) hd0, mul_nonneg (sub_nonneg.2 hd1) hu0]

/-- Lemma 83(1), simple gadget functions: EPS, N1, G3a0, G3a1, A1lo, B1lo, B1hi, Dyb, Dxb, the
two chord-denominators, and the drop bounds `3/2 < d < 21/10`. -/
theorem face_basic (u δ : ℝ) (h : GadDom u δ) :
    0 < feps u δ ∧ feps u δ < 1 ∧ 0 < fb u - fa' u δ ∧ 0 < fb' u δ - fa u ∧
    0 < fP u δ ∧ 0 < falpha u δ 1 - fbeta u δ 1 ∧
    -2 < falpha u δ 1 ∧ -2 < fbeta u δ 1 ∧ fbeta u δ 1 < 0 ∧
    3 / 2 < fd u δ ∧ fd u δ < 21 / 10 ∧ 0 < fDyb u δ ∧ 0 < fDxb u δ := by
  obtain ⟨hd0, hd1, hu0, hu1⟩ := h
  have hb : fb u = 31 / 50 + 9 / 25 * u := rfl
  have hb' : fb' u δ = 31 / 50 + 9 / 25 * u + 9 / 25 * δ := rfl
  have ha : fa u = 1 / 50 + 7 / 25 * u := rfl
  have ha' : fa' u δ = 1 / 50 + 7 / 25 * u + 7 / 25 * δ := rfl
  have hbpos : 0 < fb u := by rw [hb]; linarith
  have hD1 : 27 / 50 < fb u - fa' u δ := by rw [hb, ha']; linarith
  have hD2 : 3 / 5 ≤ fb' u δ - fa u := by rw [hb', ha]; linarith
  have hD1p : 0 < fb u - fa' u δ := by linarith
  have hD2p : 0 < fb' u δ - fa u := by linarith
  -- ε
  have heps : feps u δ * fb u = 3 / 4 * fa' u δ := by
    unfold feps; field_simp
  have he0 : 0 < feps u δ := by
    unfold feps; apply div_pos _ hbpos; rw [ha']; linarith
  have he1 : feps u δ < 37 / 100 := by
    unfold feps; rw [div_lt_iff₀ hbpos, ha', hb]; linarith
  -- slopes
  have hsA : fsA u δ * (fb u - fa' u δ) = -feps u δ := by
    unfold fsA; field_simp
  have hsB : fsB u δ * (fb' u δ - fa u) = feps u δ - 1 := by
    unfold fsB; field_simp
  have hsA0 : fsA u δ < 0 := by
    unfold fsA; exact div_neg_of_neg_of_pos (by linarith) hD1p
  have hsA1 : -(37 / 54) < fsA u δ := by nlinarith
  have hsB0 : fsB u δ < 0 := by
    unfold fsB; exact div_neg_of_neg_of_pos (by linarith) hD2p
  have hsB1 : -(5 / 3) ≤ fsB u δ := by nlinarith
  have h1b' : 0 ≤ 1 - fb' u δ := by rw [hb']; linarith
  have h1b'' : 1 - fb' u δ ≤ 19 / 50 := by rw [hb']; linarith
  have h1b : 0 ≤ 1 - fb u := by rw [hb]; linarith
  have h1b2 : 1 - fb u ≤ 19 / 50 := by rw [hb]; linarith
  have hal1 : falpha u δ 1 = fsA u δ * (1 - fb u) := rfl
  have hbe1 : fbeta u δ 1 = -1 + fsB u δ * (1 - fb' u δ) := rfl
  have hA1 : -(1 / 2) < falpha u δ 1 := by rw [hal1]; nlinarith
  have hB1a : -(5 / 3) * (19 / 50) ≤ fsB u δ * (1 - fb' u δ) := by nlinarith
  have hB1b : fsB u δ * (1 - fb' u δ) ≤ 0 := by nlinarith
  -- d
  have hq : (1 - fb' u δ) / (fb' u δ - fa u) * (fb' u δ - fa u) = 1 - fb' u δ := by
    field_simp
  have hdd : fd u δ = 13 / 10 + (1 - fb' u δ) / (fb' u δ - fa u) + feps u δ := rfl
  -- P
  have hP : fP u δ = -fsA u δ * fb u + 1 + fsB u δ * fb' u δ := by
    show fsA u δ * (0 - fb u) - (-1 + fsB u δ * (0 - fb' u δ)) = _; ring
  refine ⟨he0, by linarith, hD1p, hD2p, ?_, ?_, by linarith, by linarith, by linarith,
    ?_, ?_, ?_, ?_⟩
  · -- P > 0
    apply fb_pos_of_scaled (mul_pos hD1p hD2p) hbpos
    have hapos : 0 < fa u := by rw [ha]; linarith
    have hba : 0 < fb u - fa u := by rw [hb, ha]; linarith
    have key := fb_P_num (fa u) (fb u) δ hd0 hapos hbpos hba (by have : fa' u δ = fa u + 7 / 25 * δ := rfl; linarith)
    have ea' : fa' u δ = fa u + 7 / 25 * δ := rfl
    have eb' : fb' u δ = fb u + 9 / 25 * δ := rfl
    rw [← ea', ← eb'] at key
    have : fP u δ * ((fb u - fa' u δ) * (fb' u δ - fa u)) * fb u
        = 3 / 4 * fa' u δ * fb u * (fb' u δ - fa u)
          + (fb u - fa' u δ) * ((fb' u δ - fa u) * fb u - fb u * fb' u δ
            + 3 / 4 * fa' u δ * fb' u δ) := by
      rw [hP]
      linear_combination (-(fb u) * (fb' u δ - fa u) * fb u) * hsA
        + (fb' u δ * (fb u - fa' u δ) * fb u) * hsB
        + (fb u * (fb' u δ - fa u) + (fb u - fa' u δ) * fb' u δ) * heps
    rw [this]; exact key
  · linarith
  · -- d > 3/2
    rw [hdd]
    have hs : 0 < 13 / 10 + (1 - fb' u δ) / (fb' u δ - fa u) + feps u δ - 3 / 2 := by
      apply fb_pos_of_scaled hD2p hbpos
      have key := fb_dlo_num u δ hd0 hd1 hu0 hu1
      have : (13 / 10 + (1 - fb' u δ) / (fb' u δ - fa u) + feps u δ - 3 / 2)
          * (fb' u δ - fa u) * fb u
          = (1 - fb' u δ) * fb u + 3 / 4 * fa' u δ * (fb' u δ - fa u)
            - 1 / 5 * (fb' u δ - fa u) * fb u := by
        linear_combination (fb u) * hq + (fb' u δ - fa u) * heps
      rw [this]; unfold fb' fb fa' fa; exact key
    linarith
  · -- d < 21/10
    rw [hdd]
    have hs : 0 < 21 / 10 - (13 / 10 + (1 - fb' u δ) / (fb' u δ - fa u) + feps u δ) := by
      apply fb_pos_of_scaled hD2p hbpos
      have key := fb_dhi_num u δ hd0 hd1 hu0 hu1
      have : (21 / 10 - (13 / 10 + (1 - fb' u δ) / (fb' u δ - fa u) + feps u δ))
          * (fb' u δ - fa u) * fb u
          = 4 / 5 * (fb' u δ - fa u) * fb u - (1 - fb' u δ) * fb u
            - 3 / 4 * fa' u δ * (fb' u δ - fa u) := by
        linear_combination (-(fb u)) * hq - (fb' u δ - fa u) * heps
      rw [this]; unfold fb' fb fa' fa; exact key
    linarith
  · -- Dyb
    show 0 < 8 - (fsA u δ * (fb' u δ - fb u) + 1)
    have : fb' u δ - fb u = 9 / 25 * δ := by rw [hb', hb]; ring
    rw [this]; nlinarith
  · show 0 < 8 - (fsA u δ * (fa u - fb u) + feps u δ)
    have h0 : 0 ≤ fb u - fa u := by rw [hb, ha]; linarith
    have h1 : fb u - fa u ≤ 1 := by rw [hb, ha]; linarith
    have k1 : 0 ≤ (fsA u δ + 37 / 54) * (fb u - fa u) :=
      mul_nonneg (by linarith) h0
    have k2 : fsA u δ * (fa u - fb u) = -(fsA u δ * (fb u - fa u)) := by ring
    linarith

end Q2CL
