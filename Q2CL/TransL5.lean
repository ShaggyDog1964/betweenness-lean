import Q2CL.Defs

namespace Q2CL

open K4

/-- Algebraic core: with `e = ε`, `r = (1-b')/(b'-a)`, `q = -s_A(un)` and
`T = P_tr = 3/10 + e + e r + q (1 - b_n)`, both inequalities follow from crude bounds. -/
private lemma l5_core (e r q x A B' Bn : ℝ) (he0 : 0 ≤ e) (he1 : e ≤ 1 / 4) (hr0 : 0 ≤ r)
    (hr1 : r ≤ 16 / 25) (hq0 : 0 ≤ q) (hq1 : q ≤ 1 / 2) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 75)
    (hA : 0 ≤ A) (hBn0 : 0 ≤ 1 - Bn) (hBn1 : 1 - Bn ≤ 19 / 50)
    (hM : 3 / 100 ≤ 3 / 10 + r + e + q * (B' - Bn)
      - 39 / 44 * (3 / 10 + e + e * r + q * (1 - Bn))) :
    0 < (3 / 10 + r + e) + q * (B' - Bn)
        - KC * (2 + x * (3 / 10 + r + e)) * (3 / 10 + e + e * r + q * (1 - Bn)) ∧
      0 < (13 / 10 + r) + q * (A - Bn)
        - KC * (2 + x * (13 / 10 + r)) * (3 / 10 + e + e * r + q * (1 - Bn)) := by
  set T := 3 / 10 + e + e * r + q * (1 - Bn) with hTdef
  have her : e * r ≤ 1 / 4 * (16 / 25) := mul_le_mul he1 hr1 hr0 (by norm_num)
  have hqB : q * (1 - Bn) ≤ 1 / 2 * (19 / 50) := mul_le_mul hq1 hBn1 hBn0 (by norm_num)
  have hT0 : 0 ≤ T := by
    have := mul_nonneg he0 hr0; have := mul_nonneg hq0 hBn0; linarith
  have hT1 : T ≤ 9 / 10 := by linarith
  unfold KC
  constructor
  · have hS0 : 0 ≤ 3 / 10 + r + e := by linarith
    have hxS : x * (3 / 10 + r + e) ≤ 1 / 75 * (6 / 5) :=
      mul_le_mul hx1 (by linarith) hS0 (by norm_num)
    have hxST : x * (3 / 10 + r + e) * T ≤ 1 / 75 * (6 / 5) * (9 / 10) :=
      mul_le_mul hxS hT1 hT0 (by norm_num)
    nlinarith
  · have hS0 : 0 ≤ 13 / 10 + r := by linarith
    have hxS : x * (13 / 10 + r) ≤ 1 / 75 * (2 : ℝ) :=
      mul_le_mul hx1 (by linarith) hS0 (by norm_num)
    have hxST : x * (13 / 10 + r) * T ≤ 1 / 75 * 2 * (9 / 10) :=
      mul_le_mul hxS hT1 hT0 (by norm_num)
    have h1 := mul_nonneg hr0 (show 0 ≤ 1 - 39 / 44 * e by linarith)
    have h2 := mul_nonneg hq0 hA
    have h3 := mul_nonneg hq0 hBn0
    nlinarith

/-- Bounds on `ε(v, δ)` and `q = ε(v, δ) / (b(v) - a'(v, δ))`. -/
private lemma eps_bounds (v δ : ℝ) (hv : 0 ≤ v) (hd0 : 0 ≤ δ) (hd1 : δ ≤ 1 / 5)
    (hvd : v + δ ≤ 1) :
    0 ≤ feps v δ ∧ feps v δ ≤ 1 / 4 ∧ 0 ≤ feps v δ / (fb v - fa' v δ) ∧
      feps v δ / (fb v - fa' v δ) ≤ 1 / 2 := by
  have hb : 0 < fb v := by unfold fb; positivity
  have ha : 0 ≤ fa' v δ := by unfold fa' fa; positivity
  have he0 : 0 ≤ feps v δ := by unfold feps; positivity
  have he1 : feps v δ ≤ 1 / 4 := by
    unfold feps; rw [div_le_iff₀ hb]; unfold fa' fa fb at *; linarith
  have hD : 1 / 2 ≤ fb v - fa' v δ := by unfold fb fa' fa; linarith
  refine ⟨he0, he1, div_nonneg he0 (by linarith), ?_⟩
  rw [div_le_iff₀ (by linarith)]; nlinarith

/-- Bounds on `r = (1 - b')/(b' - a)`. -/
private lemma r_bounds (u δ : ℝ) (hu : 0 ≤ u) (hd0 : 0 ≤ δ) (hd1 : δ ≤ 1 / 5)
    (hud : u + δ ≤ 1) :
    0 ≤ (1 - fb' u δ) / (fb' u δ - fa u) ∧ (1 - fb' u δ) / (fb' u δ - fa u) ≤ 16 / 25 ∧
      (1 - fb' u δ) / (fb' u δ - fa u) * (fb' u δ - fa u) = 1 - fb' u δ ∧
      fb' u δ - fa u ≤ 92 / 125 := by
  have hD : 3 / 5 ≤ fb' u δ - fa u := by unfold fb' fb fa; linarith
  have hN : 0 ≤ 1 - fb' u δ := by unfold fb' fb; linarith
  refine ⟨div_nonneg hN (by linarith), ?_, div_mul_cancel₀ _ (by linarith), ?_⟩
  · rw [div_le_iff₀ (by linarith)]; unfold fb' fb fa; linarith
  · unfold fb' fb fa; linarith

private lemma l5a_eq (u un δ x : ℝ) :
    tL5a u un δ x =
      (3 / 10 + (1 - fb' u δ) / (fb' u δ - fa u) + feps u δ)
        + feps un δ / (fb un - fa' un δ) * (fb' u δ - fb un)
        - KC * (2 + x * (3 / 10 + (1 - fb' u δ) / (fb' u δ - fa u) + feps u δ))
          * (3 / 10 + feps u δ + feps u δ * ((1 - fb' u δ) / (fb' u δ - fa u))
            + feps un δ / (fb un - fa' un δ) * (1 - fb un)) := by
  simp only [tL5a, tP, falphaN, fbeta, fd, fsB, fsA]
  ring

private lemma l5b_eq (u un δ x : ℝ) :
    tL5b u un δ x =
      (13 / 10 + (1 - fb' u δ) / (fb' u δ - fa u))
        + feps un δ / (fb un - fa' un δ) * (fa u - fb un)
        - KC * (2 + x * (13 / 10 + (1 - fb' u δ) / (fb' u δ - fa u)))
          * (3 / 10 + feps u δ + feps u δ * ((1 - fb' u δ) / (fb' u δ - fa u))
            + feps un δ / (fb un - fa' un δ) * (1 - fb un)) := by
  simp only [tL5b, tP, falphaN, fbeta, fd, fsB, fsA]
  ring

/-- Lemma 83(1), transitions: L5a and L5b. -/
theorem trans_L5 (u un δ x : ℝ) (h : TransDom u un δ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 75) :
    0 < tL5a u un δ x ∧ 0 < tL5b u un δ x := by
  obtain ⟨hd0, hd1, hcase⟩ := h
  -- common facts: `u + δ ≤ 1`, `0 ≤ un`, `un + δ ≤ 1`
  have hu0 : 0 ≤ u := by rcases hcase with ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ <;> linarith
  have hud : u + δ ≤ 1 := by
    rcases hcase with ⟨-, h1, -⟩ | ⟨-, h1, -⟩ | ⟨h1, -⟩ <;> linarith
  have hun0 : 0 ≤ un := by
    rcases hcase with ⟨-, -, h1⟩ | ⟨-, -, h1⟩ | ⟨-, h1⟩ <;> rw [h1] <;> linarith
  have hund : un + δ ≤ 1 := by
    rcases hcase with ⟨-, -, h1⟩ | ⟨-, h2, h1⟩ | ⟨-, h1⟩ <;> rw [h1] <;> linarith
  obtain ⟨he0, he1, -, -⟩ := eps_bounds u δ hu0 hd0 hd1 hud
  obtain ⟨-, -, hq0, hq1⟩ := eps_bounds un δ hun0 hd0 hd1 hund
  obtain ⟨hr0, hr1, hrdef, hBA⟩ := r_bounds u δ hu0 hd0 hd1 hud
  rw [l5a_eq, l5b_eq]
  set e := feps u δ
  set q := feps un δ / (fb un - fa' un δ)
  set r := (1 - fb' u δ) / (fb' u δ - fa u)
  have hA : 0 ≤ fa u := by unfold fa; positivity
  have hBn0 : 0 ≤ 1 - fb un := by unfold fb; linarith
  have hBn1 : 1 - fb un ≤ 19 / 50 := by unfold fb; linarith
  apply l5_core e r q x (fa u) (fb' u δ) (fb un) he0 he1 hr0 hr1 hq0 hq1 hx0 hx1 hA hBn0 hBn1
  have hqr : q * (1 - fb' u δ) = q * r * (fb' u δ - fa u) := by rw [← hrdef]; ring
  have k1 := mul_nonneg hr0 (show 0 ≤ 1 / 4 - e by linarith)
  have k2 := mul_nonneg hr0 (show 0 ≤ 1 / 2 - q by linarith)
  have k3 := mul_nonneg (mul_nonneg hr0 hq0) (show 0 ≤ 92 / 125 - (fb' u δ - fa u) by linarith)
  rcases hcase with ⟨-, -, hun⟩ | ⟨-, -, hun⟩ | ⟨hu, hun⟩
  · -- stay: `b_n = b' - 9δ/25`
    have hB : fb un = fb' u δ - 9 / 25 * δ := by rw [hun]; unfold fb'; ring
    rw [hB]
    have k4 := mul_nonneg hq0 hd0
    nlinarith
  · -- step: `b_n = b' + 9δ/25`
    have hB : fb un = fb' u δ + 9 / 25 * δ := by rw [hun]; unfold fb' fb; ring
    rw [hB]
    have k4 := mul_nonneg (show 0 ≤ 1 / 2 - q by linarith) hd0
    nlinarith
  · -- wrap: `b' = 49/50`, `b_n = 31/50`
    have hB : fb un = 31 / 50 := by rw [hun]; unfold fb; ring
    have hB' : fb' u δ = 49 / 50 := by rw [hu]; unfold fb' fb; ring
    have k5 := mul_nonneg hr0 (show 0 ≤ 1 - 39 / 44 * e by linarith)
    rw [hB, hB']
    nlinarith

end Q2CL
