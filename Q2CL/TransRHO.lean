import Q2CL.Defs

namespace Q2CL

open K4

private lemma box18 (a b c d : ℝ) (ha : -3 ≤ a) (ha' : a ≤ 3) (hb : -3 ≤ b) (hb' : b ≤ 3)
    (hc : -3 ≤ c) (hc' : c ≤ 3) (hd : -3 ≤ d) (hd' : d ≤ 3) : -18 ≤ a * b - c * d := by
  nlinarith [mul_nonneg (by linarith : 0 ≤ a + 3) (by linarith : 0 ≤ b + 3),
    mul_nonneg (by linarith : 0 ≤ 3 - a) (by linarith : 0 ≤ 3 - b),
    mul_nonneg (by linarith : 0 ≤ c + 3) (by linarith : 0 ≤ 3 - d),
    mul_nonneg (by linarith : 0 ≤ 3 - c) (by linarith : 0 ≤ d + 3)]

private lemma rho_core (u un δ : ℝ) (h0 : 0 ≤ δ) (h1 : δ ≤ 1 / 5) (hu : 0 ≤ u)
    (hu1 : u + δ ≤ 1) (hn : 0 ≤ un) (hn1 : un + δ ≤ 1) :
    1 / 2 ≤ tc1 u un δ ∧ -18 ≤ tc2 u un δ := by
  have hb : 0 < fb u := by unfold fb; linarith
  have hbn : 0 < fb un := by unfold fb; linarith
  have hc : 3 / 5 ≤ fb' u δ - fa u := by unfold fb' fb fa; nlinarith
  have hc' : fb' u δ - fa u ≤ 3 / 4 := by unfold fb' fb fa; nlinarith
  have hcn : 1 / 2 ≤ fb un - fa' un δ := by unfold fb fa' fa; nlinarith
  have he0 : 0 ≤ feps u δ := by
    unfold feps; apply div_nonneg _ hb.le; unfold fa' fa; linarith
  have he1 : feps u δ ≤ 1 / 4 := by
    unfold feps; rw [div_le_iff₀ hb]; unfold fa' fa fb; nlinarith
  have hen0 : 0 ≤ feps un δ := by
    unfold feps; apply div_nonneg _ hbn.le; unfold fa' fa; linarith
  have hen1 : feps un δ ≤ 1 / 4 := by
    unfold feps; rw [div_le_iff₀ hbn]; unfold fa' fa fb; nlinarith
  have hb'1 : fb' u δ ≤ 1 := by unfold fb' fb; linarith
  have hb'0 : 0 ≤ fb' u δ := by unfold fb' fb; linarith
  have hbn1 : fb un ≤ 1 := by unfold fb; linarith
  have hbn0 : 0 ≤ fb un := hbn.le
  -- first term ≥ 1
  have hT1 : 1 ≤ (1 - feps u δ) / (fb' u δ - fa u) := by
    rw [le_div_iff₀ (by linarith)]; linarith
  -- second term ≤ 1/2
  have hT2 : feps un δ / (fb un - fa' un δ) ≤ 1 / 2 := by
    rw [div_le_iff₀ (by linarith)]; nlinarith
  -- slope bounds
  have hsB0 : fsB u δ ≤ 0 := by
    unfold fsB; apply div_nonpos_of_nonpos_of_nonneg <;> linarith
  have hsB1 : -5 / 3 ≤ fsB u δ := by
    unfold fsB; rw [le_div_iff₀ (by linarith)]; nlinarith
  have hsAe : fsA un δ = -(feps un δ / (fb un - fa' un δ)) := by unfold fsA; ring
  have hsA0 : fsA un δ ≤ 0 := by
    rw [hsAe]; linarith [div_nonneg hen0 (by linarith : (0:ℝ) ≤ fb un - fa' un δ)]
  have hsA1 : -1 / 2 ≤ fsA un δ := by
    rw [hsAe]; linarith
  have hR : (1 - fb' u δ) / (fb' u δ - fa u) ≤ 2 / 3 := by
    rw [div_le_iff₀ (by linarith)]; unfold fb' fb fa; nlinarith
  have hR0 : 0 ≤ (1 - fb' u δ) / (fb' u δ - fa u) := div_nonneg (by linarith) (by linarith)
  have hd0 : 0 ≤ fd u δ := by unfold fd; linarith
  have hd1 : fd u δ ≤ 5 / 2 := by unfold fd; linarith
  constructor
  · have e : tc1 u un δ = (1 - feps u δ) / (fb' u δ - fa u) -
        feps un δ / (fb un - fa' un δ) := by
      unfold tc1 fbeta falphaN fsB fsA; ring
    rw [e]; linarith
  · -- box bounds on the four line values
    have hB0a : -3 ≤ fbeta u δ 0 := by unfold fbeta; nlinarith
    have hB0b : fbeta u δ 0 ≤ 3 := by unfold fbeta; nlinarith
    have hB1a : -3 ≤ fbeta u δ 1 := by unfold fbeta; nlinarith
    have hB1b : fbeta u δ 1 ≤ 3 := by unfold fbeta; nlinarith
    have hA0a : -3 ≤ falphaN u un δ 0 := by unfold falphaN; nlinarith
    have hA0b : falphaN u un δ 0 ≤ 3 := by unfold falphaN; nlinarith
    have hA1a : -3 ≤ falphaN u un δ 1 := by unfold falphaN; nlinarith
    have hA1b : falphaN u un δ 1 ≤ 3 := by unfold falphaN; nlinarith
    unfold tc2
    exact box18 _ _ _ _ hB0a hB0b hA1a hA1b hA0a hA0b hB1a hB1b

/-- Lemma 83(1), transitions: RHOtr (`r(A_{j+1}) < r(B_j)`). -/
theorem trans_RHO (u un δ x : ℝ) (h : TransDom u un δ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 75) :
    0 < tRHO u un δ x := by
  have key : 1 / 2 ≤ tc1 u un δ ∧ -18 ≤ tc2 u un δ := by
    obtain ⟨h0, h1, hc⟩ := h
    rcases hc with ⟨hu, hu1, rfl⟩ | ⟨hu, hu1, rfl⟩ | ⟨rfl, rfl⟩
    · exact rho_core un un δ h0 h1 hu (by linarith) hu (by linarith)
    · exact rho_core u (u + 2 * δ) δ h0 h1 hu (by linarith) (by linarith) (by linarith)
    · exact rho_core (1 - δ) 0 δ h0 h1 (by linarith) (by linarith) le_rfl (by linarith)
  obtain ⟨k1, k2⟩ := key
  unfold tRHO
  nlinarith [mul_nonneg hx0 (by linarith : 0 ≤ tc2 u un δ + 18)]

end Q2CL
