import Q2CL.Defs

namespace Q2CL

open K4

private lemma g3_core (u un δ : ℝ) (h0 : 0 ≤ δ) (h1 : δ ≤ 1 / 5) (hu : 0 ≤ u)
    (hu1 : u + δ ≤ 1) (hn : 0 ≤ un) (hn1 : un + δ ≤ 1) :
    0 < fbeta u δ 0 - falphaN u un δ 0 ∧ 0 < tP u un δ := by
  have hb : 0 < fb u := by unfold fb; linarith
  have hbn : 0 < fb un := by unfold fb; linarith
  have hc : 0 < fb' u δ - fa u := by unfold fb' fb fa; linarith
  have hcn : 0 < fb un - fa' un δ := by unfold fb fa' fa; linarith
  have he0 : 0 ≤ feps u δ := by
    unfold feps; apply div_nonneg _ hb.le; unfold fa' fa; linarith
  have he1 : feps u δ ≤ 2 / 5 := by
    unfold feps; rw [div_le_iff₀ hb]; unfold fa' fa fb; linarith
  have hen0 : 0 ≤ feps un δ := by
    unfold feps; apply div_nonneg _ hbn.le; unfold fa' fa; linarith
  have hb'1 : fb' u δ ≤ 1 := by unfold fb' fb; linarith
  have hb'0 : 0 ≤ fb' u δ := by unfold fb' fb; linarith
  have hbn1 : fb un ≤ 1 := by unfold fb; linarith
  -- X ≥ 1/2
  have hX : 1 / 2 ≤ (1 - feps u δ * fb' u δ) / (fb' u δ - fa u) := by
    rw [le_div_iff₀ hc]
    have : feps u δ * fb' u δ ≤ 2 / 5 := by nlinarith
    have : fb' u δ - fa u ≤ 1 := by unfold fb' fb fa; linarith
    linarith
  -- Y ≤ 9/20
  have hY : feps un δ * fb un / (fb un - fa' un δ) ≤ 9 / 20 := by
    rw [div_le_iff₀ hcn]
    have : feps un δ * fb un = 3 / 4 * fa' un δ := by
      unfold feps; field_simp
    rw [this]; unfold fb fa' fa; linarith
  have hZ : 0 ≤ feps u δ * (1 - fb' u δ) / (fb' u δ - fa u) :=
    div_nonneg (mul_nonneg he0 (by linarith)) hc.le
  have hW : 0 ≤ feps un δ * (1 - fb un) / (fb un - fa' un δ) :=
    div_nonneg (mul_nonneg hen0 (by linarith)) hcn.le
  constructor
  · have e : fbeta u δ 0 - falphaN u un δ 0 = 3 / 10 + feps u δ +
        (1 - feps u δ * fb' u δ) / (fb' u δ - fa u) -
        feps un δ * fb un / (fb un - fa' un δ) := by
      unfold fbeta falphaN fsB fsA fd; ring
    rw [e]; linarith
  · have e : tP u un δ = 3 / 10 + feps u δ +
        feps u δ * (1 - fb' u δ) / (fb' u δ - fa u) +
        feps un δ * (1 - fb un) / (fb un - fa' un δ) := by
      unfold tP fbeta falphaN fsB fsA fd; ring
    rw [e]; linarith

/-- Lemma 83(1), transitions: G3b0 and G3b1 (`B_j > A_{j+1}` at both ends). -/
theorem trans_G3 (u un δ : ℝ) (h : TransDom u un δ) :
    0 < fbeta u δ 0 - falphaN u un δ 0 ∧ 0 < tP u un δ := by
  obtain ⟨h0, h1, hc⟩ := h
  rcases hc with ⟨hu, hu1, rfl⟩ | ⟨hu, hu1, rfl⟩ | ⟨rfl, rfl⟩
  · exact g3_core un un δ h0 h1 hu (by linarith) hu (by linarith)
  · exact g3_core u (u + 2 * δ) δ h0 h1 hu (by linarith) (by linarith) (by linarith)
  · exact g3_core (1 - δ) 0 δ h0 h1 (by linarith) (by linarith) le_rfl (by linarith)

end Q2CL
