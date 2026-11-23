import Q2CL.Defs

namespace Q2CL

open K4

/-- Parameter arithmetic for the witness `T(mOf δ, nsOf δ, δ)`. -/
theorem witness_arith (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 11 / 1000) :
    Adm (mOf δ) (nsOf δ) δ ∧ 32 ≤ mOf δ ^ 2 * nsOf δ ∧
    δ ≤ (7 / 25) / ((2 * (mOf δ : ℝ) + 1) * (401 / 80)) ∧
    δ ≤ 9 / 500 * ((mOf δ : ℝ) + 1) / (mOf δ : ℝ) ^ 2 ∧
    cLower / δ ^ 3 < (100 / 7 : ℝ) * (mOf δ : ℝ) ^ 2 * (nsOf δ : ℝ) := by
  -- floor facts for ns
  set k : ℕ := ⌊1 / (12 * δ)⌋₊ with hk
  have h12 : 0 < 12 * δ := by positivity
  have hk1 : (k : ℝ) ≤ 1 / (12 * δ) := Nat.floor_le (by positivity)
  have hk2 : 1 / (12 * δ) < (k : ℝ) + 1 := Nat.lt_floor_add_one _
  have hkδ : (k : ℝ) * δ ≤ 1 / 12 := by
    rw [le_div_iff₀ h12] at hk1; nlinarith
  have hkδ' : 1 < ((k : ℝ) + 1) * (12 * δ) := by
    rw [div_lt_iff₀ h12] at hk2; linarith
  have hns : nsOf δ = 1 + k := rfl
  have hnsR : (nsOf δ : ℝ) = 1 + k := by rw [hns]; push_cast; ring
  have hnsδ : 1 / 12 < (nsOf δ : ℝ) * δ := by rw [hnsR]; nlinarith
  have hAdm2 : ((nsOf δ : ℝ) - 1) * δ ≤ 1 / 12 := by rw [hnsR]; linarith
  have hcL : cLower = 203 / 1000000 := rfl
  have hδ3 : 0 < δ ^ 3 := by positivity
  -- main
  suffices H : 32 ≤ mOf δ ^ 2 * nsOf δ ∧ 2 ≤ mOf δ ∧
      δ ≤ (7 / 25) / ((2 * (mOf δ : ℝ) + 1) * (401 / 80)) ∧
      δ ≤ 9 / 500 * ((mOf δ : ℝ) + 1) / (mOf δ : ℝ) ^ 2 ∧
      cLower / δ ^ 3 < (100 / 7 : ℝ) * (mOf δ : ℝ) ^ 2 * (nsOf δ : ℝ) by
    obtain ⟨h1, h2, h3, h4, h5⟩ := H
    exact ⟨⟨h2, le_trans (by norm_num) h1, hδ, hAdm2⟩, h1, h3, h4, h5⟩
  unfold mOf
  split_ifs with ha hb
  · -- m = 2
    have hk7 : 7 ≤ k := by
      rw [hk]; apply Nat.le_floor
      rw [le_div_iff₀ h12]; push_cast; nlinarith
    refine ⟨by rw [hns]; nlinarith, le_rfl, ?_, ?_, ?_⟩
    · rw [le_div_iff₀ (by norm_num)]; push_cast; nlinarith
    · push_cast; nlinarith
    · rw [hcL, div_lt_iff₀ hδ3]; push_cast
      have hd2 : (3 / 400 : ℝ) ^ 2 < δ ^ 2 := by nlinarith
      nlinarith [mul_lt_mul'' hnsδ hd2 (by norm_num) (by norm_num)]
  · -- m = 3
    push Not at ha
    have hk11 : 11 ≤ k := by
      rw [hk]; apply Nat.le_floor
      rw [le_div_iff₀ h12]; push_cast; nlinarith
    refine ⟨by rw [hns]; nlinarith, by norm_num, ?_, ?_, ?_⟩
    · rw [le_div_iff₀ (by norm_num)]; push_cast; nlinarith
    · push_cast; nlinarith
    · rw [hcL, div_lt_iff₀ hδ3]; push_cast
      have hd2 : (9 / 2000 : ℝ) ^ 2 < δ ^ 2 := by nlinarith
      nlinarith [mul_lt_mul'' hnsδ hd2 (by norm_num) (by norm_num)]
  · push Not at ha hb
    set m : ℕ := ⌊(9 / 500) / δ⌋₊ with hm
    have hm1 : (m : ℝ) ≤ (9 / 500) / δ := Nat.floor_le (by positivity)
    have hm2 : (9 / 500) / δ < (m : ℝ) + 1 := Nat.lt_floor_add_one _
    have hmδ : (m : ℝ) * δ ≤ 9 / 500 := by rw [le_div_iff₀ hδ] at hm1; linarith
    have hmδ' : 9 / 500 < ((m : ℝ) + 1) * δ := by rw [div_lt_iff₀ hδ] at hm2; linarith
    have hm4 : 4 ≤ m := by
      rw [hm]; apply Nat.le_floor
      rw [le_div_iff₀ hδ]; push_cast; nlinarith
    have hm4R : (4 : ℝ) ≤ m := by exact_mod_cast hm4
    have hk18 : 18 ≤ k := by
      rw [hk]; apply Nat.le_floor
      rw [le_div_iff₀ h12]; push_cast; nlinarith
    refine ⟨?_, by omega, ?_, ?_, ?_⟩
    · rw [hns]
      have : 16 ≤ m ^ 2 := by nlinarith
      nlinarith
    · rw [le_div_iff₀ (by positivity)]; nlinarith
    · rw [le_div_iff₀ (by positivity)]; nlinarith
    · rw [hcL, div_lt_iff₀ hδ3]
      have hmδ2 : (27 / 2000 : ℝ) < (m : ℝ) * δ := by nlinarith
      have hsq : (27 / 2000 : ℝ) ^ 2 < ((m : ℝ) * δ) ^ 2 := by
        have := hmδ2; nlinarith
      have := mul_lt_mul'' hnsδ hsq (by norm_num) (by norm_num)
      nlinarith

end Q2CL
