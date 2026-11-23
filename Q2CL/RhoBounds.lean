import Q2CL.Defs
import Q2CL.GadgetLines
import Q2CL.FaceRate
import Q2CL.TransRHO

namespace Q2CL

open K4

/-- Identity (4.1), cross-difference form. -/
private lemma iden_cross (H g a0 a1 b0 b1 : ℝ) (hH : H ≠ 0) :
    g * H ^ 2 * ((b0 - b1) - (a0 - a1) + g / H * (b0 * a1 - a0 * b1)) =
      H * ((H + g * b0) * (H + g * a1) - (H + g * a0) * (H + g * b1)) := by
  field_simp; ring

/-- Identity (4.1), denominator form. -/
private lemma iden_den (H g a0 b1 : ℝ) (hH : H ≠ 0) :
    H ^ 2 * ((1 + g / H * a0) * (1 + g / H * b1)) = (H + g * a0) * (H + g * b1) := by
  field_simp

/-- Lemma 74: `ρ_j ≥ 1 + g/(2H_j)`, `ρ_j - 1 ≤ β (H_j - H_{j+1})/H_j`, and
`r(A_{j+1}) < r(B_j)`. -/
theorem rho_bounds {m ns : ℕ} {ds : ℝ} (hA : Adm m ns ds) :
    (∀ j, j < Jn m ns →
      1 + gP m ns / (2 * Hh m ns j) ≤ rho m ns j ∧
      rho m ns j - 1 ≤ 17 / 20 * (Hh m ns j - Hh m ns (j + 1)) / Hh m ns j) ∧
    (∀ j, j + 1 < Jn m ns →
      UA m ns (j + 1) / SA m ns (j + 1) < UB m ns j / SB m ns j) := by
  obtain ⟨hg0, hg1, -, hJ, -, -⟩ := J_spec hA
  have hm : 2 ≤ m := hA.1
  have hns : 1 ≤ ns := by
    rcases Nat.eq_zero_or_pos ns with h | h
    · have := hA.2.1; subst h; simp at this
    · exact h
  have hGL := gadget_lines hA
  -- H_j ≥ 1 for placed gadgets
  have hH1 : ∀ j, j < Jn m ns → 1 ≤ Hh m ns j := by
    intro j hj
    have h1 := (hJ j hj).1
    have he := (face_basic _ _ (class_trans m ns j hm hns).1).1
    have : 0 < gP m ns * epsJ m ns j := mul_pos hg0 he
    linarith
  refine ⟨fun j hj => ?_, fun j hj => ?_⟩
  · set H := Hh m ns j with hHdef
    set g := gP m ns with hgdef
    have hHpos : 0 < H := by linarith [hH1 j hj]
    have hx0 : 0 ≤ g / H := div_nonneg hg0.le hHpos.le
    have hx1 : g / H ≤ 1 / 75 := by
      rw [div_le_iff₀ hHpos]; nlinarith [hH1 j hj]
    obtain ⟨hSB, -, -, hSBUB, hUBUA⟩ := hGL.1 j hj
    have hSBpos : 0 < SB m ns j := by linarith
    have hUApos : 0 < UA m ns j := by linarith
    have hFR := face_rate _ _ (g / H) (class_trans m ns j hm hns).1 hx0 hx1
    obtain ⟨hBET, hKAP⟩ := hFR
    unfold fKAP fc1 fc2 at hKAP
    unfold fBET fc1 fc2 at hBET
    set u := uOf m ns j
    set δ := dlt m
    set a0 := falpha u δ 0
    set a1 := falpha u δ 1
    set b0 := fbeta u δ 0
    set b1 := fbeta u δ 1
    have eUA : UA m ns j = H + g * a0 := rfl
    have eSA : SA m ns j = H + g * a1 := rfl
    have eUB : UB m ns j = H + g * b0 := rfl
    have eSB : SB m ns j = H + g * b1 := rfl
    have ec := iden_cross H g a0 a1 b0 b1 hHpos.ne'
    have ed := iden_den H g a0 b1 hHpos.ne'
    set Δ := UB m ns j * SA m ns j - UA m ns j * SB m ns j with hΔ
    have eΔ : Δ = (H + g * b0) * (H + g * a1) - (H + g * a0) * (H + g * b1) := by
      rw [hΔ, eUA, eSA, eUB, eSB]
    set P := UA m ns j * SB m ns j with hP
    have eP : P = (H + g * a0) * (H + g * b1) := by rw [hP, eUA, eSB]
    have hPpos : 0 < P := mul_pos hUApos hSBpos
    have erho : rho m ns j = UB m ns j * SA m ns j / (SB m ns j * UA m ns j) := by
      unfold rho; rw [div_div_div_eq]
    have hPeq : SB m ns j * UA m ns j = P := by rw [hP]; ring
    rw [erho, hPeq]
    have hgH2 : 0 < g * H ^ 2 := by positivity
    constructor
    · -- KAP
      have k := mul_pos hgH2 hKAP
      have hk : g * H ^ 2 * ((b0 - b1 - (a0 - a1) + g / H * (b0 * a1 - a0 * b1)) -
          1 / 2 * (1 + g / H * a0) * (1 + g / H * b1)) = H * Δ - g / 2 * P := by
        rw [mul_assoc (1 / 2 : ℝ), mul_sub, ec, eΔ, eP, ← ed]; ring
      have hmain : g * P ≤ 2 * H * Δ := by
        have : 0 < H * Δ - g / 2 * P := by rw [← hk]; exact k
        linarith
      rw [le_div_iff₀ hPpos]
      have e2 : g / (2 * H) * P * (2 * H) = g * P := by field_simp
      have : g / (2 * H) * P ≤ Δ := by
        have h2H : 0 < 2 * H := by linarith
        refine le_of_mul_le_mul_right ?_ h2H
        linarith
      linarith
    · -- BET
      have k := mul_pos hgH2 hBET
      set d := fd u δ
      have hk : g * H ^ 2 * (17 / 20 * d * (1 + g / H * a0) * (1 + g / H * b1) -
          (b0 - b1 - (a0 - a1) + g / H * (b0 * a1 - a0 * b1))) =
          17 / 20 * g * d * P - H * Δ := by
        rw [mul_sub, ec, eΔ, eP, ← ed]; ring
      have hmain : H * Δ ≤ 17 / 20 * g * d * P := by
        have : 0 < 17 / 20 * g * d * P - H * Δ := by rw [← hk]; exact k
        linarith
      have hstep := (normalization m ns j hm).1
      have eHd : H - Hh m ns (j + 1) = g * d := by
        rw [hstep]
        show Hh m ns j - (Hh m ns j - gP m ns * dJ m ns j) = gP m ns * fd (uOf m ns j) (dlt m)
        unfold dJ; ring
      rw [eHd, sub_le_iff_le_add, div_le_iff₀ hPpos]
      have e2 : 17 / 20 * (g * d) / H * P * H = 17 / 20 * g * d * P := by field_simp
      have : Δ ≤ 17 / 20 * (g * d) / H * P := by
        refine le_of_mul_le_mul_right ?_ hHpos
        linarith
      linarith
  · have hj' : j < Jn m ns := by omega
    set H := Hh m ns j with hHdef
    set g := gP m ns with hgdef
    have hHpos : 0 < H := by linarith [hH1 j hj']
    have hx0 : 0 ≤ g / H := div_nonneg hg0.le hHpos.le
    have hx1 : g / H ≤ 1 / 75 := by
      rw [div_le_iff₀ hHpos]; nlinarith [hH1 j hj']
    obtain ⟨hSB, -, -, -, -⟩ := hGL.1 j hj'
    obtain ⟨hSB', hSBSA', -, -, -⟩ := hGL.1 (j + 1) hj
    have hSBpos : 0 < SB m ns j := by linarith
    have hSApos' : 0 < SA m ns (j + 1) := by linarith
    have hT := trans_RHO _ _ _ (g / H) (class_trans m ns j hm hns).2 hx0 hx1
    unfold tRHO tc1 tc2 at hT
    have hN := (normalization m ns j hm).2.1
    set u := uOf m ns j
    set un := uOf m ns (j + 1)
    set δ := dlt m
    have eUA' : UA m ns (j + 1) = H + g * falphaN u un δ 0 := hN 0
    have eSA' : SA m ns (j + 1) = H + g * falphaN u un δ 1 := hN 1
    have eUB : UB m ns j = H + g * fbeta u δ 0 := rfl
    have eSB : SB m ns j = H + g * fbeta u δ 1 := rfl
    have ec := iden_cross H g (falphaN u un δ 0) (falphaN u un δ 1) (fbeta u δ 0)
      (fbeta u δ 1) hHpos.ne'
    have hgH2 : 0 < g * H ^ 2 := by positivity
    have k := mul_pos hgH2 hT
    rw [ec] at k
    rw [div_lt_div_iff₀ hSApos' hSBpos, eUA', eSA', eUB, eSB]
    have : 0 < (H + g * fbeta u δ 0) * (H + g * falphaN u un δ 1) -
        (H + g * falphaN u un δ 0) * (H + g * fbeta u δ 1) := pos_of_mul_pos_right k hHpos.le
    linarith

end Q2CL
