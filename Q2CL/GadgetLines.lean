import Q2CL.Defs
import Q2CL.JSpec
import Q2CL.TransG3

namespace Q2CL

open K4

/-- Lemma 74: positivity and ordering of the tight lines. -/
theorem gadget_lines {m ns : ℕ} {ds : ℝ} (hA : Adm m ns ds) :
    (∀ j, j < Jn m ns →
      1 - 2 * gP m ns ≤ SB m ns j ∧ SB m ns j < SA m ns j ∧ SA m ns j < UA m ns j ∧
      SB m ns j < UB m ns j ∧ UB m ns j < UA m ns j) ∧
    (∀ j, j + 1 < Jn m ns → UA m ns (j + 1) < UB m ns j ∧ SA m ns (j + 1) < SB m ns j) := by
  obtain ⟨hg0, -, -, hJ, -, -⟩ := J_spec hA
  have hm : 2 ≤ m := hA.1
  have hns : 1 ≤ ns := by
    rcases Nat.eq_zero_or_pos ns with h | h
    · have := hA.2.1; subst h; simp at this
    · exact h
  refine ⟨fun j hj => ?_, fun j hj => ?_⟩
  · obtain ⟨hH1, -⟩ := hJ j hj
    have hF := face_basic _ _ (class_trans m ns j hm hns).1
    obtain ⟨he0, he1, hD1, hD2, hP, hab, -, hb1, -⟩ := hF
    have hsA : fsA (uOf m ns j) (dlt m) < 0 := by
      unfold fsA; exact div_neg_of_neg_of_pos (by linarith) hD1
    have hsB : fsB (uOf m ns j) (dlt m) < 0 := by
      unfold fsB; exact div_neg_of_neg_of_pos (by linarith) hD2
    have hge : 0 ≤ gP m ns * epsJ m ns j := by
      unfold epsJ; exact mul_nonneg hg0.le he0.le
    have eA : alJ m ns j 0 - alJ m ns j 1 = -fsA (uOf m ns j) (dlt m) := by
      unfold alJ falpha; ring
    have eB : beJ m ns j 0 - beJ m ns j 1 = -fsB (uOf m ns j) (dlt m) := by
      unfold beJ fbeta; ring
    have eP : alJ m ns j 0 - beJ m ns j 0 = fP (uOf m ns j) (dlt m) := rfl
    have eAB : alJ m ns j 1 - beJ m ns j 1 =
        falpha (uOf m ns j) (dlt m) 1 - fbeta (uOf m ns j) (dlt m) 1 := rfl
    have eb1 : beJ m ns j 1 = fbeta (uOf m ns j) (dlt m) 1 := rfl
    have k1 := mul_pos hg0 hab
    rw [← eAB] at k1
    have k2 := mul_pos hg0 (neg_pos.2 hsA)
    rw [← eA] at k2
    have k3 := mul_pos hg0 (neg_pos.2 hsB)
    rw [← eB] at k3
    have k4 := mul_pos hg0 hP
    rw [← eP] at k4
    have k5 : -2 * gP m ns ≤ gP m ns * beJ m ns j 1 := by
      rw [eb1]; nlinarith
    unfold SB SA UA UB
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · linarith
    · linarith [mul_sub (gP m ns) (alJ m ns j 1) (beJ m ns j 1)]
    · linarith [mul_sub (gP m ns) (alJ m ns j 0) (alJ m ns j 1)]
    · linarith [mul_sub (gP m ns) (beJ m ns j 0) (beJ m ns j 1)]
    · linarith [mul_sub (gP m ns) (alJ m ns j 0) (beJ m ns j 0)]
  · have hT := trans_G3 _ _ _ (class_trans m ns j hm hns).2
    have hN := (normalization m ns j hm).2.1
    have h0 := hN 0
    have h1 := hN 1
    have e0 := mul_pos hg0 hT.1
    have e1 := mul_pos hg0 hT.2
    unfold tP at e1
    have b0 : beJ m ns j 0 = fbeta (uOf m ns j) (dlt m) 0 := rfl
    have b1 : beJ m ns j 1 = fbeta (uOf m ns j) (dlt m) 1 := rfl
    unfold UA UB SA SB
    rw [h0, h1, b0, b1]
    constructor
    · linarith [mul_sub (gP m ns) (fbeta (uOf m ns j) (dlt m) 0)
        (falphaN (uOf m ns j) (uOf m ns (j + 1)) (dlt m) 0)]
    · linarith [mul_sub (gP m ns) (fbeta (uOf m ns j) (dlt m) 1)
        (falphaN (uOf m ns j) (uOf m ns (j + 1)) (dlt m) 1)]

end Q2CL
