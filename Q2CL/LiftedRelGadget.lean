import Q2CL.Defs
import Q2CL.FaceL2
import Q2CL.FaceBasic
import Q2CL.WCons
import Q2CL.CwBound
import Q2CL.SliceEval
import Q2CL.LiftOn
import Q2CL.TightNest
import Q2CL.GadgetLines
import Q2CL.ClassTrans
import Q2CL.JSpec

namespace Q2CL

open K4

/-- Lifting identity (Lemma 75(3)), multiplied out. -/
private lemma lift_id (U S V s t L V' : ℝ) (hs : s < 1) (hk : 1 + cOf s * V ≠ 0)
    (hk' : 1 + cOf s * V' ≠ 0) (hH : 1 + hLift s L V' ≠ 0) :
    fval U S V (liftPt s t L V') * (1 + hLift s L V') =
      (1 - s) * (L - (U * (1 - t) + S * t) + cOf s * (1 + hLift s L V') * (V - V')) := by
  rw [(slice_eval U S V s t L V' hs hk hH 0 (by norm_num)).1]
  have e : hLift s L V' * (1 + cOf s * V') = L - cOf s * V' := by
    unfold hLift; field_simp
  generalize hLift s L V' = H at *
  generalize cOf s = c at *
  have h1 : (1 - s) * (1 + c * V) / (1 + H) *
      (H - ((U - c * V) * (1 - t) + (S - c * V) * t) / (1 + c * V)) * (1 + H) =
      (1 - s) * ((1 + c * V) * H - ((U - c * V) * (1 - t) + (S - c * V) * t)) := by
    field_simp
  rw [h1]
  linear_combination (1 - s) * e

/-- The shared bound: `c (1 + H') Y < g D`. -/
private lemma core_bound {g P w c Hp H o D Y Kb : ℝ} (hg : 0 < g) (hP : 0 < P) (hw : 0 < w)
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1 / 11) (hH0 : 0 < 1 + Hp) (hHp : 1 + Hp ≤ 1 + H + g * o)
    (hY0 : 0 ≤ Y) (hY1 : Y ≤ w * (g * P)) (hK : 1 / 11 * w * (1 + H + g * o) ≤ Kb)
    (hD : 0 < D - Kb * P) : c * (1 + Hp) * Y < g * D := by
  have h1 : c * (1 + Hp) ≤ 1 / 11 * (1 + H + g * o) :=
    mul_le_mul hc1 hHp hH0.le (by norm_num)
  have h2 : c * (1 + Hp) * Y ≤ 1 / 11 * (1 + H + g * o) * (w * (g * P)) :=
    mul_le_mul h1 hY1 hY0 (by nlinarith)
  have h3 : 1 / 11 * (1 + H + g * o) * (w * (g * P)) ≤ Kb * (g * P) := by
    have : 1 / 11 * (1 + H + g * o) * (w * (g * P)) =
        (1 / 11 * w * (1 + H + g * o)) * (g * P) := by ring
    rw [this]; exact mul_le_mul_of_nonneg_right hK (by positivity)
  have h4 : Kb * (g * P) < g * D := by nlinarith
  linarith

theorem lifted_rel_gadget {m ns : ℕ} {ds : ℝ} (hA : Adm m ns ds) :
    ∀ j, j < Jn m ns →
      fval (UA m ns j) (SA m ns j) (VA m ns j) (gpt m ns ds j 2) < 0 ∧
      fval (UA m ns j) (SA m ns j) (VA m ns j) (gpt m ns ds j 3) < 0 ∧
      0 < fval (UB m ns j) (SB m ns j) (VB m ns j) (gpt m ns ds j 0) ∧
      0 < fval (UB m ns j) (SB m ns j) (VB m ns j) (gpt m ns ds j 1) := by
  intro j hj
  have hm : 2 ≤ m := hA.1
  have hns : 1 ≤ ns := by
    rcases Nat.eq_zero_or_pos ns with h | h
    · have := hA.2.1; subst h; simp at this
    · exact h
  obtain ⟨hg0, hg1, -, hJ, -, -⟩ := J_spec hA
  obtain ⟨hs0, hs1, -, -, hVA1, hVB1, hHpos⟩ := cw_bound hA j hj
  obtain ⟨-, hwc, -⟩ := w_cons hA
  have hwc' := hwc j hj
  obtain ⟨hSB1, hSBA, hSAU, -, hUBA⟩ := (gadget_lines hA).1 j hj
  obtain ⟨hVBA, -⟩ := (tight_nest hA).1 j hj
  have hGD := (class_trans m ns j hm hns).1
  obtain ⟨he0, he1, -, -, hP, -⟩ := face_basic _ _ hGD
  obtain ⟨hL2a, hL2b, hL2c, hL2d⟩ := face_L2 _ _ (gP m ns) hGD hg0.le hg1
  set s := sig ns ds j with hs
  set c := cOf s with hcdef
  set g := gP m ns with hgdef
  set H := Hh m ns j with hHdef
  set u := uOf m ns j with hudef
  set δ := dlt m with hδdef
  set ε := feps u δ with hεdef
  set P := fP u δ with hPdef
  set w := wA m ns j with hwdef
  have hs1' : s < 1 := by linarith
  have hc0 : 0 ≤ c := by rw [hcdef]; unfold cOf; apply div_nonneg hs0; linarith
  have hc1 : c ≤ 1 / 11 := by
    rw [hcdef]; unfold cOf; rw [div_le_iff₀ (by linarith)]; linarith
  have hSA0 : 0 < SA m ns j := by linarith
  have hUA0 : 0 < UA m ns j := by linarith
  have hw0 : 0 < w := by
    have := ((w_envelope hA).1 j hj.le).1
    have h0 : (0 : ℝ) < o0 := by unfold o0; norm_num
    linarith
  have hkA : 0 < 1 + c * VA m ns j := by nlinarith
  have hkB : 0 < 1 + c * VB m ns j := by nlinarith
  -- `UA - UB = g P`
  have hUAB : UA m ns j - UB m ns j = g * P := by
    show (H + g * alJ m ns j 0) - (H + g * beJ m ns j 0) = g * fP u δ
    unfold alJ beJ fP; ring
  -- `Y = VA - VB`
  have hYeq : (VA m ns j - VB m ns j) * UA m ns j = w * SA m ns j * (g * P) := by
    have : VA m ns j = w * SA m ns j := rfl
    rw [← hUAB]; linear_combination (-1 : ℝ) * hVBA + (UA m ns j - UB m ns j) * this
  have hgP : 0 < g * P := mul_pos hg0 hP
  have hY0 : 0 ≤ VA m ns j - VB m ns j := by
    have : 0 < (VA m ns j - VB m ns j) * UA m ns j := by rw [hYeq]; positivity
    exact (pos_of_mul_pos_left this hUA0.le).le
  have hY1 : VA m ns j - VB m ns j ≤ w * (g * P) := by
    refine le_of_mul_le_mul_right ?_ hUA0
    rw [hYeq]
    have : w * SA m ns j * (g * P) ≤ w * UA m ns j * (g * P) := by
      apply mul_le_mul_of_nonneg_right _ hgP.le
      exact mul_le_mul_of_nonneg_left hSAU.le hw0.le
    linarith
  -- lines in face coordinates
  have hAt : ∀ t, UA m ns j * (1 - t) + SA m ns j * t = H + g * falpha u δ t := by
    intro t
    show (H + g * alJ m ns j 0) * (1 - t) + (H + g * alJ m ns j 1) * t = _
    unfold alJ falpha; ring
  have hBt : ∀ t, UB m ns j * (1 - t) + SB m ns j * t = H + g * fbeta u δ t := by
    intro t
    show (H + g * beJ m ns j 0) * (1 - t) + (H + g * beJ m ns j 1) * t = _
    unfold beJ fbeta; ring
  -- generic facts on a lifted point
  have hHp_le : ∀ L V', 0 < hLift s L V' → 0 ≤ c * V' → hLift s L V' ≤ L := by
    intro L V' hpos hk
    have e : hLift s L V' * (1 + c * V') = L - c * V' := by
      unfold hLift; rw [← hcdef]; field_simp
    nlinarith
  have hε : epsJ m ns j = ε := rfl
  have hcVA : 0 ≤ c * VA m ns j := by nlinarith
  have hcVB : 0 ≤ c * VB m ns j := by nlinarith
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- G2a: yb, lifted from B, against A
    have hH' := hHpos 2 (by norm_num)
    simp only [gpt, ptT, ptL, ptV, show (2:ℕ) ≠ 0 by decide, show (2:ℕ) ≠ 1 by decide,
      if_true, if_false, show ¬ (2:ℕ) < 2 by decide] at hH' ⊢
    change 0 < hLift s (H - g) (VB m ns j) at hH'
    change fval (UA m ns j) (SA m ns j) (VA m ns j) (liftPt s (fb' u δ) (H - g) (VB m ns j)) < 0
    have hid := lift_id (UA m ns j) (SA m ns j) (VA m ns j) s (fb' u δ) (H - g) (VB m ns j)
      hs1' hkA.ne' hkB.ne' (by linarith)
    rw [← hcdef, hAt] at hid
    have hle := hHp_le _ _ hH' hcVB
    have hb := core_bound (o := -1) (H := H) (Hp := hLift s (H - g) (VB m ns j)) (D := falpha u δ (fb' u δ) + 1) hg0 hP hw0 hc0 hc1
      (by linarith) (by linarith) hY0 hY1 (hwc' (-1) le_rfl (by norm_num))
      (by rw [show max (-1 : ℝ) 0 = 0 by norm_num]; unfold fL2a at hL2a; linarith)
    have hneg : (1 - s) * (H - g - (H + g * falpha u δ (fb' u δ)) +
        c * (1 + hLift s (H - g) (VB m ns j)) * (VA m ns j - VB m ns j)) < 0 := by
      apply mul_neg_of_pos_of_neg (by linarith); linarith
    rw [← hid] at hneg
    exact neg_of_mul_neg_left hneg (by linarith)
  · -- G2b: xb, lifted from B, against A
    have hH' := hHpos 3 (by norm_num)
    simp only [gpt, ptT, ptL, ptV, show (3:ℕ) ≠ 0 by decide, show (3:ℕ) ≠ 1 by decide,
      show (3:ℕ) ≠ 2 by decide, if_true, if_false, show ¬ (3:ℕ) < 2 by decide] at hH' ⊢
    change 0 < hLift s (H - g * ε) (VB m ns j) at hH'
    change fval (UA m ns j) (SA m ns j) (VA m ns j) (liftPt s (fa u) (H - g * ε) (VB m ns j)) < 0
    have hid := lift_id (UA m ns j) (SA m ns j) (VA m ns j) s (fa u) (H - g * ε)
      (VB m ns j) hs1' hkA.ne' hkB.ne' (by linarith)
    rw [← hcdef, hAt] at hid
    have hle := hHp_le _ _ hH' hcVB
    have hb := core_bound (o := -ε) (H := H) (Hp := hLift s (H - g * ε) (VB m ns j)) (D := falpha u δ (fa u) + ε) hg0 hP hw0 hc0 hc1
      (by linarith) (by linarith) hY0 hY1 (hwc' (-ε) (by linarith) (by linarith))
      (by rw [show max (-ε) 0 = 0 from max_eq_right (by linarith)]
          unfold fL2b at hL2b; linarith)
    have hneg : (1 - s) * (H - g * ε - (H + g * falpha u δ (fa u)) +
        c * (1 + hLift s (H - g * ε) (VB m ns j)) * (VA m ns j - VB m ns j)) < 0 := by
      apply mul_neg_of_pos_of_neg (by linarith); linarith
    rw [← hid] at hneg
    exact neg_of_mul_neg_left hneg (by linarith)
  · -- G2c: xa, lifted from A, against B
    have hH' := hHpos 0 (by norm_num)
    simp only [gpt, ptT, ptL, ptV, if_true, show (0:ℕ) < 2 by decide] at hH' ⊢
    change 0 < hLift s (H + g * ε) (VA m ns j) at hH'
    change 0 < fval (UB m ns j) (SB m ns j) (VB m ns j)
      (liftPt s (fa' u δ) (H + g * ε) (VA m ns j))
    have hid := lift_id (UB m ns j) (SB m ns j) (VB m ns j) s (fa' u δ) (H + g * ε)
      (VA m ns j) hs1' hkB.ne' hkA.ne' (by linarith)
    rw [← hcdef, hBt] at hid
    have hle := hHp_le _ _ hH' hcVA
    have hb := core_bound (o := ε) (H := H) (Hp := hLift s (H + g * ε) (VA m ns j)) (D := ε - fbeta u δ (fa' u δ)) hg0 hP hw0 hc0 hc1
      (by linarith) (by linarith) hY0 hY1 (hwc' ε (by linarith) (by linarith))
      (by rw [show max ε 0 = ε from max_eq_left (by linarith)]
          have e : fL2c u δ g = ε - fbeta u δ (fa' u δ) - KC * (2 + g * ε) * P := rfl
          linarith)
    have hpos : 0 < (1 - s) * (H + g * ε - (H + g * fbeta u δ (fa' u δ)) +
        c * (1 + hLift s (H + g * ε) (VA m ns j)) * (VB m ns j - VA m ns j)) := by
      have e : c * (1 + hLift s (H + g * ε) (VA m ns j)) * (VB m ns j - VA m ns j) =
          -(c * (1 + hLift s (H + g * ε) (VA m ns j)) * (VA m ns j - VB m ns j)) := by ring
      apply mul_pos (by linarith); linarith
    rw [← hid] at hpos
    exact pos_of_mul_pos_left hpos (by linarith)
  · -- G2d: ya, lifted from A, against B
    have hH' := hHpos 1 (by norm_num)
    simp only [gpt, ptT, ptL, ptV, show (1:ℕ) ≠ 0 by decide, if_true, if_false,
      show (1:ℕ) < 2 by decide] at hH' ⊢
    change 0 < hLift s H (VA m ns j) at hH'
    change 0 < fval (UB m ns j) (SB m ns j) (VB m ns j) (liftPt s (fb u) H (VA m ns j))
    have hid := lift_id (UB m ns j) (SB m ns j) (VB m ns j) s (fb u) H
      (VA m ns j) hs1' hkB.ne' hkA.ne' (by linarith)
    rw [← hcdef, hBt] at hid
    have hle := hHp_le _ _ hH' hcVA
    have hb := core_bound (o := 0) (H := H) (Hp := hLift s H (VA m ns j)) (D := -fbeta u δ (fb u)) hg0 hP hw0 hc0 hc1
      (by linarith) (by linarith) hY0 hY1 (hwc' 0 (by norm_num) (by norm_num))
      (by rw [show max (0 : ℝ) 0 = 0 by norm_num]; unfold fL2d at hL2d; linarith)
    have hpos : 0 < (1 - s) * (H - (H + g * fbeta u δ (fb u)) +
        c * (1 + hLift s H (VA m ns j)) * (VB m ns j - VA m ns j)) := by
      have e : c * (1 + hLift s H (VA m ns j)) * (VB m ns j - VA m ns j) =
          -(c * (1 + hLift s H (VA m ns j)) * (VA m ns j - VB m ns j)) := by ring
      apply mul_pos (by linarith); linarith
    rw [← hid] at hpos
    exact pos_of_mul_pos_left hpos (by linarith)

end Q2CL
