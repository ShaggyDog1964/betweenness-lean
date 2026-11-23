import Q2CL.Defs
import Q2CL.TransL4
import Q2CL.TransL5
import Q2CL.WCons
import Q2CL.CwBound
import Q2CL.SliceEval
import Q2CL.LiftOn

namespace Q2CL

open K4

/-- Lemma 75(3) (lifting identity), in the form used here. -/
private lemma lift_id (U S V s t L V' : ℝ) (hk : 0 < 1 + cOf s * V')
    (hH : 0 < 1 + hLift s L V') (hs : s < 1) :
    fval U S V (liftPt s t L V') = (1 - s) / (1 + hLift s L V') *
      (L - (U * (1 - t) + S * t) + cOf s * (1 + hLift s L V') * (V - V')) := by
  have hs1 : (1 - s) ≠ 0 := by linarith
  have hc : s = cOf s * (1 - s) := by unfold cOf; field_simp
  have hHdef : hLift s L V' * (1 + cOf s * V') = L - cOf s * V' := by
    unfold hLift; field_simp
  simp only [fval, liftPt, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Matrix.cons_val_three]
  generalize hLift s L V' = H at hH hHdef ⊢
  generalize cOf s = c at hc hk hHdef ⊢
  have hVs : V * s = V * (c * (1 - s)) := by rw [← hc]
  rw [hVs]
  have hH' : (1 + H) ≠ 0 := hH.ne'
  field_simp
  linear_combination hHdef

/-- `c (1 + H') w ≤ (1/11) w (1 + L)`. -/
private lemma cw_le {s L V w : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 12) (hV : 1 < V) (hw : 0 < w)
    (hH : 0 < hLift s L V) :
    cOf s * (1 + hLift s L V) * w ≤ 1 / 11 * w * (1 + L) := by
  have hc0 : 0 ≤ cOf s := by unfold cOf; apply div_nonneg hs0; linarith
  have hc1 : cOf s ≤ 1 / 11 := by
    unfold cOf; rw [div_le_iff₀ (by linarith)]; linarith
  have hk : 0 ≤ cOf s * V := by positivity
  have hHL : hLift s L V ≤ L := by
    have hH' := hH
    unfold hLift at hH' ⊢
    have hpos : 0 < 1 + cOf s * V := by linarith
    have hLk : 0 < L - cOf s * V := by
      by_contra hc; rw [not_lt] at hc
      have := div_nonpos_of_nonpos_of_nonneg hc hpos.le
      linarith
    rw [div_le_iff₀ hpos]; nlinarith
  have h1 : cOf s * (1 + hLift s L V) ≤ 1 / 11 * (1 + L) :=
    mul_le_mul hc1 (by linarith) (by linarith) (by norm_num)
  nlinarith

private lemma fin_neg {g T P X Y B : ℝ} (hX : g * P * X ≤ g * P * Y) (hT : 0 < g * T)
    (hB : B = -(g * T) - g * P * Y + g * P * X) : B < 0 := by
  rw [hB]; linarith

private lemma fin_pos {g T P X Y B : ℝ} (hX : g * P * X ≤ g * P * Y) (hT : 0 < g * T)
    (hB : B = g * T + g * P * Y - g * P * X) : 0 < B := by
  rw [hB]; linarith

/-- Lemma 76, transition items G4, R1, G5a, G5b. -/
theorem lifted_rel_trans {m ns : ℕ} {ds : ℝ} (hA : Adm m ns ds) :
    ∀ j, j + 1 < Jn m ns →
      fval (UB m ns j) (SB m ns j) (VB m ns j) (gpt m ns ds (j + 1) 0) < 0 ∧
      fval (UB m ns j) (SB m ns j) (VB m ns j) (gpt m ns ds (j + 1) 1) < 0 ∧
      0 < fval (UA m ns (j + 1)) (SA m ns (j + 1)) (VA m ns (j + 1)) (gpt m ns ds j 2) ∧
      0 < fval (UA m ns (j + 1)) (SA m ns (j + 1)) (VA m ns (j + 1)) (gpt m ns ds j 3) := by
  intro j hj
  obtain ⟨hm, h30, hds, hns1⟩ := id hA
  have hns : 1 ≤ ns := by
    rcases Nat.eq_zero_or_pos ns with h | h
    · subst h; simp at h30
    · exact h
  obtain ⟨hg0, hg1, -, -, -, -⟩ := J_spec hA
  have hj' : j < Jn m ns := by omega
  have hCT := class_trans m ns j hm hns
  have hFj := face_basic _ _ hCT.1
  have hFn := face_basic _ _ (class_trans m ns (j + 1) hm hns).1
  have hN := normalization m ns j hm
  obtain ⟨hs0, hs1, -, hcwB, -, hVB, hHj⟩ := cw_bound hA j hj'
  obtain ⟨hs0n, hs1n, hcwAn, -, hVAn, -, hHn⟩ := cw_bound hA (j + 1) hj
  have hWC := (w_cons hA).2.2 j hj
  have hGL := (gadget_lines hA).2 j hj
  obtain ⟨hL4, hLR1⟩ := trans_L4 _ _ _ (gP m ns) hCT.2 hg0.le hg1
  obtain ⟨hL5a, hL5b⟩ := trans_L5 _ _ _ (gP m ns) hCT.2 hg0.le hg1
  have hwB : wB m ns j = wA m ns (j + 1) := by
    unfold wB wA; rw [Finset.prod_range_succ]; ring
  have hwBpos : 0 < wB m ns j := by
    have := (w_envelope hA).1 (j + 1) hj.le
    rw [hwB]; unfold o0 at this; linarith [this.1]
  have hc0 : 0 ≤ cOf (sig ns ds j) := by unfold cOf; apply div_nonneg hs0; linarith
  have hc0n : 0 ≤ cOf (sig ns ds (j + 1)) := by
    unfold cOf; apply div_nonneg hs0n; linarith
  -- lines in the frame of gadget `j`
  have eB : ∀ t, UB m ns j * (1 - t) + SB m ns j * t =
      Hh m ns j + gP m ns * fbeta (uOf m ns j) (dlt m) t := by
    intro t; unfold UB SB beJ fbeta; ring
  have eA : ∀ t, UA m ns (j + 1) * (1 - t) + SA m ns (j + 1) * t =
      Hh m ns j + gP m ns * falphaN (uOf m ns j) (uOf m ns (j + 1)) (dlt m) t := by
    intro t; rw [← hN.2.1 t]; unfold UA SA alJ falpha; ring
  have eS : SB m ns j - SA m ns (j + 1) =
      gP m ns * tP (uOf m ns j) (uOf m ns (j + 1)) (dlt m) := by
    have h1 := eA 1; have h2 := eB 1
    simp only [sub_self, mul_zero, zero_add, mul_one] at h1 h2
    rw [h1, h2]; unfold tP; ring
  have hP : 0 < tP (uOf m ns j) (uOf m ns (j + 1)) (dlt m) := by
    have : 0 < gP m ns * tP (uOf m ns j) (uOf m ns (j + 1)) (dlt m) := by
      rw [← eS]; linarith [hGL.2]
    exact pos_of_mul_pos_right this hg0.le
  have edV : VB m ns j - VA m ns (j + 1) =
      wB m ns j * (gP m ns * tP (uOf m ns j) (uOf m ns (j + 1)) (dlt m)) := by
    rw [← eS]; unfold VB VA; rw [← hwB]; ring
  have hgP : 0 ≤ gP m ns * tP (uOf m ns j) (uOf m ns (j + 1)) (dlt m) :=
    (mul_pos hg0 hP).le
  have hH1 : Hh m ns (j + 1) = Hh m ns j - gP m ns * fd (uOf m ns j) (dlt m) := hN.1
  have hkn : 0 < 1 + cOf (sig ns ds (j + 1)) * VA m ns (j + 1) := by
    have := mul_nonneg hc0n (by linarith : (0:ℝ) ≤ VA m ns (j + 1)); linarith
  have hkj : 0 < 1 + cOf (sig ns ds j) * VB m ns j := by
    have := mul_nonneg hc0 (by linarith : (0:ℝ) ≤ VB m ns j); linarith
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- G4: `xa_{j+1}` against `T_B(j)`
    have g0 : gpt m ns ds (j + 1) 0 = liftPt (sig ns ds (j + 1)) (fa' (uOf m ns (j + 1)) (dlt m))
        (Hh m ns (j + 1) + gP m ns * epsJ m ns (j + 1)) (VA m ns (j + 1)) := by
      simp [gpt, ptT, ptL, ptV]
    have hH := hHn 0 (by norm_num)
    simp only [ptL, ptV, if_true, show (0:ℕ) < 2 by norm_num] at hH
    rw [g0, lift_id _ _ _ _ _ _ _ hkn (by linarith) (by linarith), eB]
    apply mul_neg_of_pos_of_neg (div_pos (by linarith) (by linarith))
    have hb := cw_le hs0n hs1n hVAn hwBpos hH
    have ho0 : 0 ≤ epsJ m ns (j + 1) := hFn.1.le
    have he1 : epsJ m ns (j + 1) < 1 := hFn.2.1
    have hw := hWC (epsJ m ns (j + 1)) (by linarith) (by linarith)
    rw [max_eq_left ho0] at hw
    have hX := mul_le_mul_of_nonneg_left ((hb.trans_eq (by ring)).trans hw) hgP
    rw [edV]
    have key : Hh m ns (j + 1) + gP m ns * epsJ m ns (j + 1) -
        (Hh m ns j + gP m ns * fbeta (uOf m ns j) (dlt m) (fa' (uOf m ns (j + 1)) (dlt m))) =
        -(gP m ns * (tL4 (uOf m ns j) (uOf m ns (j + 1)) (dlt m) (gP m ns) +
          KC * (2 + gP m ns * epsJ m ns (j + 1)) *
            tP (uOf m ns j) (uOf m ns (j + 1)) (dlt m))) := by
      rw [hH1]; unfold tL4 epsJ; ring
    rw [key]
    refine fin_neg hX (mul_pos hg0 hL4) ?_
    ring
  · -- R1: `ya_{j+1}` against `T_B(j)`
    have g1 : gpt m ns ds (j + 1) 1 = liftPt (sig ns ds (j + 1)) (fb (uOf m ns (j + 1)))
        (Hh m ns (j + 1)) (VA m ns (j + 1)) := by
      simp [gpt, ptT, ptL, ptV]
    have hH := hHn 1 (by norm_num)
    simp only [ptL, ptV, one_ne_zero, if_false, if_true, show (1:ℕ) < 2 by norm_num] at hH
    rw [g1, lift_id _ _ _ _ _ _ _ hkn (by linarith) (by linarith), eB]
    apply mul_neg_of_pos_of_neg (div_pos (by linarith) (by linarith))
    have hb := cw_le hs0n hs1n hVAn hwBpos hH
    have hw := hWC 0 (by norm_num) (by norm_num)
    rw [max_self] at hw
    simp only [mul_zero, add_zero] at hw
    have hX := mul_le_mul_of_nonneg_left ((hb.trans_eq (by ring)).trans hw) hgP
    rw [edV]
    have key : Hh m ns (j + 1) -
        (Hh m ns j + gP m ns * fbeta (uOf m ns j) (dlt m) (fb (uOf m ns (j + 1)))) =
        -(gP m ns * (tLR1 (uOf m ns j) (uOf m ns (j + 1)) (dlt m) +
          2 * KC * tP (uOf m ns j) (uOf m ns (j + 1)) (dlt m))) := by
      rw [hH1]; unfold tLR1; ring
    rw [key]
    refine fin_neg hX (mul_pos hg0 hLR1) ?_
    ring
  · -- G5a: `yb_j` against `T_A(j+1)`
    have g2 : gpt m ns ds j 2 = liftPt (sig ns ds j) (fb' (uOf m ns j) (dlt m))
        (Hh m ns j - gP m ns) (VB m ns j) := by
      simp [gpt, ptT, ptL, ptV]
    have hH := hHj 2 (by norm_num)
    simp only [ptL, ptV, OfNat.ofNat_ne_zero, OfNat.ofNat_ne_one, if_false, if_true,
      lt_irrefl] at hH
    rw [g2, lift_id _ _ _ _ _ _ _ hkj (by linarith) (by linarith), eA]
    apply mul_pos (div_pos (by linarith) (by linarith))
    have hb := cw_le hs0 hs1 hVB hwBpos hH
    have hd := hFj.2.2.2.2.2.2.2.2.2.1
    have hd2 := hFj.2.2.2.2.2.2.2.2.2.2.1
    have ho0 : 0 ≤ fd (uOf m ns j) (dlt m) - 1 := by linarith
    have hw := hWC (fd (uOf m ns j) (dlt m) - 1) (by linarith) (by linarith)
    rw [max_eq_left ho0] at hw
    have hL : Hh m ns j - gP m ns =
        Hh m ns (j + 1) + gP m ns * (fd (uOf m ns j) (dlt m) - 1) := by rw [hH1]; ring
    have hX := mul_le_mul_of_nonneg_left ((hb.trans_eq (by rw [hL]; ring)).trans hw) hgP
    have edV' : VA m ns (j + 1) - VB m ns j =
        -(wB m ns j * (gP m ns * tP (uOf m ns j) (uOf m ns (j + 1)) (dlt m))) := by
      rw [← edV]; ring
    rw [edV']
    have key : Hh m ns j - gP m ns -
        (Hh m ns j + gP m ns *
          falphaN (uOf m ns j) (uOf m ns (j + 1)) (dlt m) (fb' (uOf m ns j) (dlt m))) =
        gP m ns * (tL5a (uOf m ns j) (uOf m ns (j + 1)) (dlt m) (gP m ns) +
          KC * (2 + gP m ns * (fd (uOf m ns j) (dlt m) - 1)) *
            tP (uOf m ns j) (uOf m ns (j + 1)) (dlt m)) := by
      unfold tL5a; ring
    rw [key]
    refine fin_pos hX (mul_pos hg0 hL5a) ?_
    ring
  · -- G5b: `xb_j` against `T_A(j+1)`
    have g3 : gpt m ns ds j 3 = liftPt (sig ns ds j) (fa (uOf m ns j))
        (Hh m ns j - gP m ns * epsJ m ns j) (VB m ns j) := by
      simp [gpt, ptT, ptL, ptV]
    have hH := hHj 3 (by norm_num)
    simp only [ptL, ptV, OfNat.ofNat_ne_zero, OfNat.ofNat_ne_one, if_false,
      show (3:ℕ) ≠ 2 by decide, show ¬ (3:ℕ) < 2 by decide] at hH
    rw [g3, lift_id _ _ _ _ _ _ _ hkj (by linarith) (by linarith), eA]
    apply mul_pos (div_pos (by linarith) (by linarith))
    have hb := cw_le hs0 hs1 hVB hwBpos hH
    have hd := hFj.2.2.2.2.2.2.2.2.2.1
    have hd2 := hFj.2.2.2.2.2.2.2.2.2.2.1
    have he0 := hFj.1
    have he1 := hFj.2.1
    have ho0 : 0 ≤ fd (uOf m ns j) (dlt m) - feps (uOf m ns j) (dlt m) := by linarith
    have hw := hWC (fd (uOf m ns j) (dlt m) - feps (uOf m ns j) (dlt m))
      (by linarith) (by linarith)
    rw [max_eq_left ho0] at hw
    have hL : Hh m ns j - gP m ns * epsJ m ns j =
        Hh m ns (j + 1) + gP m ns * (fd (uOf m ns j) (dlt m) - feps (uOf m ns j) (dlt m)) := by
      rw [hH1]; unfold epsJ; ring
    have hX := mul_le_mul_of_nonneg_left ((hb.trans_eq (by rw [hL]; ring)).trans hw) hgP
    have edV' : VA m ns (j + 1) - VB m ns j =
        -(wB m ns j * (gP m ns * tP (uOf m ns j) (uOf m ns (j + 1)) (dlt m))) := by
      rw [← edV]; ring
    rw [edV']
    have key : Hh m ns j - gP m ns * epsJ m ns j -
        (Hh m ns j + gP m ns *
          falphaN (uOf m ns j) (uOf m ns (j + 1)) (dlt m) (fa (uOf m ns j))) =
        gP m ns * (tL5b (uOf m ns j) (uOf m ns (j + 1)) (dlt m) (gP m ns) +
          KC * (2 + gP m ns * (fd (uOf m ns j) (dlt m) - feps (uOf m ns j) (dlt m))) *
            tP (uOf m ns j) (uOf m ns (j + 1)) (dlt m)) := by
      unfold tL5b epsJ; ring
    rw [key]
    refine fin_pos hX (mul_pos hg0 hL5b) ?_
    ring

end Q2CL
