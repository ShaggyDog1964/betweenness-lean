import Q2CL.Defs
import Q2CL.LiftedRelGadget
import Q2CL.FaceBasic
import Q2CL.CwBound
import Q2CL.GadgetLines
import Q2CL.WEnvelope
import Q2CL.WCons
import Q2CL.SliceEval
import Q2CL.TightNest
import Q2CL.ClassTrans
import Q2CL.JSpec

namespace Q2CL

open K4

/-- Lifting identity (Lemma 75(3)), multiplied out (copy of the private lemma in
`Q2CL.LiftedRelGadget`). -/
private lemma hx_lift_id (U S V s t L V' : ℝ) (hs : s < 1) (hk : 1 + cOf s * V ≠ 0)
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

/-- The final arithmetic step: from the lifting identity to the four conclusions. -/
private lemma hx_final {s Hp f VA VB c g A L : ℝ} (hs : s < 1) (hHp : 0 < Hp) (hf : f < 0)
    (hc : 0 ≤ c) (hVAB : VB ≤ VA) (hg : 0 < g)
    (hid : f * (1 + Hp) = (1 - s) * (L - A + c * (1 + Hp) * (VA - VB)))
    (hAL : A - L ≤ 8 * g) (hkey : 8 * g < Hp * (VA - 1)) :
    0 < (1 - s) * (Hp / (1 + Hp)) ∧
    0 < (1 - s) * (Hp / (1 + Hp)) / ((1 - s) * (Hp / (1 + Hp)) - f) ∧
    (1 - s) * (Hp / (1 + Hp)) / ((1 - s) * (Hp / (1 + Hp)) - f) < 1 ∧
    1 < (1 - s) * (Hp / (1 + Hp)) / ((1 - s) * (Hp / (1 + Hp)) - f) * VA := by
  have hs' : 0 < 1 - s := by linarith
  have h1H : 0 < 1 + Hp := by linarith
  have hp2 : 0 < (1 - s) * (Hp / (1 + Hp)) := by positivity
  have hden : 0 < (1 - s) * (Hp / (1 + Hp)) - f := by linarith
  refine ⟨hp2, div_pos hp2 hden, (div_lt_one hden).2 (by linarith), ?_⟩
  rw [div_mul_eq_mul_div, one_lt_div hden]
  -- `-f < p2 (VA - 1)`, after multiplying by `1 + Hp`
  have hp2e : (1 - s) * (Hp / (1 + Hp)) * (1 + Hp) = (1 - s) * Hp := by
    field_simp
  have hT : 0 ≤ c * (1 + Hp) * (VA - VB) := by
    apply mul_nonneg (mul_nonneg hc h1H.le); linarith
  have hlhs : -f * (1 + Hp) ≤ (1 - s) * (8 * g) := by
    have : -f * (1 + Hp) = (1 - s) * (A - L - c * (1 + Hp) * (VA - VB)) := by
      linear_combination (-1 : ℝ) * hid
    rw [this]
    apply mul_le_mul_of_nonneg_left _ hs'.le
    linarith
  have hrhs : (1 - s) * (8 * g) < (1 - s) * (Hp / (1 + Hp)) * (VA - 1) * (1 + Hp) := by
    have : (1 - s) * (Hp / (1 + Hp)) * (VA - 1) * (1 + Hp) = (1 - s) * (Hp * (VA - 1)) := by
      rw [mul_right_comm, hp2e]; ring
    rw [this]
    exact mul_lt_mul_of_pos_left hkey hs'
  have : -f < (1 - s) * (Hp / (1 + Hp)) * (VA - 1) := by
    have h3 : -f * (1 + Hp) < (1 - s) * (Hp / (1 + Hp)) * (VA - 1) * (1 + Hp) := by linarith
    exact lt_of_mul_lt_mul_right h3 h1H.le
  linarith

/-- Lower bound `H' ≥ 27/100` for a point lifted from `B` at height `L ≥ SB`. -/
private lemma hx_Hp_lb {Hp L κ SB : ℝ} (e : Hp * (1 + κ) = L - κ) (hκ0 : 0 ≤ κ)
    (hκ : κ ≤ 25 / 44 * SB) (hSBL : SB ≤ L) (hSB : 73 / 75 ≤ SB) : 27 / 100 ≤ Hp := by
  by_contra hlt
  push Not at hlt
  have h1 : Hp * (1 + κ) < 27 / 100 * (1 + κ) := mul_lt_mul_of_pos_right hlt (by linarith)
  nlinarith

theorem hom_X {m ns : ℕ} {ds : ℝ} (hA : Adm m ns ds) :
    wA m ns (Jn m ns - 1) < o1 m ns ∧
    ∀ τ, 2 ≤ τ → τ < 4 →
      0 < (gpt m ns ds (Jn m ns - 1) τ) 2 ∧
      0 < (gpt m ns ds (Jn m ns - 1) τ) 2 /
        ((gpt m ns ds (Jn m ns - 1) τ) 2 -
          fval (UA m ns (Jn m ns - 1)) (SA m ns (Jn m ns - 1)) (VA m ns (Jn m ns - 1))
            (gpt m ns ds (Jn m ns - 1) τ)) ∧
      (gpt m ns ds (Jn m ns - 1) τ) 2 /
        ((gpt m ns ds (Jn m ns - 1) τ) 2 -
          fval (UA m ns (Jn m ns - 1)) (SA m ns (Jn m ns - 1)) (VA m ns (Jn m ns - 1))
            (gpt m ns ds (Jn m ns - 1) τ)) < 1 ∧
      1 < (gpt m ns ds (Jn m ns - 1) τ) 2 /
        ((gpt m ns ds (Jn m ns - 1) τ) 2 -
          fval (UA m ns (Jn m ns - 1)) (SA m ns (Jn m ns - 1)) (VA m ns (Jn m ns - 1))
            (gpt m ns ds (Jn m ns - 1) τ)) * VA m ns (Jn m ns - 1) := by
  have hm : 2 ≤ m := hA.1
  have hns : 1 ≤ ns := by
    rcases Nat.eq_zero_or_pos ns with h | h
    · have := hA.2.1; subst h; simp at this
    · exact h
  obtain ⟨hg0, hg1, hJ2, -, -, -⟩ := J_spec hA
  set j := Jn m ns - 1 with hjdef
  have hj : j < Jn m ns := by omega
  have hj1 : j + 1 = Jn m ns := by omega
  refine ⟨?_, ?_⟩
  · have := (w_envelope hA).2 j hj
    rw [hj1] at this
    exact this
  intro τ hτ2 hτ4
  obtain ⟨hs0, hs1, -, hcwB, hVA1, hVB1, hHpos⟩ := cw_bound hA j hj
  obtain ⟨hSB1, hSBA, hSAU, -, hUBA⟩ := (gadget_lines hA).1 j hj
  obtain ⟨hVBA, -⟩ := (tight_nest hA).1 j hj
  obtain ⟨hfyb, hfxb, -, -⟩ := lifted_rel_gadget hA j hj
  have hGD := class_trans m ns j hm hns |>.1
  obtain ⟨he0, he1, -, hD2, -, -, -, -, -, -, -, hDyb, hDxb⟩ := face_basic _ _ hGD
  have hwA : o0 ≤ wA m ns j := ((w_envelope hA).1 j hj.le).1
  set s := sig ns ds j with hs
  set c := cOf s with hcdef
  set g := gP m ns with hgdef
  set H := Hh m ns j with hHdef
  set u := uOf m ns j with hudef
  set δ := dlt m with hδdef
  set ε := feps u δ with hεdef
  have hs1' : s < 1 := by linarith
  have hc0 : 0 ≤ c := by rw [hcdef]; unfold cOf; apply div_nonneg hs0; linarith
  have hSB0 : 0 < SB m ns j := by linarith
  have hSA0 : 0 < SA m ns j := by linarith
  have hUA0 : 0 < UA m ns j := by linarith
  have hSBlo : 73 / 75 ≤ SB m ns j := by linarith
  -- `VB ≤ VA`
  have hVAB : VB m ns j ≤ VA m ns j := by
    have hVA0 : 0 < VA m ns j := by linarith
    have : VB m ns j * UA m ns j ≤ VA m ns j * UA m ns j := by
      rw [hVBA]; exact mul_le_mul_of_nonneg_left hUBA.le hVA0.le
    exact le_of_mul_le_mul_right this hUA0
  -- `VA - 1 > 23/50`
  have hVAlo : 23 / 50 < VA m ns j - 1 := by
    have hVAe : VA m ns j = wA m ns j * SA m ns j := rfl
    have ho0 : o0 = 3 / 2 := rfl
    have : 3 / 2 * SA m ns j ≤ wA m ns j * SA m ns j :=
      mul_le_mul_of_nonneg_right (by rw [← ho0]; exact hwA) hSA0.le
    linarith
  -- `κ = c VB ≤ (25/44) SB`
  have hκ : c * VB m ns j ≤ 25 / 44 * SB m ns j := by
    have hVBe : VB m ns j = wB m ns j * SB m ns j := rfl
    rw [hVBe, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right hcwB hSB0.le
  have hκ0 : 0 ≤ c * VB m ns j := by nlinarith
  have hkA : 0 < 1 + c * VA m ns j := by nlinarith
  -- `β(1) ≤ -1`, so `SB ≤ H - g`
  have hbe1 : fbeta u δ 1 ≤ -1 := by
    have hsB : fsB u δ < 0 := by
      unfold fsB; exact div_neg_of_neg_of_pos (by linarith) hD2
    have hb' : fb' u δ ≤ 1 := by
      obtain ⟨-, hd1, hu0, hu1⟩ := hGD
      unfold fb' fb; linarith
    unfold fbeta
    have : fsB u δ * (1 - fb' u δ) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hsB.le (by linarith)
    linarith
  have hSBe : SB m ns j = H + g * fbeta u δ 1 := rfl
  have hSBg : SB m ns j ≤ H - g := by
    rw [hSBe]; nlinarith
  have hAt : ∀ t, UA m ns j * (1 - t) + SA m ns j * t = H + g * falpha u δ t := by
    intro t
    show (H + g * alJ m ns j 0) * (1 - t) + (H + g * alJ m ns j 1) * t = _
    unfold alJ falpha; ring
  -- generic: from height `L ≥ SB`, `A_line(t) - L ≤ 8 g`, finish
  have key : ∀ t L, SB m ns j ≤ L → 0 < hLift s L (VB m ns j) →
      fval (UA m ns j) (SA m ns j) (VA m ns j) (liftPt s t L (VB m ns j)) < 0 →
      H + g * falpha u δ t - L ≤ 8 * g →
      0 < (liftPt s t L (VB m ns j)) 2 ∧
      0 < (liftPt s t L (VB m ns j)) 2 / ((liftPt s t L (VB m ns j)) 2 -
          fval (UA m ns j) (SA m ns j) (VA m ns j) (liftPt s t L (VB m ns j))) ∧
      (liftPt s t L (VB m ns j)) 2 / ((liftPt s t L (VB m ns j)) 2 -
          fval (UA m ns j) (SA m ns j) (VA m ns j) (liftPt s t L (VB m ns j))) < 1 ∧
      1 < (liftPt s t L (VB m ns j)) 2 / ((liftPt s t L (VB m ns j)) 2 -
          fval (UA m ns j) (SA m ns j) (VA m ns j) (liftPt s t L (VB m ns j))) *
          VA m ns j := by
    intro t L hSBL hHp hf hAL
    have hp2 : (liftPt s t L (VB m ns j)) 2 =
        (1 - s) * (hLift s L (VB m ns j) / (1 + hLift s L (VB m ns j))) := by
      simp [liftPt]
    rw [hp2]
    have hid := hx_lift_id (UA m ns j) (SA m ns j) (VA m ns j) s t L (VB m ns j) hs1'
      hkA.ne' (by linarith) (by linarith)
    rw [← hcdef, hAt] at hid
    have e : hLift s L (VB m ns j) * (1 + c * VB m ns j) = L - c * VB m ns j := by
      unfold hLift; rw [← hcdef]; field_simp
    have hlb := hx_Hp_lb e hκ0 hκ hSBL hSBlo
    have hkey : 8 * g < hLift s L (VB m ns j) * (VA m ns j - 1) := by
      have : 27 / 100 * (23 / 50) ≤ hLift s L (VB m ns j) * (VA m ns j - 1) :=
        mul_le_mul hlb hVAlo.le (by norm_num) (by linarith)
      linarith
    exact hx_final hs1' hHp hf hc0 hVAB hg0 hid hAL hkey
  have hτ : τ = 2 ∨ τ = 3 := by omega
  rcases hτ with rfl | rfl
  · have hH' := hHpos 2 (by norm_num)
    simp only [gpt, ptT, ptL, ptV, show (2:ℕ) ≠ 0 by decide, show (2:ℕ) ≠ 1 by decide,
      if_true, if_false, show ¬ (2:ℕ) < 2 by decide] at hH' hfyb ⊢
    refine key _ _ hSBg hH' hfyb ?_
    have : falpha u δ (fb' u δ) + 1 < 8 := by unfold fDyb at hDyb; linarith
    nlinarith
  · have hH' := hHpos 3 (by norm_num)
    simp only [gpt, ptT, ptL, ptV, show (3:ℕ) ≠ 0 by decide, show (3:ℕ) ≠ 1 by decide,
      show (3:ℕ) ≠ 2 by decide, if_true, if_false, show ¬ (3:ℕ) < 2 by decide] at hH' hfxb ⊢
    have hε : epsJ m ns j = ε := rfl
    rw [hε] at hH' hfxb ⊢
    have hge : g * ε ≤ g := by
      have := mul_le_mul_of_nonneg_left he1.le hg0.le; linarith
    refine key _ _ (by linarith) hH' hfxb ?_
    have : falpha u δ (fa u) + ε < 8 := by unfold fDxb at hDxb; linarith
    have h2 : g * (falpha u δ (fa u) + ε) ≤ g * 8 := mul_le_mul_of_nonneg_left this.le hg0.le
    linarith

end Q2CL
