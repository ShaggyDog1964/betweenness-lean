import Q2CL.Defs
import Q2CL.ChainNormal
import Q2CL.ChordLemma
import Q2CL.Normalization
import Q2CL.GadgetLines
import Q2CL.LiftOn
import Q2CL.CwBound
import Q2CL.ClassTrans

namespace Q2CL

open K4

/-- A vector acting on a lifted point of a line `(U, S)` with state `V`. -/
private lemma dot_lift (w : Lot 4) (s t U S V : ℝ) (hs : s < 1) (hk : 0 < 1 + cOf s * V)
    (hH : 0 < hLift s (U * (1 - t) + S * t) V) :
    dot w (liftPt s t (U * (1 - t) + S * t) V) =
      (1 - s) / (1 + hLift s (U * (1 - t) + S * t) V) *
        ((w 2 + cOf s * w 3) *
            (((U - cOf s * V) * (1 - t) + (S - cOf s * V) * t) / (1 + cOf s * V)) +
          w 0 * (1 - t) + w 1 * t + cOf s * w 3) := by
  have hL : ((U - cOf s * V) * (1 - t) + (S - cOf s * V) * t) / (1 + cOf s * V) =
      hLift s (U * (1 - t) + S * t) V := by
    unfold hLift; congr 1; ring
  rw [hL]
  unfold dot
  rw [Fin.sum_univ_four]
  simp only [liftPt, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Matrix.cons_val_three]
  generalize hLift s (U * (1 - t) + S * t) V = H at hH ⊢
  have h1 : (1 - s) ≠ 0 := by linarith
  have h2 : (1 + H) ≠ 0 := by linarith
  unfold cOf
  field_simp
  ring

/-- Separation of two lines: the vector's line is below the point line at `t1` and above
at `t2`. -/
private lemma sepA (a0 a1 a2 a3 c P0 P1 K t1 t2 : ℝ) (hK : 0 < K) (hm : 0 < a2 + c * a3)
    (hP0 : 0 < P0) (hP1 : 0 < P1) (ht1 : 0 ≤ t1) (ht : t1 < t2) (ht2 : t2 ≤ 1)
    (h1 : 0 < (a2 + c * a3) * ((P0 * (1 - t1) + P1 * t1) / K) + a0 * (1 - t1) + a1 * t1 +
      c * a3)
    (h2 : (a2 + c * a3) * ((P0 * (1 - t2) + P1 * t2) / K) + a0 * (1 - t2) + a1 * t2 +
      c * a3 < 0) :
    (-a0 - c * a3) * P1 < P0 * (-a1 - c * a3) := by
  have hμ : 0 < (a2 + c * a3) / K := div_pos hm hK
  have r1 : (a2 + c * a3) * ((P0 * (1 - t1) + P1 * t1) / K) =
      (a2 + c * a3) / K * (P0 * (1 - t1) + P1 * t1) := by ring
  have r2 : (a2 + c * a3) * ((P0 * (1 - t2) + P1 * t2) / K) =
      (a2 + c * a3) / K * (P0 * (1 - t2) + P1 * t2) := by ring
  rw [r1] at h1
  rw [r2] at h2
  generalize (a2 + c * a3) / K = μ at hμ h1 h2
  have D1 : (-a0 - c * a3 - μ * P0) * (1 - t1) + (-a1 - c * a3 - μ * P1) * t1 < 0 := by
    have : (-a0 - c * a3 - μ * P0) * (1 - t1) + (-a1 - c * a3 - μ * P1) * t1 =
      -(μ * (P0 * (1 - t1) + P1 * t1) + a0 * (1 - t1) + a1 * t1 + c * a3) := by ring
    linarith
  have D2 : 0 < (-a0 - c * a3 - μ * P0) * (1 - t2) + (-a1 - c * a3 - μ * P1) * t2 := by
    have : (-a0 - c * a3 - μ * P0) * (1 - t2) + (-a1 - c * a3 - μ * P1) * t2 =
      -(μ * (P0 * (1 - t2) + P1 * t2) + a0 * (1 - t2) + a1 * t2 + c * a3) := by ring
    linarith
  generalize he0 : -a0 - c * a3 - μ * P0 = e0 at D1 D2
  generalize he1 : -a1 - c * a3 - μ * P1 = e1 at D1 D2
  have hd : 0 < t2 - t1 := by linarith
  have hinc : 0 < e1 - e0 := by
    by_contra hc; rw [not_lt] at hc
    have := mul_nonpos_of_nonpos_of_nonneg hc hd.le
    nlinarith
  have he0n : e0 < 0 := by nlinarith [mul_nonneg ht1 hinc.le]
  have he1p : 0 < e1 := by nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ 1 - t2) hinc.le]
  have k : (-a0 - c * a3) * P1 - P0 * (-a1 - c * a3) = e0 * P1 - P0 * e1 := by
    rw [← he0, ← he1]; ring
  nlinarith [mul_neg_of_neg_of_pos he0n hP1, mul_pos hP0 he1p]

/-- Separation, reversed: above at `t1`, below at `t2`. -/
private lemma sepB (a0 a1 a2 a3 c P0 P1 K t1 t2 : ℝ) (hK : 0 < K) (hm : 0 < a2 + c * a3)
    (hP0 : 0 < P0) (hP1 : 0 < P1) (ht1 : 0 ≤ t1) (ht : t1 < t2) (ht2 : t2 ≤ 1)
    (h1 : (a2 + c * a3) * ((P0 * (1 - t1) + P1 * t1) / K) + a0 * (1 - t1) + a1 * t1 +
      c * a3 < 0)
    (h2 : 0 < (a2 + c * a3) * ((P0 * (1 - t2) + P1 * t2) / K) + a0 * (1 - t2) + a1 * t2 +
      c * a3) :
    P0 * (-a1 - c * a3) < (-a0 - c * a3) * P1 := by
  have hμ : 0 < (a2 + c * a3) / K := div_pos hm hK
  have r1 : (a2 + c * a3) * ((P0 * (1 - t1) + P1 * t1) / K) =
      (a2 + c * a3) / K * (P0 * (1 - t1) + P1 * t1) := by ring
  have r2 : (a2 + c * a3) * ((P0 * (1 - t2) + P1 * t2) / K) =
      (a2 + c * a3) / K * (P0 * (1 - t2) + P1 * t2) := by ring
  rw [r1] at h1
  rw [r2] at h2
  generalize (a2 + c * a3) / K = μ at hμ h1 h2
  have D1 : 0 < (-a0 - c * a3 - μ * P0) * (1 - t1) + (-a1 - c * a3 - μ * P1) * t1 := by
    have : (-a0 - c * a3 - μ * P0) * (1 - t1) + (-a1 - c * a3 - μ * P1) * t1 =
      -(μ * (P0 * (1 - t1) + P1 * t1) + a0 * (1 - t1) + a1 * t1 + c * a3) := by ring
    linarith
  have D2 : (-a0 - c * a3 - μ * P0) * (1 - t2) + (-a1 - c * a3 - μ * P1) * t2 < 0 := by
    have : (-a0 - c * a3 - μ * P0) * (1 - t2) + (-a1 - c * a3 - μ * P1) * t2 =
      -(μ * (P0 * (1 - t2) + P1 * t2) + a0 * (1 - t2) + a1 * t2 + c * a3) := by ring
    linarith
  generalize he0 : -a0 - c * a3 - μ * P0 = e0 at D1 D2
  generalize he1 : -a1 - c * a3 - μ * P1 = e1 at D1 D2
  have hd : 0 < t2 - t1 := by linarith
  have hdec : e1 - e0 < 0 := by
    by_contra hc; rw [not_lt] at hc
    have := mul_nonneg hc hd.le
    nlinarith
  have he0p : 0 < e0 := by nlinarith [mul_nonneg ht1 (neg_nonneg.2 hdec.le)]
  have he1n : e1 < 0 := by
    nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ 1 - t2) (neg_nonneg.2 hdec.le)]
  have k : (-a0 - c * a3) * P1 - P0 * (-a1 - c * a3) = e0 * P1 - P0 * e1 := by
    rw [← he0, ← he1]; ring
  nlinarith [mul_pos he0p hP1, mul_neg_of_pos_of_neg hP0 he1n]

private lemma rEff_eq (U S φ : ℝ) (hS : 0 < S) (hφ : φ < 1) :
    rEff (U / S) φ = (U - φ * S) / (S - φ * S) := by
  have h1 : S ≠ 0 := hS.ne'
  have h2 : (1 - φ) ≠ 0 := by linarith
  have h3 : S - φ * S = S * (1 - φ) := by ring
  unfold rEff
  rw [h3, div_sub' h1, div_div]
  ring_nf

private lemma ratio_form (a0 a1 a3 c : ℝ) (ha1 : a1 < 0) :
    a0 / a1 - c * (a3 / -a1) = (-a0 - c * a3) / (-a1) ∧
      1 - c * (a3 / -a1) = (-a1 - c * a3) / (-a1) := by
  have h : -a1 ≠ 0 := by linarith
  have h' : a1 ≠ 0 := by linarith
  constructor
  · field_simp; ring
  · field_simp
    ring

private lemma convA (a0 a1 a3 c U S φ : ℝ) (ha1 : a1 < 0) (hS : 0 < S) (hφ : φ < 1)
    (h : (-a0 - c * a3) * (S - φ * S) < (U - φ * S) * (-a1 - c * a3)) :
    a0 / a1 - c * (a3 / -a1) < rEff (U / S) φ * (1 - c * (a3 / -a1)) := by
  obtain ⟨e1, e2⟩ := ratio_form a0 a1 a3 c ha1
  rw [e1, e2, rEff_eq U S φ hS hφ]
  have hSφ : 0 < S - φ * S := by nlinarith
  have hn : 0 < -a1 := by linarith
  rw [div_mul_div_comm, div_lt_div_iff₀ hn (mul_pos hSφ hn)]
  nlinarith

private lemma convB (a0 a1 a3 c U S φ : ℝ) (ha1 : a1 < 0) (hS : 0 < S) (hφ : φ < 1)
    (h : (U - φ * S) * (-a1 - c * a3) < (-a0 - c * a3) * (S - φ * S)) :
    rEff (U / S) φ * (1 - c * (a3 / -a1)) < a0 / a1 - c * (a3 / -a1) := by
  obtain ⟨e1, e2⟩ := ratio_form a0 a1 a3 c ha1
  rw [e1, e2, rEff_eq U S φ hS hφ]
  have hSφ : 0 < S - φ * S := by nlinarith
  have hn : 0 < -a1 := by linarith
  rw [div_mul_div_comm, div_lt_div_iff₀ (mul_pos hSφ hn) hn]
  nlinarith

private lemma final_step (c Ω1 Ω2 R1 R2 a b : ℝ) (hb : 0 < b) (hΩ1 : 0 < Ω1)
    (hΩ2 : 0 < Ω2) (h12 : Ω1 * R2 ≤ Ω2 * R1) (h1 : R1 - c * Ω1 < a * (1 - c * Ω1))
    (h2 : b * (1 - c * Ω2) < R2 - c * Ω2) :
    Ω1 * b / (a + c * Ω1 * (b - a)) < Ω2 := by
  have k1 := mul_lt_mul_of_pos_left h1 hΩ2
  have k2 := mul_lt_mul_of_pos_left h2 hΩ1
  have key : Ω1 * b < Ω2 * (a + c * Ω1 * (b - a)) := by nlinarith
  have hD : 0 < a + c * Ω1 * (b - a) := by
    by_contra hc; rw [not_lt] at hc
    have := mul_nonpos_of_nonneg_of_nonpos hΩ2.le hc
    nlinarith [mul_pos hΩ1 hb]
  rw [div_lt_iff₀ hD]; linarith

set_option maxHeartbeats 1600000 in
/-- Step through gadget `j` (proof of Proposition 71, non-representability): with `α = 4j+1`
the vector after
`xa_j` and `β = 4j+3` the vector after `yb_j`, any chain has `ω_β > F_j(ω_α)`. -/
theorem gadget_omega_step {m ns : ℕ} {ds : ℝ} (hA : Adm m ns ds) (W : ℕ → Lot 4)
    (hW : IsChainFn (4 * Jn m ns + 2) (Tpt m ns ds) W) :
    ∀ j, j < Jn m ns →
      transF m ns ds j (W (4 * j + 1) 3 / -W (4 * j + 1) 1) <
        W (4 * j + 3) 3 / -W (4 * j + 3) 1 := by
  intro j hj
  obtain ⟨hNorm, hMono, -, -⟩ := chain_normal hA W hW
  have hm : 2 ≤ m := hA.1
  have hns : 1 ≤ ns := by
    rcases Nat.eq_zero_or_pos ns with h | h
    · have := hA.2.1; subst h; simp at this
    · exact h
  obtain ⟨hs0, hs1, hcwA, hcwB, hVA, hVB, hHp⟩ := cw_bound hA j hj
  obtain ⟨hSB, hSBA, hSAU, hSBU, -⟩ := (gadget_lines hA).1 j hj
  obtain ⟨-, hg1, -⟩ := J_spec hA
  have hN := normalization m ns j hm
  obtain ⟨hd0, hd5, hu0, hu1⟩ := (class_trans m ns j hm hns).1
  -- times
  have t0 : ptT m ns j 0 = fa' (uOf m ns j) (dlt m) := by simp [ptT]
  have t1 : ptT m ns j 1 = fb (uOf m ns j) := by simp [ptT]
  have t2 : ptT m ns j 2 = fb' (uOf m ns j) (dlt m) := by simp [ptT]
  have t3 : ptT m ns j 3 = fa (uOf m ns j) := by simp [ptT]
  have ht0 : 0 ≤ ptT m ns j 0 := by rw [t0]; unfold fa' fa; positivity
  have ht01 : ptT m ns j 0 < ptT m ns j 1 := by rw [t0, t1]; unfold fa' fa fb; linarith
  have ht1 : ptT m ns j 1 ≤ 1 := by rw [t1]; unfold fb; linarith
  have ht3 : 0 ≤ ptT m ns j 3 := by rw [t3]; unfold fa; positivity
  have ht32 : ptT m ns j 3 < ptT m ns j 2 := by rw [t3, t2]; unfold fa fb' fb; linarith
  have ht2 : ptT m ns j 2 ≤ 1 := by rw [t2]; unfold fb' fb; linarith
  -- points
  have e0 : Tpt m ns ds (4 * j + 1) = gpt m ns ds j 0 := by
    unfold Tpt; rw [if_neg (by omega), if_neg (by omega)]
    rw [show (4 * j + 1 - 1) / 4 = j by omega, show (4 * j + 1 - 1) % 4 = 0 by omega]
  have e1 : Tpt m ns ds (4 * j + 1 + 1) = gpt m ns ds j 1 := by
    unfold Tpt; rw [if_neg (by omega), if_neg (by omega)]
    rw [show (4 * j + 1 + 1 - 1) / 4 = j by omega, show (4 * j + 1 + 1 - 1) % 4 = 1 by omega]
  have e2 : Tpt m ns ds (4 * j + 3) = gpt m ns ds j 2 := by
    unfold Tpt; rw [if_neg (by omega), if_neg (by omega)]
    rw [show (4 * j + 3 - 1) / 4 = j by omega, show (4 * j + 3 - 1) % 4 = 2 by omega]
  have e3 : Tpt m ns ds (4 * j + 3 + 1) = gpt m ns ds j 3 := by
    unfold Tpt; rw [if_neg (by omega), if_neg (by omega)]
    rw [show (4 * j + 3 + 1 - 1) / 4 = j by omega, show (4 * j + 3 + 1 - 1) % 4 = 3 by omega]
  have pv0 : ptV m ns j 0 = VA m ns j := by simp [ptV]
  have pv1 : ptV m ns j 1 = VA m ns j := by simp [ptV]
  have pv2 : ptV m ns j 2 = VB m ns j := by simp [ptV]
  have pv3 : ptV m ns j 3 = VB m ns j := by simp [ptV]
  have g0 : gpt m ns ds j 0 = liftPt (sig ns ds j) (ptT m ns j 0)
      (UA m ns j * (1 - ptT m ns j 0) + SA m ns j * ptT m ns j 0) (VA m ns j) := by
    unfold gpt; rw [← hN.2.2.1 0 (by norm_num), pv0]
  have g1 : gpt m ns ds j 1 = liftPt (sig ns ds j) (ptT m ns j 1)
      (UA m ns j * (1 - ptT m ns j 1) + SA m ns j * ptT m ns j 1) (VA m ns j) := by
    unfold gpt; rw [← hN.2.2.1 1 (by norm_num), pv1]
  have g2 : gpt m ns ds j 2 = liftPt (sig ns ds j) (ptT m ns j 2)
      (UB m ns j * (1 - ptT m ns j 2) + SB m ns j * ptT m ns j 2) (VB m ns j) := by
    unfold gpt; rw [← hN.2.2.2 2 (by norm_num) (by norm_num), pv2]
  have g3 : gpt m ns ds j 3 = liftPt (sig ns ds j) (ptT m ns j 3)
      (UB m ns j * (1 - ptT m ns j 3) + SB m ns j * ptT m ns j 3) (VB m ns j) := by
    unfold gpt; rw [← hN.2.2.2 3 (by norm_num) (by norm_num), pv3]
  have hH0 := hHp 0 (by norm_num)
  have hH1 := hHp 1 (by norm_num)
  have hH2 := hHp 2 (by norm_num)
  have hH3 := hHp 3 (by norm_num)
  rw [hN.2.2.1 0 (by norm_num), pv0] at hH0
  rw [hN.2.2.1 1 (by norm_num), pv1] at hH1
  rw [hN.2.2.2 2 (by norm_num) (by norm_num), pv2] at hH2
  rw [hN.2.2.2 3 (by norm_num) (by norm_num), pv3] at hH3
  -- constants
  have hc0 : 0 ≤ cOf (sig ns ds j) := by
    unfold cOf; apply div_nonneg hs0; linarith
  have hs : sig ns ds j < 1 := by linarith
  have hSB0 : 0 < SB m ns j := by linarith
  have hSA0 : 0 < SA m ns j := by linarith
  have hwA0 : 0 < wA m ns j := by
    have := hVA; unfold VA at this
    by_contra h; rw [not_lt] at h; nlinarith
  have hwB0 : 0 < wB m ns j := by
    have := hVB; unfold VB at this
    by_contra h; rw [not_lt] at h; nlinarith
  have hκA : cOf (sig ns ds j) * VA m ns j = cOf (sig ns ds j) * wA m ns j * SA m ns j := by
    unfold VA; ring
  have hκB : cOf (sig ns ds j) * VB m ns j = cOf (sig ns ds j) * wB m ns j * SB m ns j := by
    unfold VB; ring
  have hKA : 0 < 1 + cOf (sig ns ds j) * VA m ns j := by
    have := mul_nonneg hc0 (by linarith : (0:ℝ) ≤ VA m ns j); linarith
  have hKB : 0 < 1 + cOf (sig ns ds j) * VB m ns j := by
    have := mul_nonneg hc0 (by linarith : (0:ℝ) ≤ VB m ns j); linarith
  have hκA1 : cOf (sig ns ds j) * VA m ns j ≤ 25 / 44 * SA m ns j := by
    rw [hκA]; exact mul_le_mul_of_nonneg_right hcwA hSA0.le
  have hκB1 : cOf (sig ns ds j) * VB m ns j ≤ 25 / 44 * SB m ns j := by
    rw [hκB]; exact mul_le_mul_of_nonneg_right hcwB hSB0.le
  have hPA1 : 0 < SA m ns j - cOf (sig ns ds j) * VA m ns j := by linarith
  have hPA0 : 0 < UA m ns j - cOf (sig ns ds j) * VA m ns j := by linarith
  have hPB1 : 0 < SB m ns j - cOf (sig ns ds j) * VB m ns j := by linarith
  have hPB0 : 0 < UB m ns j - cOf (sig ns ds j) * VB m ns j := by linarith
  -- chain facts
  have hα := hNorm (4 * j + 1) (by omega) (by omega)
  have hβ := hNorm (4 * j + 3) (by omega) (by omega)
  have cα := hW.1 (4 * j + 1) (by omega)
  have cβ := hW.1 (4 * j + 3) (by omega)
  rw [e0, g0] at cα
  rw [e2, g2] at cβ
  have cα2 := cα.2.2
  have cβ2 := cβ.2.2
  rw [e1, g1] at cα2
  rw [e3, g3] at cβ2
  have cα1 := cα.2.1
  have cβ1 := cβ.2.1
  -- dot identities
  rw [dot_lift _ _ _ _ _ _ hs hKA hH0] at cα1
  rw [dot_lift _ _ _ _ _ _ hs hKA hH1] at cα2
  rw [dot_lift _ _ _ _ _ _ hs hKB hH2] at cβ1
  rw [dot_lift _ _ _ _ _ _ hs hKB hH3] at cβ2
  have hpos : ∀ H : ℝ, 0 < H → 0 < (1 - sig ns ds j) / (1 + H) := fun H hH =>
    div_pos (by linarith) (by linarith)
  have pα1 := pos_of_mul_pos_right cα1 (hpos _ hH0).le
  have pβ1 := pos_of_mul_pos_right cβ1 (hpos _ hH2).le
  have nα2 := (neg_of_mul_neg_right cα2 (hpos _ hH1).le)
  have nβ2 := (neg_of_mul_neg_right cβ2 (hpos _ hH3).le)
  obtain ⟨hα2, hα1, hα01, hα23⟩ := hα
  obtain ⟨hβ2, hβ1, hβ01, hβ23⟩ := hβ
  have hmα : 0 < W (4 * j + 1) 2 + cOf (sig ns ds j) * W (4 * j + 1) 3 := by
    have := mul_nonneg hc0 (by linarith : (0:ℝ) ≤ W (4 * j + 1) 3); linarith
  have hmβ : 0 < W (4 * j + 3) 2 + cOf (sig ns ds j) * W (4 * j + 3) 3 := by
    have := mul_nonneg hc0 (by linarith : (0:ℝ) ≤ W (4 * j + 3) 3); linarith
  have sA := sepA _ _ _ _ _ _ _ _ _ _ hKA hmα hPA0 hPA1 ht0 ht01 ht1 pα1 nα2
  have sB := sepB _ _ _ _ _ _ _ _ _ _ hKB hmβ hPB0 hPB1 ht3 ht32 ht2 nβ2 pβ1
  rw [hκA] at sA
  rw [hκB] at sB
  have hφA : cOf (sig ns ds j) * wA m ns j < 1 := by linarith
  have hφB : cOf (sig ns ds j) * wB m ns j < 1 := by linarith
  have k1 := convA _ _ _ _ _ _ _ hα1 hSA0 hφA sA
  have k2 := convB _ _ _ _ _ _ _ hβ1 hSB0 hφB sB
  have hb : 0 < rEff (UB m ns j / SB m ns j) (cOf (sig ns ds j) * wB m ns j) := by
    unfold rEff
    have : 1 < UB m ns j / SB m ns j := (one_lt_div hSB0).2 hSBU
    apply div_pos <;> linarith
  have hΩ1 : 0 < W (4 * j + 1) 3 / -W (4 * j + 1) 1 := div_pos (by linarith) (by linarith)
  have hΩ2 : 0 < W (4 * j + 3) 3 / -W (4 * j + 3) 1 := div_pos (by linarith) (by linarith)
  -- monotonicity of `V/U`
  have m1 : W (4 * j + 1) 3 / -W (4 * j + 1) 0 ≤ W (4 * j + 2) 3 / -W (4 * j + 2) 0 :=
    (hMono (4 * j + 1) (by omega) (by omega)).2
  have m2 : W (4 * j + 2) 3 / -W (4 * j + 2) 0 ≤ W (4 * j + 3) 3 / -W (4 * j + 3) 0 :=
    (hMono (4 * j + 2) (by omega) (by omega)).2
  have m12 := le_trans m1 m2
  rw [div_le_div_iff₀ (by linarith) (by linarith)] at m12
  have h12 : W (4 * j + 1) 3 / -W (4 * j + 1) 1 * (W (4 * j + 3) 0 / W (4 * j + 3) 1) ≤
      W (4 * j + 3) 3 / -W (4 * j + 3) 1 * (W (4 * j + 1) 0 / W (4 * j + 1) 1) := by
    have n1 : W (4 * j + 1) 1 ≠ 0 := by linarith
    have n3 : W (4 * j + 3) 1 ≠ 0 := by linarith
    have : W (4 * j + 3) 3 / -W (4 * j + 3) 1 * (W (4 * j + 1) 0 / W (4 * j + 1) 1) -
        W (4 * j + 1) 3 / -W (4 * j + 1) 1 * (W (4 * j + 3) 0 / W (4 * j + 3) 1) =
        (W (4 * j + 3) 3 * -W (4 * j + 1) 0 - W (4 * j + 1) 3 * -W (4 * j + 3) 0) /
          (W (4 * j + 1) 1 * W (4 * j + 3) 1) := by
      field_simp
    have hd : 0 < W (4 * j + 1) 1 * W (4 * j + 3) 1 := mul_pos_of_neg_of_neg hα1 hβ1
    have := div_nonneg (by linarith : (0:ℝ) ≤
      W (4 * j + 3) 3 * -W (4 * j + 1) 0 - W (4 * j + 1) 3 * -W (4 * j + 3) 0) hd.le
    linarith
  unfold transF
  exact final_step _ _ _ _ _ _ _ hb hΩ1 hΩ2 h12 k1 k2

end Q2CL
