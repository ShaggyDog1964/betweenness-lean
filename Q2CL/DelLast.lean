import Q2CL.Defs
import Q2CL.Strictify
import Q2CL.TightNest
import Q2CL.LiftedRelGadget
import Q2CL.LiftedRelTrans
import Q2CL.ReliftDval
import Q2CL.LiftOn
import Q2CL.Normalization
import Q2CL.HomX
import Q2CL.CwBound
import Q2CL.GadgetLines
import Q2CL.JSpec
import Q2CL.SliceEval
import Q2CL.ClassTrans
import Q2CL.FaceBasic

namespace Q2CL

open K4

noncomputable section

/-! The tight-state machinery below is the one of `Q2CL.DelRend` (private there). -/

private def aF (X κ r v : ℝ) : ℝ := ((1 + κ) * r + ((X - κ) / (1 + κ) + 1) * κ * v) / X

private def vsolve (X κ r T : ℝ) : ℝ :=
  (T - (1 + κ) * r / X) / (((X - κ) / (1 + κ) + 1) * κ / X - 1)

private lemma aF_sub (X κ r v : ℝ) :
    aF X κ r v - v = (1 + κ) * r / X + v * (((X - κ) / (1 + κ) + 1) * κ / X - 1) := by
  unfold aF; ring

private lemma coef_neg {X κ : ℝ} (hX : 0 < X) (hκ0 : 0 ≤ κ) (hκX : κ < X) :
    ((X - κ) / (1 + κ) + 1) * κ / X - 1 < 0 := by
  have e : ((X - κ) / (1 + κ) + 1) * κ / X - 1 = (κ - X) / ((1 + κ) * X) := by
    field_simp; ring
  rw [e]; apply div_neg_of_neg_of_pos (by linarith); positivity

private lemma aF_vsolve {X κ : ℝ} (r T : ℝ) (hX : 0 < X) (hκ0 : 0 ≤ κ) (hκX : κ < X) :
    aF X κ r (vsolve X κ r T) - vsolve X κ r T = T := by
  rw [aF_sub]; unfold vsolve
  have hk := (coef_neg hX hκ0 hκX).ne
  generalize ((X - κ) / (1 + κ) + 1) * κ / X - 1 = k at hk ⊢
  field_simp; ring

private lemma aF_mono {X κ r r' : ℝ} (v : ℝ) (hX : 0 < X) (hκ0 : 0 ≤ κ) (hr : r' ≤ r) :
    aF X κ r' v ≤ aF X κ r v := by
  unfold aF
  apply div_le_div_of_nonneg_right _ hX.le
  nlinarith

private lemma on_gen (U S V s t r0 r1 v : ℝ) (hs0 : 0 ≤ s) (hs : s < 1) (hV : 0 ≤ V)
    (hU : 0 < U) (hS : 0 < S) (hH : 0 < hLift s (U * (1 - t) + S * t) V) :
    fval U S V (liftPt s t (U * (1 - t) + S * t) V) = 0 ∧
    ∃ K > 0, -(U * aF U (cOf s * V) r0 v) * liftPt s t (U * (1 - t) + S * t) V 0 -
        S * aF S (cOf s * V) r1 v * liftPt s t (U * (1 - t) + S * t) V 1 +
        V * v * liftPt s t (U * (1 - t) + S * t) V 3 = -K * (r0 * (1 - t) + r1 * t) := by
  have hc0 : 0 ≤ cOf s := by unfold cOf; apply div_nonneg hs0; linarith
  have hk : 0 < 1 + cOf s * V := by have := mul_nonneg hc0 hV; linarith
  refine ⟨lift_on U S V s t hs hk.ne' (by linarith), ?_⟩
  refine ⟨(1 - s) * (1 + cOf s * V) / (1 + hLift s (U * (1 - t) + S * t) V), ?_, ?_⟩
  · apply div_pos (mul_pos (by linarith) hk) (by linarith)
  · have := relift_dval U S V s t r0 r1 v hs hk hU.ne' hS.ne' (by linarith)
    unfold aF
    rw [this]

private def gU (m ns j τ : ℕ) : ℝ := if τ < 2 then UA m ns j else UB m ns j
private def gS (m ns j τ : ℕ) : ℝ := if τ < 2 then SA m ns j else SB m ns j

private def stU (m ns i : ℕ) : ℝ := gU m ns ((i - 1) / 4) ((i - 1) % 4)
private def stS (m ns i : ℕ) : ℝ := gS m ns ((i - 1) / 4) ((i - 1) % 4)
private def stV (m ns i : ℕ) : ℝ := ptV m ns ((i - 1) / 4) ((i - 1) % 4)
private def stK (m ns : ℕ) (ds : ℝ) (i : ℕ) : ℝ := cOf (sig ns ds ((i - 1) / 4)) * stV m ns i

private def r0of (τ : ℕ) : ℝ := if τ = 0 then -1 else if τ = 2 then 1 else -2
private def r1of (τ : ℕ) : ℝ := if τ = 0 then 1 else if τ = 2 then -1 else -2
private def rt0 (i : ℕ) : ℝ := if i = 0 then 1 else r0of ((i - 1) % 4)
private def rt1 (i : ℕ) : ℝ := if i = 0 then 1 else r1of ((i - 1) % 4)

private def vv (m ns : ℕ) (ds : ℝ) : ℕ → ℝ
  | 0 => 2
  | i + 1 =>
    if i % 4 = 2 then
      vsolve (stU m ns (i + 1)) (stK m ns ds (i + 1)) (rt0 (i + 1))
        (aF (stU m ns i) (stK m ns ds i) (rt0 i) (vv m ns ds i) - vv m ns ds i)
    else if i % 4 = 0 ∧ i ≠ 0 then
      vsolve (stS m ns (i + 1)) (stK m ns ds (i + 1)) (rt1 (i + 1))
        (aF (stS m ns i) (stK m ns ds i) (rt1 i) (vv m ns ds i) - vv m ns ds i)
    else vv m ns ds i

private def aS (m ns : ℕ) (ds : ℝ) (i : ℕ) : ℝ :=
  aF (stU m ns i) (stK m ns ds i) (rt0 i) (vv m ns ds i)
private def bS (m ns : ℕ) (ds : ℝ) (i : ℕ) : ℝ :=
  aF (stS m ns i) (stK m ns ds i) (rt1 i) (vv m ns ds i)

/-! ### The modified last state: the homothety `X = μ T_A(J-1)` at position `4J-1` -/

private def fUx (m ns : ℕ) (μ : ℝ) (i : ℕ) : ℝ :=
  if i = 4 * Jn m ns - 1 then μ * UA m ns (Jn m ns - 1) else stU m ns i
private def fSx (m ns : ℕ) (μ : ℝ) (i : ℕ) : ℝ :=
  if i = 4 * Jn m ns - 1 then μ * SA m ns (Jn m ns - 1) else stS m ns i
private def fVx (m ns : ℕ) (μ : ℝ) (i : ℕ) : ℝ :=
  if i = 4 * Jn m ns - 1 then μ * VA m ns (Jn m ns - 1) else stV m ns i
private def fAx (m ns : ℕ) (ds cc : ℝ) (i : ℕ) : ℝ :=
  if i = 4 * Jn m ns - 1 then
    cc + (aS m ns ds (4 * Jn m ns - 2) - vv m ns ds (4 * Jn m ns - 2))
  else aS m ns ds i
private def fBx (m ns : ℕ) (ds cc : ℝ) (i : ℕ) : ℝ :=
  if i = 4 * Jn m ns - 1 then
    cc + (bS m ns ds (4 * Jn m ns - 2) - vv m ns ds (4 * Jn m ns - 2))
  else bS m ns ds i
private def fCx (m ns : ℕ) (ds cc : ℝ) (i : ℕ) : ℝ :=
  if i = 4 * Jn m ns - 1 then cc else vv m ns ds i

private lemma fUx_ne {m ns : ℕ} {μ : ℝ} {i : ℕ} (h : i ≠ 4 * Jn m ns - 1) :
    fUx m ns μ i = stU m ns i := if_neg h
private lemma fSx_ne {m ns : ℕ} {μ : ℝ} {i : ℕ} (h : i ≠ 4 * Jn m ns - 1) :
    fSx m ns μ i = stS m ns i := if_neg h
private lemma fVx_ne {m ns : ℕ} {μ : ℝ} {i : ℕ} (h : i ≠ 4 * Jn m ns - 1) :
    fVx m ns μ i = stV m ns i := if_neg h
private lemma fAx_ne {m ns : ℕ} {ds cc : ℝ} {i : ℕ} (h : i ≠ 4 * Jn m ns - 1) :
    fAx m ns ds cc i = aS m ns ds i := if_neg h
private lemma fBx_ne {m ns : ℕ} {ds cc : ℝ} {i : ℕ} (h : i ≠ 4 * Jn m ns - 1) :
    fBx m ns ds cc i = bS m ns ds i := if_neg h
private lemma fCx_ne {m ns : ℕ} {ds cc : ℝ} {i : ℕ} (h : i ≠ 4 * Jn m ns - 1) :
    fCx m ns ds cc i = vv m ns ds i := if_neg h

private lemma fUx_eq {m ns : ℕ} {μ : ℝ} {i : ℕ} (h : i = 4 * Jn m ns - 1) :
    fUx m ns μ i = μ * UA m ns (Jn m ns - 1) := if_pos h
private lemma fSx_eq {m ns : ℕ} {μ : ℝ} {i : ℕ} (h : i = 4 * Jn m ns - 1) :
    fSx m ns μ i = μ * SA m ns (Jn m ns - 1) := if_pos h
private lemma fVx_eq {m ns : ℕ} {μ : ℝ} {i : ℕ} (h : i = 4 * Jn m ns - 1) :
    fVx m ns μ i = μ * VA m ns (Jn m ns - 1) := if_pos h
private lemma fAx_eq {m ns : ℕ} {ds cc : ℝ} {i : ℕ} (h : i = 4 * Jn m ns - 1) :
    fAx m ns ds cc i =
      cc + (aS m ns ds (4 * Jn m ns - 2) - vv m ns ds (4 * Jn m ns - 2)) := if_pos h
private lemma fBx_eq {m ns : ℕ} {ds cc : ℝ} {i : ℕ} (h : i = 4 * Jn m ns - 1) :
    fBx m ns ds cc i =
      cc + (bS m ns ds (4 * Jn m ns - 2) - vv m ns ds (4 * Jn m ns - 2)) := if_pos h
private lemma fCx_eq {m ns : ℕ} {ds cc : ℝ} {i : ℕ} (h : i = 4 * Jn m ns - 1) :
    fCx m ns ds cc i = cc := if_pos h

private lemma st_val (m ns : ℕ) (ds : ℝ) (i j τ : ℕ) (h1 : (i - 1) / 4 = j)
    (h2 : (i - 1) % 4 = τ) :
    stU m ns i = gU m ns j τ ∧ stS m ns i = gS m ns j τ ∧ stV m ns i = ptV m ns j τ ∧
    stK m ns ds i = cOf (sig ns ds j) * ptV m ns j τ := by
  unfold stK stV stU stS; rw [h1, h2]; exact ⟨rfl, rfl, rfl, rfl⟩

private lemma rt_val (i τ : ℕ) (hi : 1 ≤ i) (h2 : (i - 1) % 4 = τ) :
    rt0 i = r0of τ ∧ rt1 i = r1of τ := by
  unfold rt0 rt1; rw [if_neg (by omega), if_neg (by omega), h2]; exact ⟨rfl, rfl⟩

/-- Entries before the deleted position are unchanged. -/
private lemma pt_val {m ns k : ℕ} (hk : 4 * Jn m ns - 1 ≤ k) (ds : ℝ) (i j τ : ℕ)
    (hi1 : 1 ≤ i) (hi : i ≤ 4 * Jn m ns - 2)
    (h1 : (i - 1) / 4 = j) (h2 : (i - 1) % 4 = τ) :
    Tpt m ns ds (skipIdx k i) = gpt m ns ds j τ := by
  have hs : skipIdx k i = i := by unfold skipIdx; rw [if_pos (by omega)]
  rw [hs]; unfold Tpt
  rw [if_neg (by omega : i ≠ 0), if_neg (by omega : i ≠ 4 * Jn m ns + 1), h1, h2]

private lemma ptT_bounds (m ns j : ℕ) (hm : 2 ≤ m) (hns : 1 ≤ ns) :
    ptT m ns j 0 ≤ 3 / 10 ∧ ptT m ns j 3 ≤ 3 / 10 ∧ 31 / 50 ≤ ptT m ns j 1 ∧
      31 / 50 ≤ ptT m ns j 2 := by
  obtain ⟨hd0, hd5, hu0, hu1⟩ := (class_trans m ns j hm hns).1
  simp only [ptT, if_true, show (1:ℕ) ≠ 0 by decide, show (2:ℕ) ≠ 0 by decide,
    show (3:ℕ) ≠ 0 by decide, show (2:ℕ) ≠ 1 by decide, show (3:ℕ) ≠ 1 by decide,
    show (3:ℕ) ≠ 2 by decide, if_false]
  unfold fa' fa fb' fb
  refine ⟨by linarith, by linarith, by linarith, by linarith⟩

private lemma ns_pos {m ns : ℕ} {ds : ℝ} (hA : Adm m ns ds) : 1 ≤ ns := by
  rcases Nat.eq_zero_or_pos ns with h | h
  · have := hA.2.1; subst h; simp at this
  · exact h

private lemma g_pos {m ns : ℕ} {ds : ℝ} (hA : Adm m ns ds) (j τ : ℕ) (hj : j < Jn m ns) :
    0 < gS m ns j τ ∧ gS m ns j τ < gU m ns j τ ∧ 1 < ptV m ns j τ ∧
      0 ≤ cOf (sig ns ds j) * ptV m ns j τ ∧
      cOf (sig ns ds j) * ptV m ns j τ < gS m ns j τ := by
  obtain ⟨hg0, hg1, -, -, -, -⟩ := J_spec hA
  obtain ⟨hSB1, hSBA, hSAU, hSBU, -⟩ := (gadget_lines hA).1 j hj
  obtain ⟨hs0, hs1, hcA, hcB, hVA, hVB, -⟩ := cw_bound hA j hj
  have hc0 : 0 ≤ cOf (sig ns ds j) := by unfold cOf; apply div_nonneg hs0; linarith
  have hSB : 0 < SB m ns j := by linarith
  have hSA : 0 < SA m ns j := by linarith
  unfold gS gU ptV
  split_ifs
  · refine ⟨hSA, hSAU, hVA, by positivity, ?_⟩
    have : cOf (sig ns ds j) * VA m ns j = cOf (sig ns ds j) * wA m ns j * SA m ns j := by
      unfold VA; ring
    rw [this]; nlinarith
  · refine ⟨hSB, hSBU, hVB, by positivity, ?_⟩
    have : cOf (sig ns ds j) * VB m ns j = cOf (sig ns ds j) * wB m ns j * SB m ns j := by
      unfold VB; ring
    rw [this]; nlinarith

private lemma on_pt {m ns : ℕ} {ds : ℝ} (hA : Adm m ns ds) (j τ : ℕ) (hj : j < Jn m ns)
    (hτ : τ < 4) (r0 r1 v : ℝ) :
    fval (gU m ns j τ) (gS m ns j τ) (ptV m ns j τ) (gpt m ns ds j τ) = 0 ∧
    ∃ K > 0, -(gU m ns j τ * aF (gU m ns j τ) (cOf (sig ns ds j) * ptV m ns j τ) r0 v) *
        gpt m ns ds j τ 0 -
      gS m ns j τ * aF (gS m ns j τ) (cOf (sig ns ds j) * ptV m ns j τ) r1 v *
        gpt m ns ds j τ 1 +
      ptV m ns j τ * v * gpt m ns ds j τ 3 =
      -K * (r0 * (1 - ptT m ns j τ) + r1 * ptT m ns j τ) := by
  obtain ⟨hS, hSU, hV, -, -⟩ := g_pos hA j τ hj
  obtain ⟨hs0, hs1, -, -, -, -, hH⟩ := cw_bound hA j hj
  have hN := normalization m ns j hA.1
  have hL : ptL m ns j τ = gU m ns j τ * (1 - ptT m ns j τ) + gS m ns j τ * ptT m ns j τ := by
    unfold gU gS
    split_ifs with h
    · exact hN.2.2.1 τ h
    · exact hN.2.2.2 τ (by omega) hτ
  have hH' := hH τ hτ
  rw [hL] at hH'
  have e : gpt m ns ds j τ = liftPt (sig ns ds j) (ptT m ns j τ)
      (gU m ns j τ * (1 - ptT m ns j τ) + gS m ns j τ * ptT m ns j τ) (ptV m ns j τ) := by
    unfold gpt; rw [hL]
  rw [e]
  exact on_gen _ _ _ _ _ r0 r1 v hs0 (by linarith) (by linarith) (by linarith) hS hH'

private lemma sgn_pos {K X D : ℝ} (hK : 0 < K) (hD : D = -K * X) (hX : X < 0) : 0 < D := by
  rw [hD]; nlinarith
private lemma sgn_neg {K X D : ℝ} (hK : 0 < K) (hD : D = -K * X) (hX : 0 < X) : D < 0 := by
  rw [hD]; nlinarith

private lemma on_A {m ns : ℕ} {ds : ℝ} (hA : Adm m ns ds) (j τ : ℕ) (hj : j < Jn m ns)
    (hτ : τ < 2) (r0 r1 v : ℝ) :
    fval (UA m ns j) (SA m ns j) (VA m ns j) (gpt m ns ds j τ) = 0 ∧
    ∃ K > 0, -(UA m ns j * aF (UA m ns j) (cOf (sig ns ds j) * VA m ns j) r0 v) *
        gpt m ns ds j τ 0 -
      SA m ns j * aF (SA m ns j) (cOf (sig ns ds j) * VA m ns j) r1 v * gpt m ns ds j τ 1 +
      VA m ns j * v * gpt m ns ds j τ 3 =
      -K * (r0 * (1 - ptT m ns j τ) + r1 * ptT m ns j τ) := by
  have h := on_pt hA j τ hj (by omega) r0 r1 v
  simp only [gU, gS, ptV, if_pos hτ] at h
  exact h

private lemma on_B {m ns : ℕ} {ds : ℝ} (hA : Adm m ns ds) (j τ : ℕ) (hj : j < Jn m ns)
    (hτ : ¬ τ < 2) (hτ4 : τ < 4) (r0 r1 v : ℝ) :
    fval (UB m ns j) (SB m ns j) (VB m ns j) (gpt m ns ds j τ) = 0 ∧
    ∃ K > 0, -(UB m ns j * aF (UB m ns j) (cOf (sig ns ds j) * VB m ns j) r0 v) *
        gpt m ns ds j τ 0 -
      SB m ns j * aF (SB m ns j) (cOf (sig ns ds j) * VB m ns j) r1 v * gpt m ns ds j τ 1 +
      VB m ns j * v * gpt m ns ds j τ 3 =
      -K * (r0 * (1 - ptT m ns j τ) + r1 * ptT m ns j τ) := by
  have h := on_pt hA j τ hj hτ4 r0 r1 v
  simp only [gU, gS, ptV, if_neg hτ] at h
  exact h

private lemma stA (m ns : ℕ) (ds : ℝ) (i j : ℕ) (h1 : (i - 1) / 4 = j) (h2 : (i - 1) % 4 < 2) :
    stU m ns i = UA m ns j ∧ stS m ns i = SA m ns j ∧ stV m ns i = VA m ns j ∧
    stK m ns ds i = cOf (sig ns ds j) * VA m ns j := by
  obtain ⟨a, b, c, d⟩ := st_val m ns ds i j _ h1 rfl
  simp only [gU, gS, ptV, if_pos h2] at a b c d
  exact ⟨a, b, c, d⟩

private lemma stB (m ns : ℕ) (ds : ℝ) (i j : ℕ) (h1 : (i - 1) / 4 = j)
    (h2 : ¬ (i - 1) % 4 < 2) :
    stU m ns i = UB m ns j ∧ stS m ns i = SB m ns j ∧ stV m ns i = VB m ns j ∧
    stK m ns ds i = cOf (sig ns ds j) * VB m ns j := by
  obtain ⟨a, b, c, d⟩ := st_val m ns ds i j _ h1 rfl
  simp only [gU, gS, ptV, if_neg h2] at a b c d
  exact ⟨a, b, c, d⟩

private lemma nest_same {U S V κ v r0 r0' r1 r1' : ℝ} (hU : 0 < U) (hS : 0 < S) (hκ : 0 ≤ κ)
    (h0 : r0' ≤ r0) (h1 : r1' ≤ r1) :
    (U < U ∨ (U = U ∧ aF U κ r0' v ≤ aF U κ r0 v)) ∧
    (S < S ∨ (S = S ∧ aF S κ r1' v ≤ aF S κ r1 v)) ∧
    (U * V < V * U ∨ (U * V = V * U ∧ aF U κ r0' v - aF U κ r0 v ≤ v - v)) ∧
    (S * V < V * S ∨ (S * V = V * S ∧ aF S κ r1' v - aF S κ r1 v ≤ v - v)) := by
  have ha := aF_mono v hU hκ h0
  have hb := aF_mono v hS hκ h1
  exact ⟨Or.inr ⟨rfl, ha⟩, Or.inr ⟨rfl, hb⟩, Or.inr ⟨by ring, by linarith⟩,
    Or.inr ⟨by ring, by linarith⟩⟩

private lemma idx_cases (i : ℕ) : i = 0 ∨ (∃ j, i = 4 * j + 1) ∨ (∃ j, i = 4 * j + 2) ∨
    (∃ j, i = 4 * j + 3) ∨ (∃ j, i = 4 * j + 4) := by
  rcases Nat.eq_zero_or_pos i with h | h
  · exact Or.inl h
  · have h4 : (i - 1) % 4 = 0 ∨ (i - 1) % 4 = 1 ∨ (i - 1) % 4 = 2 ∨ (i - 1) % 4 = 3 := by
      omega
    rcases h4 with h4 | h4 | h4 | h4
    · exact Or.inr (Or.inl ⟨(i - 1) / 4, by omega⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨(i - 1) / 4, by omega⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨(i - 1) / 4, by omega⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨(i - 1) / 4, by omega⟩)))

/-- Homothety identity: `fval (μU) (μS) (μV) p = μ (fval U S V p - p₂) + p₂`. -/
private lemma fval_hom (μ U S V : ℝ) (p : Lot 4) :
    fval (μ * U) (μ * S) (μ * V) p = μ * (fval U S V p - p 2) + p 2 := by
  unfold fval; ring

end

/-- Deleting `yb_{J-1}` (position `4J-1`) or `xb_{J-1}` (position `4J`) leaves a ranking with
a chain (the last vector is the homothety `X` of `T_A(J-1)`). -/
theorem del_last {m ns : ℕ} {ds : ℝ} (hA : Adm m ns ds) (k : ℕ)
    (hk : k = 4 * Jn m ns - 1 ∨ k = 4 * Jn m ns) :
    ∃ W, IsChainFn (4 * Jn m ns + 1) (fun i => Tpt m ns ds (skipIdx k i)) W := by
  have hm := hA.1
  have hns := ns_pos hA
  obtain ⟨hg0, hg1, hJ2, -, -, -⟩ := J_spec hA
  have hGL := gadget_lines hA
  have hTN := tight_nest hA
  have hk' : 4 * Jn m ns - 1 ≤ k := by omega
  have hp0 : Tpt m ns ds (skipIdx k 0) = Rlot o0 := by
    have : skipIdx k 0 = 0 := by unfold skipIdx; rw [if_pos (by omega)]
    rw [this]; unfold Tpt; simp
  -- the surviving last point `p = gpt (J-1) τ`
  obtain ⟨τ, hτ2, hτ4, hq⟩ : ∃ τ, 2 ≤ τ ∧ τ < 4 ∧
      Tpt m ns ds (skipIdx k (4 * Jn m ns - 1)) = gpt m ns ds (Jn m ns - 1) τ := by
    rcases hk with rfl | rfl
    · refine ⟨3, by norm_num, by norm_num, ?_⟩
      have : skipIdx (4 * Jn m ns - 1) (4 * Jn m ns - 1) = 4 * Jn m ns := by
        unfold skipIdx; rw [if_neg (by omega)]; omega
      rw [this]; unfold Tpt
      rw [if_neg (by omega), if_neg (by omega)]
      congr 1 <;> omega
    · refine ⟨2, by norm_num, by norm_num, ?_⟩
      have : skipIdx (4 * Jn m ns) (4 * Jn m ns - 1) = 4 * Jn m ns - 1 := by
        unfold skipIdx; rw [if_pos (by omega)]
      rw [this]; unfold Tpt
      rw [if_neg (by omega), if_neg (by omega)]
      congr 1 <;> omega
  have hq1 : Tpt m ns ds (skipIdx k (4 * Jn m ns)) = Rlot (o1 m ns) := by
    have : skipIdx k (4 * Jn m ns) = 4 * Jn m ns + 1 := by
      unfold skipIdx; rw [if_neg (by omega)]
    rw [this]; unfold Tpt; rw [if_neg (by omega), if_pos rfl]
  have hjJ : Jn m ns - 1 < Jn m ns := by omega
  have hfp : fval (UA m ns (Jn m ns - 1)) (SA m ns (Jn m ns - 1)) (VA m ns (Jn m ns - 1))
      (gpt m ns ds (Jn m ns - 1) τ) < 0 := by
    interval_cases τ
    · exact (lifted_rel_gadget hA _ hjJ).1
    · exact (lifted_rel_gadget hA _ hjJ).2.1
  obtain ⟨hwo, hX⟩ := hom_X hA
  obtain ⟨hp2, hμ0, hμ1, hμV⟩ := hX τ hτ2 hτ4
  set p := gpt m ns ds (Jn m ns - 1) τ with hpdef
  obtain ⟨μ, hμ⟩ : ∃ μ, μ = p 2 / (p 2 -
      fval (UA m ns (Jn m ns - 1)) (SA m ns (Jn m ns - 1)) (VA m ns (Jn m ns - 1)) p) :=
    ⟨_, rfl⟩
  rw [← hμ] at hμ0 hμ1 hμV
  have hval : fval (μ * UA m ns (Jn m ns - 1)) (μ * SA m ns (Jn m ns - 1))
      (μ * VA m ns (Jn m ns - 1)) p = 0 := by
    rw [fval_hom, hμ]
    have hne : p 2 - fval (UA m ns (Jn m ns - 1)) (SA m ns (Jn m ns - 1))
        (VA m ns (Jn m ns - 1)) p ≠ 0 := by linarith
    field_simp
    ring
  obtain ⟨cc, hcc⟩ : ∃ cc : ℝ, cc = -(μ * UA m ns (Jn m ns - 1) *
      (aS m ns ds (4 * Jn m ns - 2) - vv m ns ds (4 * Jn m ns - 2)) * p 0 +
      μ * SA m ns (Jn m ns - 1) *
      (bS m ns ds (4 * Jn m ns - 2) - vv m ns ds (4 * Jn m ns - 2)) * p 1 + 1) / p 2 :=
    ⟨_, rfl⟩
  have hSAU := g_pos hA (Jn m ns - 1) 0 hjJ
  simp only [gS, gU, ptV, if_pos (show (0:ℕ) < 2 by norm_num)] at hSAU
  obtain ⟨hSA0, hSAUA, hVA1, -, -⟩ := hSAU
  apply strictify (4 * Jn m ns + 1) _ (fUx m ns μ) (fSx m ns μ) (fVx m ns μ)
    (fAx m ns ds cc) (fBx m ns ds cc) (fCx m ns ds cc)
  · -- coordinates
    intro i hi
    by_cases h : i = 4 * Jn m ns - 1
    · rw [fUx_eq h, fSx_eq h, fVx_eq h]
      exact ⟨mul_pos hμ0 hSA0, mul_lt_mul_of_pos_left hSAUA hμ0, hμV⟩
    rw [fUx_ne h, fSx_ne h, fVx_ne h]
    obtain ⟨u1, s1, v1, -⟩ := st_val m ns ds i ((i - 1) / 4) ((i - 1) % 4) rfl rfl
    obtain ⟨h1, h2, h3, -⟩ := g_pos hA ((i - 1) / 4) ((i - 1) % 4) (by omega)
    rw [u1, s1, v1]; exact ⟨h1, h2, h3⟩
  · -- nesting
    intro i hi
    by_cases hlast : i = 4 * Jn m ns - 2
    · subst hlast
      have h1 : 4 * Jn m ns - 2 ≠ 4 * Jn m ns - 1 := by omega
      have h2 : 4 * Jn m ns - 2 + 1 = 4 * Jn m ns - 1 := by omega
      rw [fUx_ne h1, fSx_ne h1, fVx_ne h1, fAx_ne h1, fBx_ne h1, fCx_ne h1,
        fUx_eq h2, fSx_eq h2, fVx_eq h2, fAx_eq h2, fBx_eq h2, fCx_eq h2]
      obtain ⟨u0, s0, v0, -⟩ := stA m ns ds (4 * Jn m ns - 2) (Jn m ns - 1) (by omega)
        (by omega)
      rw [u0, s0, v0]
      have hUA0 : 0 < UA m ns (Jn m ns - 1) := by linarith
      refine ⟨Or.inl (mul_lt_of_lt_one_left hUA0 hμ1),
        Or.inl (mul_lt_of_lt_one_left hSA0 hμ1), Or.inr ⟨by ring, by linarith⟩,
        Or.inr ⟨by ring, by linarith⟩⟩
    have h1 : i ≠ 4 * Jn m ns - 1 := by omega
    have h2 : i + 1 ≠ 4 * Jn m ns - 1 := by omega
    rw [fUx_ne h1, fSx_ne h1, fVx_ne h1, fAx_ne h1, fBx_ne h1, fCx_ne h1,
      fUx_ne h2, fSx_ne h2, fVx_ne h2, fAx_ne h2, fBx_ne h2, fCx_ne h2]
    rcases idx_cases i with rfl | ⟨j, rfl⟩ | ⟨j, rfl⟩ | ⟨j, rfl⟩ | ⟨j, rfl⟩
    · -- front → after xa_0: same line A_0, (1,1) → (−1,1)
      have hJ0 : 0 < Jn m ns := by omega
      obtain ⟨u0, s0, v0, k0⟩ := stA m ns ds 0 0 (by norm_num) (by norm_num)
      obtain ⟨u1, s1, v1, k1⟩ := stA m ns ds (0 + 1) 0 (by norm_num) (by norm_num)
      obtain ⟨r0e, r1e⟩ := rt_val (0 + 1) 0 (by norm_num) (by norm_num)
      have hr0 : rt0 0 = 1 := by simp [rt0]
      have hr1 : rt1 0 = 1 := by simp [rt1]
      have hv : vv m ns ds (0 + 1) = vv m ns ds 0 := by simp [vv]
      obtain ⟨hS, hSU, -, hk, -⟩ := g_pos hA 0 0 hJ0
      simp only [gS, gU, ptV, if_pos (show (0:ℕ) < 2 by norm_num)] at hS hSU hk
      simp only [aS, bS]
      rw [u0, s0, v0, k0, u1, s1, v1, k1, hv, r0e, r1e, hr0, hr1]
      exact nest_same (by linarith) hS hk (by norm_num [r0of]) (by norm_num [r1of])
    · have hj : j < Jn m ns := by omega
      obtain ⟨u0, s0, v0, k0⟩ := stA m ns ds (4 * j + 1) j (by omega) (by omega)
      obtain ⟨u1, s1, v1, k1⟩ := stA m ns ds (4 * j + 1 + 1) j (by omega) (by omega)
      obtain ⟨r0e, r1e⟩ := rt_val (4 * j + 1) 0 (by omega) (by omega)
      obtain ⟨r0e', r1e'⟩ := rt_val (4 * j + 1 + 1) 1 (by omega) (by omega)
      have hv : vv m ns ds (4 * j + 1 + 1) = vv m ns ds (4 * j + 1) := by
        rw [vv, if_neg (by omega), if_neg (by omega)]
      obtain ⟨hS, hSU, -, hk, -⟩ := g_pos hA j 0 hj
      simp only [gS, gU, ptV, if_pos (show (0:ℕ) < 2 by norm_num)] at hS hSU hk
      simp only [aS, bS]
      rw [u0, s0, v0, k0, u1, s1, v1, k1, hv, r0e, r1e, r0e', r1e']
      exact nest_same (by linarith) hS hk (by simp [r0of]) (by simp [r1of]; norm_num)
    · have hj : j < Jn m ns := by omega
      obtain ⟨hkB0, hkBS⟩ := (g_pos hA j 2 hj).2.2.2
      obtain ⟨hSB0, hSBU, -⟩ := g_pos hA j 2 hj
      simp only [gS, gU, ptV, if_neg (show ¬ (2:ℕ) < 2 by norm_num)] at hkB0 hkBS hSB0 hSBU
      obtain ⟨u0, s0, v0, k0⟩ := stA m ns ds (4 * j + 2) j (by omega) (by omega)
      obtain ⟨u1, s1, v1, k1⟩ := stB m ns ds (4 * j + 2 + 1) j (by omega) (by omega)
      have hv : vv m ns ds (4 * j + 2 + 1) = vsolve (stU m ns (4 * j + 2 + 1))
          (stK m ns ds (4 * j + 2 + 1)) (rt0 (4 * j + 2 + 1))
          (aS m ns ds (4 * j + 2) - vv m ns ds (4 * j + 2)) := by
        rw [vv, if_pos (by omega)]; rfl
      have key : aS m ns ds (4 * j + 2 + 1) - vv m ns ds (4 * j + 2 + 1) =
          aS m ns ds (4 * j + 2) - vv m ns ds (4 * j + 2) := by
        unfold aS at hv ⊢; rw [hv]
        rw [u1, k1]
        exact aF_vsolve _ _ (by linarith) hkB0 (by linarith)
      obtain ⟨hSB1, hSBA, hSAU, -, hUBA⟩ := hGL.1 j hj
      obtain ⟨eUV, hSUc⟩ := hTN.1 j hj
      have hVA : 1 < VA m ns j := (cw_bound hA j hj).2.2.2.2.1
      rw [u0, s0, v0, u1, s1, v1]
      refine ⟨Or.inl hUBA, Or.inl hSBA, Or.inr ⟨by linear_combination -eUV, by linarith⟩,
        Or.inl ?_⟩
      have hUA : 0 < UA m ns j := by linarith
      refine lt_of_mul_lt_mul_right ?_ hUA.le
      have h1 : SB m ns j * UA m ns j * VA m ns j < UB m ns j * SA m ns j * VA m ns j :=
        mul_lt_mul_of_pos_right hSUc (by linarith)
      linear_combination h1 - SA m ns j * eUV
    · have hj : j < Jn m ns := by omega
      obtain ⟨u0, s0, v0, k0⟩ := stB m ns ds (4 * j + 3) j (by omega) (by omega)
      obtain ⟨u1, s1, v1, k1⟩ := stB m ns ds (4 * j + 3 + 1) j (by omega) (by omega)
      obtain ⟨r0e, r1e⟩ := rt_val (4 * j + 3) 2 (by omega) (by omega)
      obtain ⟨r0e', r1e'⟩ := rt_val (4 * j + 3 + 1) 3 (by omega) (by omega)
      have hv : vv m ns ds (4 * j + 3 + 1) = vv m ns ds (4 * j + 3) := by
        rw [vv, if_neg (by omega), if_neg (by omega)]
      obtain ⟨hS, hSU, -, hk, -⟩ := g_pos hA j 2 hj
      simp only [gS, gU, ptV, if_neg (show ¬ (2:ℕ) < 2 by norm_num)] at hS hSU hk
      simp only [aS, bS]
      rw [u0, s0, v0, k0, u1, s1, v1, k1, hv, r0e, r1e, r0e', r1e']
      exact nest_same (by linarith) hS hk (by norm_num [r0of]) (by norm_num [r1of])
    · have hj : j + 1 < Jn m ns := by omega
      have hj' : j < Jn m ns := by omega
      obtain ⟨hkA0, hkAS⟩ := (g_pos hA (j + 1) 0 hj).2.2.2
      obtain ⟨hSA0', -⟩ := g_pos hA (j + 1) 0 hj
      simp only [gS, gU, ptV, if_pos (show (0:ℕ) < 2 by norm_num)] at hkA0 hkAS hSA0'
      obtain ⟨u0, s0, v0, k0⟩ := stB m ns ds (4 * j + 4) j (by omega) (by omega)
      obtain ⟨u1, s1, v1, k1⟩ := stA m ns ds (4 * j + 4 + 1) (j + 1) (by omega) (by omega)
      have hv : vv m ns ds (4 * j + 4 + 1) = vsolve (stS m ns (4 * j + 4 + 1))
          (stK m ns ds (4 * j + 4 + 1)) (rt1 (4 * j + 4 + 1))
          (bS m ns ds (4 * j + 4) - vv m ns ds (4 * j + 4)) := by
        rw [vv, if_neg (by omega), if_pos ⟨by omega, by omega⟩]; rfl
      have key : bS m ns ds (4 * j + 4 + 1) - vv m ns ds (4 * j + 4 + 1) =
          bS m ns ds (4 * j + 4) - vv m ns ds (4 * j + 4) := by
        unfold bS at hv ⊢; rw [hv]
        rw [s1, k1]
        exact aF_vsolve _ _ hSA0' hkA0 hkAS
      obtain ⟨hU', hS'⟩ := hGL.2 j hj
      obtain ⟨eSV, hUSc, -⟩ := hTN.2 j hj
      have hSB1 := (hGL.1 j hj').1
      have hVB : 1 < VB m ns j := (cw_bound hA j hj').2.2.2.2.2.1
      rw [u0, s0, v0, u1, s1, v1]
      refine ⟨Or.inl hU', Or.inl hS', Or.inl ?_, Or.inr ⟨by linear_combination -eSV,
        by linarith⟩⟩
      have hSB : 0 < SB m ns j := by linarith
      refine lt_of_mul_lt_mul_right ?_ hSB.le
      have h1 : UA m ns (j + 1) * SB m ns j * VB m ns j <
          UB m ns j * SA m ns (j + 1) * VB m ns j :=
        mul_lt_mul_of_pos_right hUSc (by linarith)
      linear_combination h1 - UB m ns j * eSV
  · -- relations
    intro i hi
    by_cases hX4 : i = 4 * Jn m ns - 1
    · -- the homothety X: p on (derivative 1), R(o1) strictly below
      rw [fUx_eq hX4, fSx_eq hX4, fVx_eq hX4, fAx_eq hX4, fBx_eq hX4, fCx_eq hX4]
      have hpi : Tpt m ns ds (skipIdx k i) = p := by rw [hX4]; exact hq
      have hpi1 : Tpt m ns ds (skipIdx k (i + 1)) = Rlot (o1 m ns) := by
        rw [show i + 1 = 4 * Jn m ns by omega]; exact hq1
      rw [hpi, hpi1]
      refine ⟨Or.inr ⟨hval, ?_⟩, Or.inl ?_⟩
      · have hcc' : cc * p 2 = -(μ * UA m ns (Jn m ns - 1) *
            (aS m ns ds (4 * Jn m ns - 2) - vv m ns ds (4 * Jn m ns - 2)) * p 0 +
            μ * SA m ns (Jn m ns - 1) *
            (bS m ns ds (4 * Jn m ns - 2) - vv m ns ds (4 * Jn m ns - 2)) * p 1 + 1) := by
          rw [hcc]; field_simp
        have hcv : cc * fval (μ * UA m ns (Jn m ns - 1)) (μ * SA m ns (Jn m ns - 1))
            (μ * VA m ns (Jn m ns - 1)) p = 0 := by rw [hval]; ring
        unfold fval at hcv
        nlinarith [hcv, hcc']
      · have hVAe : VA m ns (Jn m ns - 1) = wA m ns (Jn m ns - 1) * SA m ns (Jn m ns - 1) :=
          rfl
        have hw0 : 0 < wA m ns (Jn m ns - 1) := by
          by_contra hw
          push_neg at hw
          have : wA m ns (Jn m ns - 1) * SA m ns (Jn m ns - 1) ≤ 0 :=
            mul_nonpos_of_nonpos_of_nonneg hw hSA0.le
          linarith
        have ho1 : 0 < o1 m ns := by linarith
        have e : fval (μ * UA m ns (Jn m ns - 1)) (μ * SA m ns (Jn m ns - 1))
            (μ * VA m ns (Jn m ns - 1)) (Rlot (o1 m ns)) =
            μ * SA m ns (Jn m ns - 1) * (wA m ns (Jn m ns - 1) - o1 m ns) / (1 + o1 m ns) := by
          simp only [fval, Rlot, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
            Matrix.head_cons]
          rw [hVAe]
          field_simp
          ring
        rw [e]
        apply div_neg_of_neg_of_pos _ (by linarith)
        exact mul_neg_of_pos_of_neg (mul_pos hμ0 hSA0) (by linarith)
    rw [fUx_ne hX4, fSx_ne hX4, fVx_ne hX4, fAx_ne hX4, fBx_ne hX4, fCx_ne hX4]
    simp only [aS, bS]
    by_cases hY : i = 4 * Jn m ns - 2
    · -- A_{J-1}, rotation low, ya_{J-1} on, p strictly below (G2a/G2b)
      obtain ⟨u0, s0, v0, k0⟩ := stA m ns ds i (Jn m ns - 1) (by omega) (by omega)
      obtain ⟨r0e, r1e⟩ := rt_val i 1 (by omega) (by omega)
      have hp := pt_val hk' ds i (Jn m ns - 1) 1 (by omega) (by omega) (by omega) (by omega)
      have hp' : Tpt m ns ds (skipIdx k (i + 1)) = p := by
        rw [show i + 1 = 4 * Jn m ns - 1 by omega]; exact hq
      rw [u0, s0, v0, k0, hp, hp']
      obtain ⟨h0, K, hK, hD⟩ := on_A hA (Jn m ns - 1) 1 hjJ (by norm_num) (rt0 i)
        (rt1 i) (vv m ns ds i)
      have e0 : rt0 i = -2 := by rw [r0e]; simp [r0of]
      have e1 : rt1 i = -2 := by rw [r1e]; simp [r1of]
      refine ⟨Or.inr ⟨h0, sgn_pos hK hD ?_⟩, Or.inl hfp⟩
      rw [e0, e1]; linarith
    rcases idx_cases i with rfl | ⟨j, rfl⟩ | ⟨j, rfl⟩ | ⟨j, rfl⟩ | ⟨j, rfl⟩
    · have hJ0 : 0 < Jn m ns := by omega
      obtain ⟨u0, s0, v0, k0⟩ := stA m ns ds 0 0 (by norm_num) (by norm_num)
      have hr0 : rt0 0 = 1 := by simp [rt0]
      have hr1 : rt1 0 = 1 := by simp [rt1]
      have hv0 : vv m ns ds 0 = 2 := rfl
      have hp1 := pt_val hk' ds (0 + 1) 0 0 (by norm_num) (by omega)
        (by norm_num) (by norm_num)
      rw [u0, s0, v0, k0, hr0, hr1, hv0, hp0, hp1]
      obtain ⟨h0, K, hK, hD⟩ := on_A hA 0 0 hJ0 (by norm_num) 1 1 2
      refine ⟨Or.inr ⟨?_, ?_⟩, Or.inr ⟨h0, sgn_neg hK hD (by linarith)⟩⟩
      · have hVA : VA m ns 0 = o0 * SA m ns 0 := by unfold VA wA; simp
        simp only [fval, Rlot, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
          Matrix.head_cons]
        rw [hVA]; unfold o0; ring
      · have hS := (g_pos hA 0 0 hJ0).1
        have hSB := (hGL.1 0 hJ0).1
        have hSBA := (hGL.1 0 hJ0).2.1
        simp only [gS, if_pos (show (0:ℕ) < 2 by norm_num)] at hS
        have hk : cOf (sig ns ds 0) * VA m ns 0 = 0 := by simp [sig, cOf]
        have hVA : VA m ns 0 = o0 * SA m ns 0 := by unfold VA wA; simp
        rw [hk]
        simp only [Rlot, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
          Matrix.head_cons]
        rw [hVA]
        unfold aF o0
        have hS2 : 1 / 2 < SA m ns 0 := by linarith
        have e : SA m ns 0 * (((1 + 0) * 1 + ((SA m ns 0 - 0) / (1 + 0) + 1) * 0 * 2) /
            SA m ns 0) = 1 := by field_simp; ring
        rw [e]
        nlinarith
    · have hj : j < Jn m ns := by omega
      obtain ⟨u0, s0, v0, k0⟩ := stA m ns ds (4 * j + 1) j (by omega) (by omega)
      obtain ⟨r0e, r1e⟩ := rt_val (4 * j + 1) 0 (by omega) (by omega)
      have hp := pt_val hk' ds (4 * j + 1) j 0 (by omega) (by omega)
        (by omega) (by omega)
      have hp' := pt_val hk' ds (4 * j + 1 + 1) j 1 (by omega) (by omega)
        (by omega) (by omega)
      rw [u0, s0, v0, k0, hp, hp']
      obtain ⟨h0, K, hK, hD⟩ := on_A hA j 0 hj (by norm_num) (rt0 (4 * j + 1))
        (rt1 (4 * j + 1)) (vv m ns ds (4 * j + 1))
      obtain ⟨h0', K', hK', hD'⟩ := on_A hA j 1 hj (by norm_num) (rt0 (4 * j + 1))
        (rt1 (4 * j + 1)) (vv m ns ds (4 * j + 1))
      obtain ⟨t0, -, t1, -⟩ := ptT_bounds m ns j hm hns
      have e0 : rt0 (4 * j + 1) = -1 := by rw [r0e]; simp [r0of]
      have e1 : rt1 (4 * j + 1) = 1 := by rw [r1e]; simp [r1of]
      refine ⟨Or.inr ⟨h0, sgn_pos hK hD ?_⟩, Or.inr ⟨h0', sgn_neg hK' hD' ?_⟩⟩
      · rw [e0, e1]; linarith
      · rw [e0, e1]; linarith
    · have hj : j < Jn m ns := by omega
      obtain ⟨u0, s0, v0, k0⟩ := stA m ns ds (4 * j + 2) j (by omega) (by omega)
      obtain ⟨r0e, r1e⟩ := rt_val (4 * j + 2) 1 (by omega) (by omega)
      have hp := pt_val hk' ds (4 * j + 2) j 1 (by omega) (by omega)
        (by omega) (by omega)
      have hp' := pt_val hk' ds (4 * j + 2 + 1) j 2 (by omega) (by omega)
        (by omega) (by omega)
      rw [u0, s0, v0, k0, hp, hp']
      obtain ⟨h0, K, hK, hD⟩ := on_A hA j 1 hj (by norm_num) (rt0 (4 * j + 2))
        (rt1 (4 * j + 2)) (vv m ns ds (4 * j + 2))
      have e0 : rt0 (4 * j + 2) = -2 := by rw [r0e]; simp [r0of]
      have e1 : rt1 (4 * j + 2) = -2 := by rw [r1e]; simp [r1of]
      refine ⟨Or.inr ⟨h0, sgn_pos hK hD ?_⟩, Or.inl (lifted_rel_gadget hA j hj).1⟩
      rw [e0, e1]; linarith
    · have hj : j < Jn m ns := by omega
      obtain ⟨u0, s0, v0, k0⟩ := stB m ns ds (4 * j + 3) j (by omega) (by omega)
      obtain ⟨r0e, r1e⟩ := rt_val (4 * j + 3) 2 (by omega) (by omega)
      have hp := pt_val hk' ds (4 * j + 3) j 2 (by omega) (by omega)
        (by omega) (by omega)
      have hp' := pt_val hk' ds (4 * j + 3 + 1) j 3 (by omega) (by omega)
        (by omega) (by omega)
      rw [u0, s0, v0, k0, hp, hp']
      obtain ⟨h0, K, hK, hD⟩ := on_B hA j 2 hj (by norm_num) (by norm_num) (rt0 (4 * j + 3))
        (rt1 (4 * j + 3)) (vv m ns ds (4 * j + 3))
      obtain ⟨h0', K', hK', hD'⟩ := on_B hA j 3 hj (by norm_num) (by norm_num)
        (rt0 (4 * j + 3)) (rt1 (4 * j + 3)) (vv m ns ds (4 * j + 3))
      obtain ⟨-, t3, -, t2⟩ := ptT_bounds m ns j hm hns
      have e0 : rt0 (4 * j + 3) = 1 := by rw [r0e]; simp [r0of]
      have e1 : rt1 (4 * j + 3) = -1 := by rw [r1e]; simp [r1of]
      refine ⟨Or.inr ⟨h0, sgn_pos hK hD ?_⟩, Or.inr ⟨h0', sgn_neg hK' hD' ?_⟩⟩
      · rw [e0, e1]; linarith
      · rw [e0, e1]; linarith
    · have hj : j + 1 < Jn m ns := by omega
      obtain ⟨u0, s0, v0, k0⟩ := stB m ns ds (4 * j + 4) j (by omega) (by omega)
      obtain ⟨r0e, r1e⟩ := rt_val (4 * j + 4) 3 (by omega) (by omega)
      have hp := pt_val hk' ds (4 * j + 4) j 3 (by omega) (by omega)
        (by omega) (by omega)
      have hp' := pt_val hk' ds (4 * j + 4 + 1) (j + 1) 0 (by omega)
        (by omega) (by omega) (by omega)
      rw [u0, s0, v0, k0, hp, hp']
      obtain ⟨h0, K, hK, hD⟩ := on_B hA j 3 (by omega) (by norm_num) (by norm_num)
        (rt0 (4 * j + 4)) (rt1 (4 * j + 4)) (vv m ns ds (4 * j + 4))
      have e0 : rt0 (4 * j + 4) = -2 := by rw [r0e]; simp [r0of]
      have e1 : rt1 (4 * j + 4) = -2 := by rw [r1e]; simp [r1of]
      refine ⟨Or.inr ⟨h0, sgn_pos hK hD ?_⟩, Or.inl (lifted_rel_trans hA j hj).1⟩
      rw [e0, e1]; linarith

end Q2CL
