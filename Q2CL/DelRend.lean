import Q2CL.Defs
import Q2CL.Strictify
import Q2CL.TightNest
import Q2CL.LiftedRelGadget
import Q2CL.LiftedRelTrans
import Q2CL.ReliftDval
import Q2CL.LiftOn
import Q2CL.Normalization
import Q2CL.CwBound
import Q2CL.GadgetLines
import Q2CL.JSpec
import Q2CL.SliceEval
import Q2CL.ClassTrans
import Q2CL.FaceBasic

namespace Q2CL

open K4

noncomputable section

/-- Re-lift log-direction of a coordinate `X ∈ {U, S}` for rotation `r` and `log V`-speed `v`. -/
private def aF (X κ r v : ℝ) : ℝ := ((1 + κ) * r + ((X - κ) / (1 + κ) + 1) * κ * v) / X

/-- The `v` making `aF X κ r v - v = T`. -/
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

/-- An on-point: value zero, and the re-lift derivative is `-K (r0 (1-t) + r1 t)`, `K > 0`. -/
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

/-! ### The tight states of the chain with `R(o_1)` deleted -/

/-- `U` of the line of point `τ` of gadget `j`. -/
private def gU (m ns j τ : ℕ) : ℝ := if τ < 2 then UA m ns j else UB m ns j
/-- `S` of the line of point `τ` of gadget `j`. -/
private def gS (m ns j τ : ℕ) : ℝ := if τ < 2 then SA m ns j else SB m ns j

private def stU (m ns i : ℕ) : ℝ := gU m ns ((i - 1) / 4) ((i - 1) % 4)
private def stS (m ns i : ℕ) : ℝ := gS m ns ((i - 1) / 4) ((i - 1) % 4)
private def stV (m ns i : ℕ) : ℝ := ptV m ns ((i - 1) / 4) ((i - 1) % 4)
private def stK (m ns : ℕ) (ds : ℝ) (i : ℕ) : ℝ := cOf (sig ns ds ((i - 1) / 4)) * stV m ns i

/-- Rotations `−+`, `low`, `+−`, `low`. -/
private def r0of (τ : ℕ) : ℝ := if τ = 0 then -1 else if τ = 2 then 1 else -2
private def r1of (τ : ℕ) : ℝ := if τ = 0 then 1 else if τ = 2 then -1 else -2
/-- Front state uses rotation `(1, 1)`. -/
private def rt0 (i : ℕ) : ℝ := if i = 0 then 1 else r0of ((i - 1) % 4)
private def rt1 (i : ℕ) : ℝ := if i = 0 then 1 else r1of ((i - 1) % 4)

/-- `log V`-speeds: constant on same-line steps, solved on `A → B` and `B → A'` steps. -/
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

private lemma st_val (m ns : ℕ) (ds : ℝ) (i j τ : ℕ) (h1 : (i - 1) / 4 = j)
    (h2 : (i - 1) % 4 = τ) :
    stU m ns i = gU m ns j τ ∧ stS m ns i = gS m ns j τ ∧ stV m ns i = ptV m ns j τ ∧
    stK m ns ds i = cOf (sig ns ds j) * ptV m ns j τ := by
  unfold stK stV stU stS; rw [h1, h2]; exact ⟨rfl, rfl, rfl, rfl⟩

private lemma rt_val (i τ : ℕ) (hi : 1 ≤ i) (h2 : (i - 1) % 4 = τ) :
    rt0 i = r0of τ ∧ rt1 i = r1of τ := by
  unfold rt0 rt1; rw [if_neg (by omega), if_neg (by omega), h2]; exact ⟨rfl, rfl⟩

private lemma pt_val {m ns : ℕ} (ds : ℝ) (i j τ : ℕ) (hi1 : 1 ≤ i) (hi : i ≤ 4 * Jn m ns)
    (h1 : (i - 1) / 4 = j) (h2 : (i - 1) % 4 = τ) :
    Tpt m ns ds (skipIdx (4 * Jn m ns + 1) i) = gpt m ns ds j τ := by
  have hs : skipIdx (4 * Jn m ns + 1) i = i := by unfold skipIdx; rw [if_pos (by omega)]
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

/-- Coordinates of a tight state. -/
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

/-- An on-point of gadget `j` against its own tight state. -/
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

end

/-- Deleting `R(o_1)` (position `4J+1`) leaves a ranking with a chain. -/
theorem del_Rend {m ns : ℕ} {ds : ℝ} (hA : Adm m ns ds) :
    ∃ W, IsChainFn (4 * Jn m ns + 1)
      (fun i => Tpt m ns ds (skipIdx (4 * Jn m ns + 1) i)) W := by
  have hm := hA.1
  have hns := ns_pos hA
  obtain ⟨hg0, hg1, hJ2, -, -, -⟩ := J_spec hA
  have hGL := gadget_lines hA
  have hTN := tight_nest hA
  have hp0 : Tpt m ns ds (skipIdx (4 * Jn m ns + 1) 0) = Rlot o0 := by
    unfold skipIdx Tpt; simp
  apply strictify (4 * Jn m ns + 1) _ (stU m ns) (stS m ns) (stV m ns) (aS m ns ds)
    (bS m ns ds) (vv m ns ds)
  · -- coordinates
    intro i hi
    obtain ⟨u1, s1, v1, -⟩ := st_val m ns ds i ((i - 1) / 4) ((i - 1) % 4) rfl rfl
    obtain ⟨h1, h2, h3, -⟩ := g_pos hA ((i - 1) / 4) ((i - 1) % 4) (by omega)
    rw [u1, s1, v1]; exact ⟨h1, h2, h3⟩
  · -- nesting
    intro i hi
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
    · -- 4j+1 → 4j+2: same line A_j, −+ → low
      have hj : j < Jn m ns := by omega
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
    · -- 4j+2 → 4j+3: A_j → B_j, U–V binding
      have hj : j < Jn m ns := by omega
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
    · -- 4j+3 → 4j+4: same line B_j, +− → low
      have hj : j < Jn m ns := by omega
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
    · -- 4j+4 → 4j+5: B_j → A_{j+1}, S–V binding
      have hj : j + 1 < Jn m ns := by omega
      have hj' : j < Jn m ns := by omega
      obtain ⟨hkA0, hkAS⟩ := (g_pos hA (j + 1) 0 hj).2.2.2
      obtain ⟨hSA0, -⟩ := g_pos hA (j + 1) 0 hj
      simp only [gS, gU, ptV, if_pos (show (0:ℕ) < 2 by norm_num)] at hkA0 hkAS hSA0
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
        exact aF_vsolve _ _ hSA0 hkA0 hkAS
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
    simp only [aS, bS]
    rcases idx_cases i with rfl | ⟨j, rfl⟩ | ⟨j, rfl⟩ | ⟨j, rfl⟩ | ⟨j, rfl⟩
    · -- front: R(o0) and xa_0 against T_A(0) with rotation (1, 1)
      have hJ0 : 0 < Jn m ns := by omega
      obtain ⟨u0, s0, v0, k0⟩ := stA m ns ds 0 0 (by norm_num) (by norm_num)
      have hr0 : rt0 0 = 1 := by simp [rt0]
      have hr1 : rt1 0 = 1 := by simp [rt1]
      have hv0 : vv m ns ds 0 = 2 := rfl
      have hp1 := pt_val (m := m) (ns := ns) ds (0 + 1) 0 0 (by norm_num) (by omega)
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
    · -- 4j+1: A_j, rotation −+, xa_j and ya_j on
      have hj : j < Jn m ns := by omega
      obtain ⟨u0, s0, v0, k0⟩ := stA m ns ds (4 * j + 1) j (by omega) (by omega)
      obtain ⟨r0e, r1e⟩ := rt_val (4 * j + 1) 0 (by omega) (by omega)
      have hp := pt_val (m := m) (ns := ns) ds (4 * j + 1) j 0 (by omega) (by omega)
        (by omega) (by omega)
      have hp' := pt_val (m := m) (ns := ns) ds (4 * j + 1 + 1) j 1 (by omega) (by omega)
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
    · -- 4j+2: A_j, rotation low, ya_j on, yb_j strict (G2a)
      have hj : j < Jn m ns := by omega
      obtain ⟨u0, s0, v0, k0⟩ := stA m ns ds (4 * j + 2) j (by omega) (by omega)
      obtain ⟨r0e, r1e⟩ := rt_val (4 * j + 2) 1 (by omega) (by omega)
      have hp := pt_val (m := m) (ns := ns) ds (4 * j + 2) j 1 (by omega) (by omega)
        (by omega) (by omega)
      have hp' := pt_val (m := m) (ns := ns) ds (4 * j + 2 + 1) j 2 (by omega) (by omega)
        (by omega) (by omega)
      rw [u0, s0, v0, k0, hp, hp']
      obtain ⟨h0, K, hK, hD⟩ := on_A hA j 1 hj (by norm_num) (rt0 (4 * j + 2))
        (rt1 (4 * j + 2)) (vv m ns ds (4 * j + 2))
      have e0 : rt0 (4 * j + 2) = -2 := by rw [r0e]; simp [r0of]
      have e1 : rt1 (4 * j + 2) = -2 := by rw [r1e]; simp [r1of]
      refine ⟨Or.inr ⟨h0, sgn_pos hK hD ?_⟩, Or.inl (lifted_rel_gadget hA j hj).1⟩
      rw [e0, e1]; linarith
    · -- 4j+3: B_j, rotation +−, yb_j and xb_j on
      have hj : j < Jn m ns := by omega
      obtain ⟨u0, s0, v0, k0⟩ := stB m ns ds (4 * j + 3) j (by omega) (by omega)
      obtain ⟨r0e, r1e⟩ := rt_val (4 * j + 3) 2 (by omega) (by omega)
      have hp := pt_val (m := m) (ns := ns) ds (4 * j + 3) j 2 (by omega) (by omega)
        (by omega) (by omega)
      have hp' := pt_val (m := m) (ns := ns) ds (4 * j + 3 + 1) j 3 (by omega) (by omega)
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
    · -- 4j+4: B_j, rotation low, xb_j on, xa_{j+1} strict (G4)
      have hj : j + 1 < Jn m ns := by omega
      obtain ⟨u0, s0, v0, k0⟩ := stB m ns ds (4 * j + 4) j (by omega) (by omega)
      obtain ⟨r0e, r1e⟩ := rt_val (4 * j + 4) 3 (by omega) (by omega)
      have hp := pt_val (m := m) (ns := ns) ds (4 * j + 4) j 3 (by omega) (by omega)
        (by omega) (by omega)
      have hp' := pt_val (m := m) (ns := ns) ds (4 * j + 4 + 1) (j + 1) 0 (by omega)
        (by omega) (by omega) (by omega)
      rw [u0, s0, v0, k0, hp, hp']
      obtain ⟨h0, K, hK, hD⟩ := on_B hA j 3 (by omega) (by norm_num) (by norm_num) (rt0 (4 * j + 4)) (rt1 (4 * j + 4)) (vv m ns ds (4 * j + 4))
      have e0 : rt0 (4 * j + 4) = -2 := by rw [r0e]; simp [r0of]
      have e1 : rt1 (4 * j + 4) = -2 := by rw [r1e]; simp [r1of]
      refine ⟨Or.inr ⟨h0, sgn_pos hK hD ?_⟩, Or.inl (lifted_rel_trans hA j hj).1⟩
      rw [e0, e1]; linarith

end Q2CL
