import Q2CL.Defs
import Q2CL.Strictify
import Q2CL.TightNest
import Q2CL.LiftedRelGadget
import Q2CL.LiftedRelTrans
import Q2CL.ReliftDval
import Q2CL.LiftOn
import Q2CL.Normalization
import Q2CL.ClassTrans
import Q2CL.CwBound
import Q2CL.GadgetLines
import Q2CL.JSpec
import Q2CL.WEnvelope
import Q2CL.RhoBounds

namespace Q2CL

open K4

noncomputable section

/-! ### Generic helpers (re-lift directions) -/

/-- re-lift log-direction of a coordinate `X ∈ {U, S}` for rotation `r` and `log V`-speed `v`. -/
private def aE (U K r v : ℝ) : ℝ := ((1 + K) * r + ((U - K) / (1 + K) + 1) * K * v) / U

/-- The `v` making `aE X κ r v - v = T`. -/
private def vsolve (X κ r T : ℝ) : ℝ :=
  (T - (1 + κ) * r / X) / (((X - κ) / (1 + κ) + 1) * κ / X - 1)

private lemma aF_sub (X κ r v : ℝ) :
    aE X κ r v - v = (1 + κ) * r / X + v * (((X - κ) / (1 + κ) + 1) * κ / X - 1) := by
  unfold aE; ring

private lemma coef_neg {X κ : ℝ} (hX : 0 < X) (hκ0 : 0 ≤ κ) (hκX : κ < X) :
    ((X - κ) / (1 + κ) + 1) * κ / X - 1 < 0 := by
  have e : ((X - κ) / (1 + κ) + 1) * κ / X - 1 = (κ - X) / ((1 + κ) * X) := by
    field_simp; ring
  rw [e]; apply div_neg_of_neg_of_pos (by linarith); positivity

private lemma aF_vsolve {X κ : ℝ} (r T : ℝ) (hX : 0 < X) (hκ0 : 0 ≤ κ) (hκX : κ < X) :
    aE X κ r (vsolve X κ r T) - vsolve X κ r T = T := by
  rw [aF_sub]; unfold vsolve
  have hk := (coef_neg hX hκ0 hκX).ne
  generalize ((X - κ) / (1 + κ) + 1) * κ / X - 1 = k at hk ⊢
  field_simp; ring

private lemma aE_sub (U K r v : ℝ) (hU : 0 < U) (hK : 0 ≤ K) :
    aE U K r v - v = (1 + K) / U * r - (U - K) / ((1 + K) * U) * v := by
  have h1 : (1 + K) ≠ 0 := by positivity
  unfold aE; field_simp; ring

private lemma aE_mono (U K r r' v : ℝ) (hU : 0 < U) (hK : 0 ≤ K) (h : r' ≤ r) :
    aE U K r' v ≤ aE U K r v := by
  unfold aE
  apply div_le_div_of_nonneg_right _ hU.le
  nlinarith

private lemma aE_zero (U r v : ℝ) : aE U 0 r v = r / U := by
  unfold aE; ring

private lemma fin_lower (n : ℕ) (f : ℕ → ℝ) (h : ∀ i, i < n → 0 < f i) :
    ∃ L, 0 < L ∧ L ≤ 1 ∧ ∀ i, i < n → L ≤ f i := by
  induction n with
  | zero => exact ⟨1, by norm_num, le_rfl, fun i hi => absurd hi (Nat.not_lt_zero _)⟩
  | succ n ih =>
    obtain ⟨L, hL0, hL1, hL⟩ := ih (fun i hi => h i (by omega))
    refine ⟨min L (f n), lt_min hL0 (h n (by omega)), (min_le_left _ _).trans hL1, ?_⟩
    intro i hi
    rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
    · exact (min_le_left _ _).trans (hL i hi)
    · exact min_le_right _ _

private lemma fin_upper (n : ℕ) (f : ℕ → ℝ) :
    ∃ D, 0 < D ∧ ∀ i, i < n → f i ≤ D := by
  induction n with
  | zero => exact ⟨1, by norm_num, fun i hi => absurd hi (Nat.not_lt_zero _)⟩
  | succ n ih =>
    obtain ⟨D, hD0, hD⟩ := ih
    refine ⟨max D (f n), lt_max_of_lt_left hD0, ?_⟩
    intro i hi
    rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
    · exact (hD i hi).trans (le_max_left _ _)
    · exact le_max_right _ _

private lemma key_step (q L D η lA lB x : ℝ) (k N : ℕ) (hL0 : 0 < L) (hL1 : L ≤ 1)
    (hq : q = L / 2) (hkN : k ≤ N) (hlA : L ≤ lA) (hlB : lB ≤ 1) (hx : x ≤ 2 * D)
    (hD : 0 < D) (hη : η = q ^ N * L / (4 * D)) :
    η * x ≤ lA * q ^ k - lB * q ^ (k + 1) := by
  have hq0 : 0 < q := by rw [hq]; linarith
  have hq1 : q ≤ 1 := by rw [hq]; linarith
  have hqN : q ^ N ≤ q ^ k := pow_le_pow_of_le_one hq0.le hq1 hkN
  have hqk : 0 < q ^ k := pow_pos hq0 k
  have hqN0 : 0 < q ^ N := pow_pos hq0 N
  have hη0 : 0 ≤ η := by rw [hη]; positivity
  have e1 : η * x ≤ η * (2 * D) := mul_le_mul_of_nonneg_left hx hη0
  have e2 : η * (2 * D) = q ^ N * L / 2 := by rw [hη]; field_simp; norm_num
  have e3 : q ^ N * L ≤ q ^ k * L := mul_le_mul_of_nonneg_right hqN hL0.le
  have e4 : L * q ^ k ≤ lA * q ^ k := mul_le_mul_of_nonneg_right hlA hqk.le
  have e5 : lB * q ^ (k + 1) ≤ q ^ (k + 1) := by
    have := pow_pos hq0 (k + 1); nlinarith
  have e6 : q ^ (k + 1) = q ^ k * L / 2 := by rw [pow_succ, hq]; ring
  nlinarith

private lemma last_step (q L D η l y : ℝ) (k N : ℕ) (hL0 : 0 < L) (hL1 : L ≤ 1)
    (hq : q = L / 2) (hkN : k ≤ N) (hl : L ≤ l) (hy : y ≤ D) (hy0 : 0 ≤ y)
    (hD : 0 < D) (hη : η = q ^ N * L / (4 * D)) :
    y * η < l * q ^ k := by
  have hq0 : 0 < q := by rw [hq]; linarith
  have hq1 : q ≤ 1 := by rw [hq]; linarith
  have hqN : q ^ N ≤ q ^ k := pow_le_pow_of_le_one hq0.le hq1 hkN
  have hqk : 0 < q ^ k := pow_pos hq0 k
  have hη0 : 0 ≤ η := by rw [hη]; positivity
  have e1 : y * η ≤ D * η := mul_le_mul_of_nonneg_right hy hη0
  have e2 : D * η = q ^ N * L / 4 := by rw [hη]; field_simp
  have e3 : q ^ N * L ≤ q ^ k * L := mul_le_mul_of_nonneg_right hqN hL0.le
  have e4 : L * q ^ k ≤ l * q ^ k := mul_le_mul_of_nonneg_right hl hqk.le
  nlinarith

/-- An on-point: value `0`, and the first-order value along the re-lift direction is
`-K (r0 (1-t) + r1 t)` with `K > 0`. -/
private lemma on_gen (U S V s t r0 r1 v : ℝ) (hs0 : 0 ≤ s) (hs : s < 1) (hV : 0 ≤ V)
    (hU : 0 < U) (hS : 0 < S) (hH : 0 < hLift s (U * (1 - t) + S * t) V) :
    fval U S V (liftPt s t (U * (1 - t) + S * t) V) = 0 ∧
    ∃ K > 0, -(U * aE U (cOf s * V) r0 v) * liftPt s t (U * (1 - t) + S * t) V 0 -
        S * aE S (cOf s * V) r1 v * liftPt s t (U * (1 - t) + S * t) V 1 +
        V * v * liftPt s t (U * (1 - t) + S * t) V 3 = -K * (r0 * (1 - t) + r1 * t) := by
  have hc0 : 0 ≤ cOf s := by unfold cOf; apply div_nonneg hs0; linarith
  have hk : 0 < 1 + cOf s * V := by have := mul_nonneg hc0 hV; linarith
  refine ⟨lift_on U S V s t hs hk.ne' (by linarith), ?_⟩
  refine ⟨(1 - s) * (1 + cOf s * V) / (1 + hLift s (U * (1 - t) + S * t) V), ?_, ?_⟩
  · apply div_pos (mul_pos (by linarith) hk) (by linarith)
  · have := relift_dval U S V s t r0 r1 v hs hk hU.ne' hS.ne' (by linarith)
    unfold aE
    rw [this]

private lemma sgn_pos {K X D : ℝ} (hK : 0 < K) (hD : D = -K * X) (hX : X < 0) : 0 < D := by
  rw [hD]; nlinarith
private lemma sgn_neg {K X D : ℝ} (hK : 0 < K) (hD : D = -K * X) (hX : 0 < X) : D < 0 := by
  rw [hD]; nlinarith

/-! ### Gadget states -/

private def gU (m ns j τ : ℕ) : ℝ := if τ < 2 then UA m ns j else UB m ns j
private def gS (m ns j τ : ℕ) : ℝ := if τ < 2 then SA m ns j else SB m ns j

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

/-- An on-point of gadget `j` against its own tight state. -/
private lemma on_pt {m ns : ℕ} {ds : ℝ} (hA : Adm m ns ds) (j τ : ℕ) (hj : j < Jn m ns)
    (hτ : τ < 4) (r0 r1 v : ℝ) :
    fval (gU m ns j τ) (gS m ns j τ) (ptV m ns j τ) (gpt m ns ds j τ) = 0 ∧
    ∃ K > 0, -(gU m ns j τ * aE (gU m ns j τ) (cOf (sig ns ds j) * ptV m ns j τ) r0 v) *
        gpt m ns ds j τ 0 -
      gS m ns j τ * aE (gS m ns j τ) (cOf (sig ns ds j) * ptV m ns j τ) r1 v *
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

private lemma on_A {m ns : ℕ} {ds : ℝ} (hA : Adm m ns ds) (j τ : ℕ) (hj : j < Jn m ns)
    (hτ : τ < 2) (r0 r1 v : ℝ) :
    fval (UA m ns j) (SA m ns j) (VA m ns j) (gpt m ns ds j τ) = 0 ∧
    ∃ K > 0, -(UA m ns j * aE (UA m ns j) (cOf (sig ns ds j) * VA m ns j) r0 v) *
        gpt m ns ds j τ 0 -
      SA m ns j * aE (SA m ns j) (cOf (sig ns ds j) * VA m ns j) r1 v * gpt m ns ds j τ 1 +
      VA m ns j * v * gpt m ns ds j τ 3 =
      -K * (r0 * (1 - ptT m ns j τ) + r1 * ptT m ns j τ) := by
  have h := on_pt hA j τ hj (by omega) r0 r1 v
  simp only [gU, gS, ptV, if_pos hτ] at h
  exact h

private lemma on_B {m ns : ℕ} {ds : ℝ} (hA : Adm m ns ds) (j τ : ℕ) (hj : j < Jn m ns)
    (hτ : ¬ τ < 2) (hτ4 : τ < 4) (r0 r1 v : ℝ) :
    fval (UB m ns j) (SB m ns j) (VB m ns j) (gpt m ns ds j τ) = 0 ∧
    ∃ K > 0, -(UB m ns j * aE (UB m ns j) (cOf (sig ns ds j) * VB m ns j) r0 v) *
        gpt m ns ds j τ 0 -
      SB m ns j * aE (SB m ns j) (cOf (sig ns ds j) * VB m ns j) r1 v * gpt m ns ds j τ 1 +
      VB m ns j * v * gpt m ns ds j τ 3 =
      -K * (r0 * (1 - ptT m ns j τ) + r1 * ptT m ns j τ) := by
  have h := on_pt hA j τ hj hτ4 r0 r1 v
  simp only [gU, gS, ptV, if_neg hτ] at h
  exact h

private lemma nest_same {U S V κ v r0 r0' r1 r1' : ℝ} (hU : 0 < U) (hS : 0 < S) (hκ : 0 ≤ κ)
    (h0 : r0' ≤ r0) (h1 : r1' ≤ r1) :
    (U < U ∨ (U = U ∧ aE U κ r0' v ≤ aE U κ r0 v)) ∧
    (S < S ∨ (S = S ∧ aE S κ r1' v ≤ aE S κ r1 v)) ∧
    (U * V < V * U ∨ (U * V = V * U ∧ aE U κ r0' v - aE U κ r0 v ≤ v - v)) ∧
    (S * V < V * S ∨ (S * V = V * S ∧ aE S κ r1' v - aE S κ r1 v ≤ v - v)) := by
  have ha := aE_mono U κ r0 r0' v hU hκ h0
  have hb := aE_mono S κ r1 r1' v hS hκ h1
  exact ⟨Or.inr ⟨rfl, ha⟩, Or.inr ⟨rfl, hb⟩, Or.inr ⟨by ring, by linarith⟩,
    Or.inr ⟨by ring, by linarith⟩⟩

/-- `R(o)` on a state with `V = o S`; first-order value `S o (c - b)/(1 + o)`. -/
private lemma rlot_eval (U S V o a b c : ℝ) (ho : 0 < o) (hV : V = o * S) :
    fval U S V (Rlot o) = 0 ∧
    -(U * a) * Rlot o 0 - S * b * Rlot o 1 + V * c * Rlot o 3 = S * o * (c - b) / (1 + o) := by
  subst hV
  have ho1 : (0 : ℝ) < 1 + o := by linarith
  simp only [fval, Rlot, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Matrix.cons_val_three]
  constructor
  · field_simp; ring
  · field_simp; ring

/-! ### The states of the chain with `ya_j` deleted -/

/-- gadget of the vector after the `i`-th remaining lottery. -/
private def gIdx (j i : ℕ) : ℕ := if i ≤ 4 * j then (i - 1) / 4 else i / 4
/-- label slot (`< 2`: line `A`, otherwise line `B`). -/
private def gTau (j i : ℕ) : ℕ :=
  if i ≤ 4 * j then (i - 1) % 4 else if i = 4 * j + 1 then 2 else i % 4

private def cU (m ns j i : ℕ) : ℝ := gU m ns (gIdx j i) (gTau j i)
private def cS (m ns j i : ℕ) : ℝ := gS m ns (gIdx j i) (gTau j i)
private def cV (m ns j i : ℕ) : ℝ := ptV m ns (gIdx j i) (gTau j i)
private def cK (m ns : ℕ) (ds : ℝ) (j i : ℕ) : ℝ := cOf (sig ns ds (gIdx j i)) * cV m ns j i

private lemma idx_hd (j i : ℕ) (hi : i ≤ 4 * j) :
    gIdx j i = (i - 1) / 4 ∧ gTau j i = (i - 1) % 4 := by
  simp [gIdx, gTau, hi]

private lemma idx_tl (j i : ℕ) (hi : 4 * j + 2 ≤ i) : gIdx j i = i / 4 ∧ gTau j i = i % 4 := by
  simp [gIdx, gTau, show ¬ i ≤ 4 * j by omega, show i ≠ 4 * j + 1 by omega]

private lemma idx_md (j : ℕ) : gIdx j (4 * j + 1) = j ∧ gTau j (4 * j + 1) = 2 := by
  refine ⟨?_, ?_⟩ <;> simp [gIdx, gTau] <;> omega

private lemma c_A (m ns : ℕ) (ds : ℝ) (j i j' : ℕ) (h1 : gIdx j i = j') (h2 : gTau j i < 2) :
    cU m ns j i = UA m ns j' ∧ cS m ns j i = SA m ns j' ∧ cV m ns j i = VA m ns j' ∧
      cK m ns ds j i = cOf (sig ns ds j') * VA m ns j' := by
  unfold cK cV cU cS; rw [h1]; simp [gU, gS, ptV, h2]

private lemma c_B (m ns : ℕ) (ds : ℝ) (j i j' : ℕ) (h1 : gIdx j i = j') (h2 : ¬ gTau j i < 2) :
    cU m ns j i = UB m ns j' ∧ cS m ns j i = SB m ns j' ∧ cV m ns j i = VB m ns j' ∧
      cK m ns ds j i = cOf (sig ns ds j') * VB m ns j' := by
  unfold cK cV cU cS; rw [h1]; simp [gU, gS, ptV, h2]

private lemma hdA (m ns : ℕ) (ds : ℝ) (j i j' : ℕ) (hi : i ≤ 4 * j) (h1 : (i - 1) / 4 = j')
    (h2 : (i - 1) % 4 < 2) :
    cU m ns j i = UA m ns j' ∧ cS m ns j i = SA m ns j' ∧ cV m ns j i = VA m ns j' ∧
      cK m ns ds j i = cOf (sig ns ds j') * VA m ns j' := by
  obtain ⟨a, b⟩ := idx_hd j i hi
  exact c_A m ns ds j i j' (by rw [a, h1]) (by rw [b]; exact h2)

private lemma hdB (m ns : ℕ) (ds : ℝ) (j i j' : ℕ) (hi : i ≤ 4 * j) (h1 : (i - 1) / 4 = j')
    (h2 : ¬ (i - 1) % 4 < 2) :
    cU m ns j i = UB m ns j' ∧ cS m ns j i = SB m ns j' ∧ cV m ns j i = VB m ns j' ∧
      cK m ns ds j i = cOf (sig ns ds j') * VB m ns j' := by
  obtain ⟨a, b⟩ := idx_hd j i hi
  exact c_B m ns ds j i j' (by rw [a, h1]) (by rw [b]; exact h2)

private lemma tlA (m ns : ℕ) (ds : ℝ) (j i j' : ℕ) (hi : 4 * j + 2 ≤ i) (h1 : i / 4 = j')
    (h2 : i % 4 < 2) :
    cU m ns j i = UA m ns j' ∧ cS m ns j i = SA m ns j' ∧ cV m ns j i = VA m ns j' ∧
      cK m ns ds j i = cOf (sig ns ds j') * VA m ns j' := by
  obtain ⟨a, b⟩ := idx_tl j i hi
  exact c_A m ns ds j i j' (by rw [a, h1]) (by rw [b]; exact h2)

private lemma tlB (m ns : ℕ) (ds : ℝ) (j i j' : ℕ) (hi : 4 * j + 2 ≤ i) (h1 : i / 4 = j')
    (h2 : ¬ i % 4 < 2) :
    cU m ns j i = UB m ns j' ∧ cS m ns j i = SB m ns j' ∧ cV m ns j i = VB m ns j' ∧
      cK m ns ds j i = cOf (sig ns ds j') * VB m ns j' := by
  obtain ⟨a, b⟩ := idx_tl j i hi
  exact c_B m ns ds j i j' (by rw [a, h1]) (by rw [b]; exact h2)

private lemma mdB (m ns : ℕ) (ds : ℝ) (j : ℕ) :
    cU m ns j (4 * j + 1) = UB m ns j ∧ cS m ns j (4 * j + 1) = SB m ns j ∧
      cV m ns j (4 * j + 1) = VB m ns j ∧
      cK m ns ds j (4 * j + 1) = cOf (sig ns ds j) * VB m ns j := by
  obtain ⟨a, b⟩ := idx_md j
  exact c_B m ns ds j _ j a (by rw [b]; norm_num)

private lemma c_pos {m ns : ℕ} {ds : ℝ} (hA : Adm m ns ds) (j : ℕ) (hj : j < Jn m ns) (i : ℕ)
    (hi : i < 4 * Jn m ns) :
    0 < cS m ns j i ∧ cS m ns j i < cU m ns j i ∧ 1 < cV m ns j i ∧ 0 ≤ cK m ns ds j i ∧
      cK m ns ds j i < cS m ns j i := by
  have hg : gIdx j i < Jn m ns := by
    unfold gIdx; split_ifs <;> omega
  exact g_pos hA (gIdx j i) (gTau j i) hg

private lemma c_lam {m ns : ℕ} {ds : ℝ} (hA : Adm m ns ds) (j : ℕ) (hj : j < Jn m ns) (i : ℕ)
    (hi : i < 4 * Jn m ns) :
    0 < (cU m ns j i - cK m ns ds j i) / ((1 + cK m ns ds j i) * cU m ns j i) ∧
    (cU m ns j i - cK m ns ds j i) / ((1 + cK m ns ds j i) * cU m ns j i) ≤ 1 ∧
    0 < (cS m ns j i - cK m ns ds j i) / ((1 + cK m ns ds j i) * cS m ns j i) ∧
    (cS m ns j i - cK m ns ds j i) / ((1 + cK m ns ds j i) * cS m ns j i) ≤ 1 ∧
    0 ≤ (1 + cK m ns ds j i) / cU m ns j i ∧ 0 ≤ (1 + cK m ns ds j i) / cS m ns j i := by
  obtain ⟨hS0, hSU, -, hK0, hKS⟩ := c_pos hA j hj i hi
  have hU0 : 0 < cU m ns j i := by linarith
  have d1 : 0 < (1 + cK m ns ds j i) * cU m ns j i := by positivity
  have d2 : 0 < (1 + cK m ns ds j i) * cS m ns j i := by positivity
  refine ⟨div_pos (by linarith) d1, (div_le_one d1).2 (by nlinarith),
    div_pos (by linarith) d2, (div_le_one d2).2 (by nlinarith), by positivity, by positivity⟩

/-- The per-index bounds used by the tail. -/
private def FacP (m ns : ℕ) (ds : ℝ) (j : ℕ) (L D : ℝ) (i : ℕ) : Prop :=
  L ≤ (cU m ns j i - cK m ns ds j i) / ((1 + cK m ns ds j i) * cU m ns j i) ∧
  L ≤ (cS m ns j i - cK m ns ds j i) / ((1 + cK m ns ds j i) * cS m ns j i) ∧
  (1 + cK m ns ds j i) / cU m ns j i ≤ D ∧ (1 + cK m ns ds j i) / cS m ns j i ≤ D

private lemma tail_setup {m ns : ℕ} {ds : ℝ} (hA : Adm m ns ds) (j : ℕ) (hj : j < Jn m ns) :
    ∃ L D, 0 < L ∧ L ≤ 1 ∧ 0 < D ∧ ∀ i, i < 4 * Jn m ns → FacP m ns ds j L D i := by
  obtain ⟨L, hL0, hL1, hL⟩ := fin_lower (4 * Jn m ns)
    (fun i => min ((cU m ns j i - cK m ns ds j i) / ((1 + cK m ns ds j i) * cU m ns j i))
      ((cS m ns j i - cK m ns ds j i) / ((1 + cK m ns ds j i) * cS m ns j i)))
    (fun i hi => lt_min (c_lam hA j hj i hi).1 (c_lam hA j hj i hi).2.2.1)
  obtain ⟨D, hD0, hD⟩ := fin_upper (4 * Jn m ns)
    (fun i => (1 + cK m ns ds j i) / cU m ns j i + (1 + cK m ns ds j i) / cS m ns j i)
  refine ⟨L, D, hL0, hL1, hD0, fun i hi => ?_⟩
  obtain ⟨-, -, -, -, p1, p2⟩ := c_lam hA j hj i hi
  have h1 := hL i hi
  have h2 := hD i hi
  exact ⟨h1.trans (min_le_left _ _), h1.trans (min_le_right _ _), by linarith, by linarith⟩

/-! ### Nesting and relation predicates (the hypotheses of `strictify`) -/

private def NestP (U S V a b c U' S' V' a' b' c' : ℝ) : Prop :=
  (U' < U ∨ (U' = U ∧ a' ≤ a)) ∧ (S' < S ∨ (S' = S ∧ b' ≤ b)) ∧
  (U' * V < V' * U ∨ (U' * V = V' * U ∧ a' - a ≤ c' - c)) ∧
  (S' * V < V' * S ∨ (S' * V = V' * S ∧ b' - b ≤ c' - c))

private def RelP (U S V a b c : ℝ) (p p' : Lot 4) : Prop :=
  (0 < fval U S V p ∨ (fval U S V p = 0 ∧ 0 < -(U * a) * p 0 - S * b * p 1 + V * c * p 3)) ∧
  (fval U S V p' < 0 ∨
    (fval U S V p' = 0 ∧ -(U * a) * p' 0 - S * b * p' 1 + V * c * p' 3 < 0))

/-! ### Points of the deleted list -/

private lemma pt_zero {m ns : ℕ} {ds : ℝ} (j : ℕ) :
    Tpt m ns ds (skipIdx (4 * j + 2) 0) = Rlot o0 := by
  unfold skipIdx Tpt; simp

private lemma pt_hd {m ns : ℕ} (ds : ℝ) (j i j' τ : ℕ) (hj : j < Jn m ns) (hi1 : 1 ≤ i)
    (hi : i ≤ 4 * j + 1) (h1 : (i - 1) / 4 = j') (h2 : (i - 1) % 4 = τ) :
    Tpt m ns ds (skipIdx (4 * j + 2) i) = gpt m ns ds j' τ := by
  have hs : skipIdx (4 * j + 2) i = i := by unfold skipIdx; rw [if_pos (by omega)]
  rw [hs]; unfold Tpt
  rw [if_neg (by omega : i ≠ 0), if_neg (by omega : i ≠ 4 * Jn m ns + 1), h1, h2]

private lemma pt_tl {m ns : ℕ} (ds : ℝ) (j i j' τ : ℕ) (hi1 : 4 * j + 2 ≤ i)
    (hi : i < 4 * Jn m ns) (h1 : i / 4 = j') (h2 : i % 4 = τ) :
    Tpt m ns ds (skipIdx (4 * j + 2) i) = gpt m ns ds j' τ := by
  have hs : skipIdx (4 * j + 2) i = i + 1 := by unfold skipIdx; rw [if_neg (by omega)]
  rw [hs]; unfold Tpt
  rw [if_neg (by omega : i + 1 ≠ 0), if_neg (by omega : i + 1 ≠ 4 * Jn m ns + 1),
    show i + 1 - 1 = i by omega, h1, h2]

private lemma pt_end {m ns : ℕ} (ds : ℝ) (j : ℕ) (hj : j < Jn m ns) :
    Tpt m ns ds (skipIdx (4 * j + 2) (4 * Jn m ns)) = Rlot (o1 m ns) := by
  have hs : skipIdx (4 * j + 2) (4 * Jn m ns) = 4 * Jn m ns + 1 := by
    unfold skipIdx; rw [if_neg (by omega)]
  rw [hs]; unfold Tpt
  rw [if_neg (by omega), if_pos rfl]

/-! ### The tail (from `xa_j` on): `del_R0`-style directions -/

private def r0f (i : ℕ) : ℝ := if i % 4 = 2 then 1 else -1
private def r1f (i : ℕ) : ℝ := if i % 4 = 0 then 1 else -1
private def vf (q : ℝ) (i : ℕ) : ℝ := -q ^ (i / 2)
/-- rotations of the tail; `raise` after `xa_j`. -/
private def r0t (j i : ℕ) : ℝ := if i = 4 * j + 1 then 1 else r0f i
private def r1t (j i : ℕ) : ℝ := if i = 4 * j + 1 then 1 else r1f i
private def vt (j : ℕ) (q : ℝ) (i : ℕ) : ℝ := if i = 4 * j + 1 then vf q (4 * j + 2) else vf q i
private def tA (m ns : ℕ) (ds : ℝ) (j : ℕ) (η q : ℝ) (i : ℕ) : ℝ :=
  aE (cU m ns j i) (cK m ns ds j i) (η * r0t j i) (vt j q i)
private def tB (m ns : ℕ) (ds : ℝ) (j : ℕ) (η q : ℝ) (i : ℕ) : ℝ :=
  aE (cS m ns j i) (cK m ns ds j i) (η * r1t j i) (vt j q i)

set_option maxHeartbeats 1600000 in
private lemma tail_nest {m ns : ℕ} {ds : ℝ} (hA : Adm m ns ds) (j : ℕ) (hj : j < Jn m ns)
    (L D q η : ℝ) (hL0 : 0 < L) (hL1 : L ≤ 1) (hD0 : 0 < D) (hq : q = L / 2)
    (hη : η = q ^ (2 * Jn m ns) * L / (4 * D))
    (hfac : ∀ i, i < 4 * Jn m ns → FacP m ns ds j L D i) (i : ℕ) (hi1 : 4 * j + 1 ≤ i)
    (hi : i + 2 < 4 * Jn m ns + 1) :
    NestP (cU m ns j i) (cS m ns j i) (cV m ns j i) (tA m ns ds j η q i) (tB m ns ds j η q i)
      (vt j q i) (cU m ns j (i + 1)) (cS m ns j (i + 1)) (cV m ns j (i + 1))
      (tA m ns ds j η q (i + 1)) (tB m ns ds j η q (i + 1)) (vt j q (i + 1)) := by
  have hGL := gadget_lines hA
  have hTN := tight_nest hA
  have hq0 : 0 < q := by rw [hq]; linarith
  have hη0 : 0 ≤ η := by rw [hη]; positivity
  have hi0 : i < 4 * Jn m ns := by omega
  have hi1' : i + 1 < 4 * Jn m ns := by omega
  have hj' : i / 4 < Jn m ns := by omega
  obtain ⟨hS0, hSU, hV1, hK0, hKS⟩ := c_pos hA j hj i hi0
  obtain ⟨hS0', hSU', hV1', hK0', hKS'⟩ := c_pos hA j hj (i + 1) hi1'
  obtain ⟨hLU, hLS, hDU, hDS⟩ := hfac i hi0
  obtain ⟨hLU', hLS', hDU', hDS'⟩ := hfac (i + 1) hi1'
  obtain ⟨-, hlU1, -, hlS1, hPU, hPS⟩ := c_lam hA j hj i hi0
  obtain ⟨-, hlU1', -, hlS1', hPU', hPS'⟩ := c_lam hA j hj (i + 1) hi1'
  have hU0 : 0 < cU m ns j i := by linarith
  have hU0' : 0 < cU m ns j (i + 1) := by linarith
  unfold NestP tA tB
  rcases (by omega : i = 4 * j + 1 ∨ (4 * j + 2 ≤ i ∧
      (i % 4 = 0 ∨ i % 4 = 1 ∨ i % 4 = 2 ∨ i % 4 = 3))) with h | ⟨h2, h | h | h | h⟩
  · -- xa_j → yb_j : same line B_j, raise → +−
    have hv : vt j q (i + 1) = vt j q i := by
      unfold vt; rw [if_neg (by omega), if_pos h, show i + 1 = 4 * j + 2 by omega]
    have r0a : r0t j i = 1 := by simp [r0t, h]
    have r1a : r1t j i = 1 := by simp [r1t, h]
    have r0b : r0t j (i + 1) = 1 := by
      unfold r0t r0f; rw [if_neg (by omega), if_pos (by omega)]
    have r1b : r1t j (i + 1) = -1 := by
      unfold r1t r1f; rw [if_neg (by omega), if_neg (by omega)]
    obtain ⟨e1, e2, e3, e4⟩ : cU m ns j i = UB m ns j ∧ cS m ns j i = SB m ns j ∧
        cV m ns j i = VB m ns j ∧ cK m ns ds j i = cOf (sig ns ds j) * VB m ns j := by
      rw [h]; exact mdB m ns ds j
    obtain ⟨f1, f2, f3, f4⟩ := tlB m ns ds j (i + 1) j (by omega) (by omega) (by omega)
    simp only [e1, e2, e3, e4] at hU0 hS0 hK0
    rw [hv, r0a, r1a, r0b, r1b, e1, e2, e3, e4, f1, f2, f3, f4]
    exact nest_same hU0 hS0 hK0 le_rfl (by linarith)
  · -- xa_k → ya_k : same line A_k
    have hne : i ≠ 4 * j + 1 := by omega
    have hne' : i + 1 ≠ 4 * j + 1 := by omega
    have hv : vt j q (i + 1) = vt j q i := by
      unfold vt vf; rw [if_neg hne', if_neg hne, show (i + 1) / 2 = i / 2 by omega]
    have r0a : r0t j i = -1 := by simp [r0t, r0f, hne, h]
    have r0b : r0t j (i + 1) = -1 := by
      simp [r0t, r0f, hne', show i ≠ 4 * j by omega,show (i + 1) % 4 = 1 by omega]
    have r1a : r1t j i = 1 := by simp [r1t, r1f, hne, h]
    have r1b : r1t j (i + 1) = -1 := by
      simp [r1t, r1f, hne', show i ≠ 4 * j by omega,show (i + 1) % 4 = 1 by omega]
    obtain ⟨e1, e2, e3, e4⟩ := tlA m ns ds j i (i / 4) h2 rfl (by omega)
    obtain ⟨f1, f2, f3, f4⟩ := tlA m ns ds j (i + 1) (i / 4) (by omega) (by omega) (by omega)
    simp only [e1, e2, e3, e4] at hU0 hS0 hK0
    rw [hv, r0a, r1a, r0b, r1b, e1, e2, e3, e4, f1, f2, f3, f4]
    exact nest_same hU0 hS0 hK0 le_rfl (by linarith)
  · -- ya_k → yb_k : A_k → B_k, equality in (U, V)
    have hne : i ≠ 4 * j + 1 := by omega
    have hne' : i + 1 ≠ 4 * j + 1 := by omega
    have hv : vt j q i = -q ^ (i / 2) := by unfold vt vf; rw [if_neg hne]
    have hv' : vt j q (i + 1) = -q ^ (i / 2 + 1) := by
      unfold vt vf; rw [if_neg hne', show (i + 1) / 2 = i / 2 + 1 by omega]
    have r0a : r0t j i = -1 := by simp [r0t, r0f, hne, h]
    have r0b : r0t j (i + 1) = 1 := by
      simp [r0t, r0f, hne', show i ≠ 4 * j by omega,show (i + 1) % 4 = 2 by omega]
    have r1a : r1t j i = -1 := by simp [r1t, r1f, hne, h]
    have r1b : r1t j (i + 1) = -1 := by
      simp [r1t, r1f, hne', show i ≠ 4 * j by omega,show (i + 1) % 4 = 2 by omega]
    obtain ⟨e1, e2, e3, e4⟩ := tlA m ns ds j i (i / 4) h2 rfl (by omega)
    obtain ⟨f1, f2, f3, f4⟩ := tlB m ns ds j (i + 1) (i / 4) (by omega) (by omega) (by omega)
    simp only [e1, e2, e3, e4] at hS0 hU0 hK0 hLU hDU
    simp only [f1, f2, f3, f4] at hS0' hU0' hK0' hlU1' hDU'
    rw [hv, hv', r0a, r0b, r1a, r1b, e1, e2, e3, e4, f1, f2, f3, f4]
    obtain ⟨hSB1, hSBA, hSAU, hSBU, hUBA⟩ := hGL.1 (i / 4) hj'
    obtain ⟨tq, tl⟩ := hTN.1 (i / 4) hj'
    obtain ⟨-, -, -, -, hVA, -, -⟩ := cw_bound hA (i / 4) hj'
    refine ⟨Or.inl hUBA, Or.inl hSBA, Or.inr ⟨by linear_combination (-1 : ℝ) * tq, ?_⟩,
      Or.inl ?_⟩
    · have h1 := aE_sub _ _ (η * 1) (-q ^ (i / 2 + 1)) hU0' hK0'
      have h2 := aE_sub _ _ (η * -1) (-q ^ (i / 2)) hU0 hK0
      have hk := key_step q L D η _ _ _ (i / 2) (2 * Jn m ns) hL0 hL1 hq (by omega) hLU
        hlU1' (by linarith : (1 + cOf (sig ns ds (i / 4)) * VA m ns (i / 4)) / UA m ns (i / 4)
          + (1 + cOf (sig ns ds (i / 4)) * VB m ns (i / 4)) / UB m ns (i / 4) ≤ 2 * D)
        hD0 hη
      linear_combination h1 - h2 + hk
    · have hUA : 0 < UA m ns (i / 4) := hU0
      refine lt_of_mul_lt_mul_right ?_ hUA.le
      have := mul_lt_mul_of_pos_left tl (by linarith : (0 : ℝ) < VA m ns (i / 4))
      linear_combination this - SA m ns (i / 4) * tq
  · -- yb_k → xb_k : same line B_k
    have hne : i ≠ 4 * j + 1 := by omega
    have hne' : i + 1 ≠ 4 * j + 1 := by omega
    have hv : vt j q (i + 1) = vt j q i := by
      unfold vt vf; rw [if_neg hne', if_neg hne, show (i + 1) / 2 = i / 2 by omega]
    have r0a : r0t j i = 1 := by simp [r0t, r0f, hne, h]
    have r0b : r0t j (i + 1) = -1 := by
      simp [r0t, r0f, hne', show i ≠ 4 * j by omega,show (i + 1) % 4 = 3 by omega]
    have r1a : r1t j i = -1 := by simp [r1t, r1f, hne, h]
    have r1b : r1t j (i + 1) = -1 := by
      simp [r1t, r1f, hne', show i ≠ 4 * j by omega,show (i + 1) % 4 = 3 by omega]
    obtain ⟨e1, e2, e3, e4⟩ := tlB m ns ds j i (i / 4) h2 rfl (by omega)
    obtain ⟨f1, f2, f3, f4⟩ := tlB m ns ds j (i + 1) (i / 4) (by omega) (by omega) (by omega)
    simp only [e1, e2, e3, e4] at hU0 hS0 hK0
    rw [hv, r0a, r1a, r0b, r1b, e1, e2, e3, e4, f1, f2, f3, f4]
    exact nest_same hU0 hS0 hK0 (by linarith) le_rfl
  · -- xb_k → xa_{k+1} : B_k → A_{k+1}, equality in (S, V)
    have hne : i ≠ 4 * j + 1 := by omega
    have hne' : i + 1 ≠ 4 * j + 1 := by omega
    have hj1 : i / 4 + 1 < Jn m ns := by omega
    have hv : vt j q i = -q ^ (i / 2) := by unfold vt vf; rw [if_neg hne]
    have hv' : vt j q (i + 1) = -q ^ (i / 2 + 1) := by
      unfold vt vf; rw [if_neg hne', show (i + 1) / 2 = i / 2 + 1 by omega]
    have r0a : r0t j i = -1 := by simp [r0t, r0f, hne, h]
    have r0b : r0t j (i + 1) = -1 := by
      simp [r0t, r0f, hne', show i ≠ 4 * j by omega,show (i + 1) % 4 = 0 by omega]
    have r1a : r1t j i = -1 := by simp [r1t, r1f, hne, h]
    have r1b : r1t j (i + 1) = 1 := by
      simp [r1t, r1f, hne', show i ≠ 4 * j by omega,show (i + 1) % 4 = 0 by omega]
    obtain ⟨e1, e2, e3, e4⟩ := tlB m ns ds j i (i / 4) h2 rfl (by omega)
    obtain ⟨f1, f2, f3, f4⟩ := tlA m ns ds j (i + 1) (i / 4 + 1) (by omega) (by omega)
      (by omega)
    simp only [e1, e2, e3, e4] at hS0 hK0 hLS hDS
    simp only [f1, f2, f3, f4] at hS0' hK0' hlS1' hDS'
    rw [hv, hv', r0a, r0b, r1a, r1b, e1, e2, e3, e4, f1, f2, f3, f4]
    obtain ⟨hUA', hSA'⟩ := hGL.2 (i / 4) hj1
    obtain ⟨tq, tl, -⟩ := hTN.2 (i / 4) hj1
    refine ⟨Or.inl hUA', Or.inl hSA', Or.inl ?_,
      Or.inr ⟨by linear_combination (-1 : ℝ) * tq, ?_⟩⟩
    · refine lt_of_mul_lt_mul_right ?_ hS0'.le
      have hVA' := (cw_bound hA (i / 4 + 1) hj1).2.2.2.2.1
      have := mul_lt_mul_of_pos_left tl (by linarith : (0 : ℝ) < VA m ns (i / 4 + 1))
      linear_combination this - UA m ns (i / 4 + 1) * tq
    · have h1 := aE_sub _ _ (η * 1) (-q ^ (i / 2 + 1)) hS0' hK0'
      have h2 := aE_sub _ _ (η * -1) (-q ^ (i / 2)) hS0 hK0
      have hk := key_step q L D η _ _ _ (i / 2) (2 * Jn m ns) hL0 hL1 hq (by omega) hLS
        hlS1' (by linarith : (1 + cOf (sig ns ds (i / 4)) * VB m ns (i / 4)) / SB m ns (i / 4)
          + (1 + cOf (sig ns ds (i / 4 + 1)) * VA m ns (i / 4 + 1)) / SA m ns (i / 4 + 1)
            ≤ 2 * D)
        hD0 hη
      linear_combination h1 - h2 + hk

set_option maxHeartbeats 1600000 in
private lemma tail_rel {m ns : ℕ} {ds : ℝ} (hA : Adm m ns ds) (j : ℕ) (hj : j < Jn m ns)
    (L D q η : ℝ) (hL0 : 0 < L) (hL1 : L ≤ 1) (hD0 : 0 < D) (hq : q = L / 2)
    (hη : η = q ^ (2 * Jn m ns) * L / (4 * D)) (hη0 : 0 < η)
    (hfac : ∀ i, i < 4 * Jn m ns → FacP m ns ds j L D i) (i : ℕ) (hi1 : 4 * j + 1 ≤ i)
    (hi : i + 1 < 4 * Jn m ns + 1) :
    RelP (cU m ns j i) (cS m ns j i) (cV m ns j i) (tA m ns ds j η q i) (tB m ns ds j η q i)
      (vt j q i) (Tpt m ns ds (skipIdx (4 * j + 2) i))
      (Tpt m ns ds (skipIdx (4 * j + 2) (i + 1))) := by
  have hm := hA.1
  have hns := ns_pos hA
  have hi0 : i < 4 * Jn m ns := by omega
  have hj' : i / 4 < Jn m ns := by omega
  obtain ⟨hS0, hSU, hV1, hK0, hKS⟩ := c_pos hA j hj i hi0
  obtain ⟨hLU, hLS, hDU, hDS⟩ := hfac i hi0
  obtain ⟨-, -, -, -, hPU, hPS⟩ := c_lam hA j hj i hi0
  unfold RelP tA tB
  rcases (by omega : i = 4 * j + 1 ∨ (4 * j + 2 ≤ i ∧
      (i % 4 = 0 ∨ i % 4 = 1 ∨ i % 4 = 2 ∨ i % 4 = 3))) with h | ⟨h2, h | h | h | h⟩
  · -- B_j, raise: xa_j strictly above (G2c), yb_j on
    have r0a : r0t j i = 1 := by unfold r0t; rw [if_pos h]
    have r1a : r1t j i = 1 := by unfold r1t; rw [if_pos h]
    obtain ⟨e1, e2, e3, e4⟩ : cU m ns j i = UB m ns j ∧ cS m ns j i = SB m ns j ∧
        cV m ns j i = VB m ns j ∧ cK m ns ds j i = cOf (sig ns ds j) * VB m ns j := by
      rw [h]; exact mdB m ns ds j
    have hp := pt_hd (m := m) (ns := ns) ds j i j 0 hj (by omega) (by omega) (by omega)
      (by omega)
    have hp' := pt_tl (m := m) (ns := ns) ds j (i + 1) j 2 (by omega) (by omega) (by omega)
      (by omega)
    rw [e1, e2, e3, e4, r0a, r1a, hp, hp']
    obtain ⟨h0, K, hK, hD⟩ := on_B hA j 2 hj (by norm_num) (by norm_num) (η * 1) (η * 1)
      (vt j q i)
    exact ⟨Or.inl (lifted_rel_gadget hA j hj).2.2.1,
      Or.inr ⟨h0, sgn_neg hK hD (by nlinarith)⟩⟩
  · -- A_k, −+: xa_k and ya_k on
    have hne : i ≠ 4 * j + 1 := by omega
    have r0a : r0t j i = -1 := by simp [r0t, r0f, hne, h]
    have r1a : r1t j i = 1 := by simp [r1t, r1f, hne, h]
    obtain ⟨e1, e2, e3, e4⟩ := tlA m ns ds j i (i / 4) h2 rfl (by omega)
    have hp := pt_tl (m := m) (ns := ns) ds j i (i / 4) 0 h2 hi0 rfl h
    have hp' := pt_tl (m := m) (ns := ns) ds j (i + 1) (i / 4) 1 (by omega) (by omega)
      (by omega) (by omega)
    rw [e1, e2, e3, e4, r0a, r1a, hp, hp']
    obtain ⟨h0, K, hK, hD⟩ := on_A hA (i / 4) 0 hj' (by norm_num) (η * -1) (η * 1) (vt j q i)
    obtain ⟨h0', K', hK', hD'⟩ := on_A hA (i / 4) 1 hj' (by norm_num) (η * -1) (η * 1)
      (vt j q i)
    obtain ⟨t0, -, t1, -⟩ := ptT_bounds m ns (i / 4) hm hns
    exact ⟨Or.inr ⟨h0, sgn_pos hK hD (by nlinarith)⟩, Or.inr ⟨h0', sgn_neg hK' hD' (by nlinarith)⟩⟩
  · -- A_k, low: ya_k on, yb_k strictly below (G2a)
    have hne : i ≠ 4 * j + 1 := by omega
    have r0a : r0t j i = -1 := by simp [r0t, r0f, hne, h]
    have r1a : r1t j i = -1 := by simp [r1t, r1f, hne, h]
    obtain ⟨e1, e2, e3, e4⟩ := tlA m ns ds j i (i / 4) h2 rfl (by omega)
    have hp := pt_tl (m := m) (ns := ns) ds j i (i / 4) 1 h2 hi0 rfl h
    have hp' := pt_tl (m := m) (ns := ns) ds j (i + 1) (i / 4) 2 (by omega) (by omega)
      (by omega) (by omega)
    rw [e1, e2, e3, e4, r0a, r1a, hp, hp']
    obtain ⟨h0, K, hK, hD⟩ := on_A hA (i / 4) 1 hj' (by norm_num) (η * -1) (η * -1) (vt j q i)
    exact ⟨Or.inr ⟨h0, sgn_pos hK hD (by nlinarith)⟩,
      Or.inl (lifted_rel_gadget hA (i / 4) hj').1⟩
  · -- B_k, +−: yb_k and xb_k on
    have hne : i ≠ 4 * j + 1 := by omega
    have r0a : r0t j i = 1 := by simp [r0t, r0f, hne, h]
    have r1a : r1t j i = -1 := by simp [r1t, r1f, hne, h]
    obtain ⟨e1, e2, e3, e4⟩ := tlB m ns ds j i (i / 4) h2 rfl (by omega)
    have hp := pt_tl (m := m) (ns := ns) ds j i (i / 4) 2 h2 hi0 rfl h
    have hp' := pt_tl (m := m) (ns := ns) ds j (i + 1) (i / 4) 3 (by omega) (by omega)
      (by omega) (by omega)
    rw [e1, e2, e3, e4, r0a, r1a, hp, hp']
    obtain ⟨h0, K, hK, hD⟩ := on_B hA (i / 4) 2 hj' (by norm_num) (by norm_num) (η * 1)
      (η * -1) (vt j q i)
    obtain ⟨h0', K', hK', hD'⟩ := on_B hA (i / 4) 3 hj' (by norm_num) (by norm_num) (η * 1)
      (η * -1) (vt j q i)
    obtain ⟨-, t3, -, t2⟩ := ptT_bounds m ns (i / 4) hm hns
    exact ⟨Or.inr ⟨h0, sgn_pos hK hD (by nlinarith)⟩, Or.inr ⟨h0', sgn_neg hK' hD' (by nlinarith)⟩⟩
  · -- B_k, low: xb_k on; then xa_{k+1} (G4) or `R(o_1)`
    have hne : i ≠ 4 * j + 1 := by omega
    have r0a : r0t j i = -1 := by simp [r0t, r0f, hne, h]
    have r1a : r1t j i = -1 := by simp [r1t, r1f, hne, h]
    have hv : vt j q i = -q ^ (i / 2) := by unfold vt vf; rw [if_neg hne]
    obtain ⟨e1, e2, e3, e4⟩ := tlB m ns ds j i (i / 4) h2 rfl (by omega)
    have hp := pt_tl (m := m) (ns := ns) ds j i (i / 4) 3 h2 hi0 rfl h
    simp only [e1, e2, e3, e4] at hS0 hK0 hLS hDS hPS
    rw [e1, e2, e3, e4, r0a, r1a, hp]
    obtain ⟨h0, K, hK, hD⟩ := on_B hA (i / 4) 3 hj' (by norm_num) (by norm_num) (η * -1)
      (η * -1) (vt j q i)
    refine ⟨Or.inr ⟨h0, sgn_pos hK hD (by nlinarith)⟩, ?_⟩
    by_cases hl : i + 1 < 4 * Jn m ns
    · rw [pt_tl (m := m) (ns := ns) ds j (i + 1) (i / 4 + 1) 0 (by omega) hl (by omega)
        (by omega)]
      exact Or.inl (lifted_rel_trans hA (i / 4) (by omega)).1
    · have hJe : Jn m ns = i / 4 + 1 := by omega
      rw [show i + 1 = 4 * Jn m ns by omega, pt_end ds j hj]
      have hwB : wB m ns (i / 4) = o1 m ns := by
        unfold wB o1 wA; rw [hJe, Finset.prod_range_succ]; ring
      have ho1 : 0 < o1 m ns := by
        have := ((w_envelope hA).1 (Jn m ns) le_rfl).1
        unfold o1; unfold o0 at this; linarith
      have hVB : VB m ns (i / 4) = o1 m ns * SB m ns (i / 4) := by unfold VB; rw [hwB]
      obtain ⟨r1, r2⟩ := rlot_eval (UB m ns (i / 4)) (SB m ns (i / 4)) (VB m ns (i / 4))
        (o1 m ns) (aE (UB m ns (i / 4)) (cOf (sig ns ds (i / 4)) * VB m ns (i / 4)) (η * -1)
          (vt j q i))
        (aE (SB m ns (i / 4)) (cOf (sig ns ds (i / 4)) * VB m ns (i / 4)) (η * -1)
          (vt j q i)) (vt j q i) ho1 hVB
      refine Or.inr ⟨r1, ?_⟩
      rw [r2]
      have h1 := aE_sub _ _ (η * -1) (vt j q i) hS0 hK0
      have hk := last_step q L D η _ _ (i / 2) (2 * Jn m ns) hL0 hL1 hq (by omega) hLS hDS
        hPS hD0 hη
      have hcb : vt j q i - aE (SB m ns (i / 4)) (cOf (sig ns ds (i / 4)) * VB m ns (i / 4))
          (η * -1) (vt j q i) < 0 := by
        rw [hv] at h1 ⊢; nlinarith
      apply div_neg_of_neg_of_pos _ (by linarith)
      exact mul_neg_of_pos_of_neg (mul_pos hS0 ho1) hcb

/-! ### The head (up to `xb_{j-1}`): `del_Rend`-style directions -/

/-- Rotations `−+`, `low`, `+−`, `low`. -/
private def r0of (τ : ℕ) : ℝ := if τ = 0 then -1 else if τ = 2 then 1 else -2
private def r1of (τ : ℕ) : ℝ := if τ = 0 then 1 else if τ = 2 then -1 else -2
/-- Front state uses rotation `(1, 1)`. -/
private def rt0 (i : ℕ) : ℝ := if i = 0 then 1 else r0of ((i - 1) % 4)
private def rt1 (i : ℕ) : ℝ := if i = 0 then 1 else r1of ((i - 1) % 4)

/-- `log V`-speeds: constant on same-line steps, solved on `A → B` and `B → A'` steps. -/
private def vvH (m ns : ℕ) (ds : ℝ) (j : ℕ) : ℕ → ℝ
  | 0 => 2
  | i + 1 =>
    if i % 4 = 2 then
      vsolve (cU m ns j (i + 1)) (cK m ns ds j (i + 1)) (rt0 (i + 1))
        (aE (cU m ns j i) (cK m ns ds j i) (rt0 i) (vvH m ns ds j i) - vvH m ns ds j i)
    else if i % 4 = 0 ∧ i ≠ 0 then
      vsolve (cS m ns j (i + 1)) (cK m ns ds j (i + 1)) (rt1 (i + 1))
        (aE (cS m ns j i) (cK m ns ds j i) (rt1 i) (vvH m ns ds j i) - vvH m ns ds j i)
    else vvH m ns ds j i

private def qA (m ns : ℕ) (ds : ℝ) (j i : ℕ) : ℝ :=
  aE (cU m ns j i) (cK m ns ds j i) (rt0 i) (vvH m ns ds j i)
private def qB (m ns : ℕ) (ds : ℝ) (j i : ℕ) : ℝ :=
  aE (cS m ns j i) (cK m ns ds j i) (rt1 i) (vvH m ns ds j i)

private lemma rt_val (i τ : ℕ) (hi : 1 ≤ i) (h2 : (i - 1) % 4 = τ) :
    rt0 i = r0of τ ∧ rt1 i = r1of τ := by
  unfold rt0 rt1; rw [if_neg (by omega), if_neg (by omega), h2]; exact ⟨rfl, rfl⟩

private lemma idx_cases (i : ℕ) : i = 0 ∨ (∃ k, i = 4 * k + 1) ∨ (∃ k, i = 4 * k + 2) ∨
    (∃ k, i = 4 * k + 3) ∨ (∃ k, i = 4 * k + 4) := by
  rcases Nat.eq_zero_or_pos i with h | h
  · exact Or.inl h
  · have h4 : (i - 1) % 4 = 0 ∨ (i - 1) % 4 = 1 ∨ (i - 1) % 4 = 2 ∨ (i - 1) % 4 = 3 := by
      omega
    rcases h4 with h4 | h4 | h4 | h4
    · exact Or.inr (Or.inl ⟨(i - 1) / 4, by omega⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨(i - 1) / 4, by omega⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨(i - 1) / 4, by omega⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨(i - 1) / 4, by omega⟩)))

set_option maxHeartbeats 1600000 in
private lemma head_nest {m ns : ℕ} {ds : ℝ} (hA : Adm m ns ds) (j : ℕ) (hj : j < Jn m ns)
    (i : ℕ) (hi : i + 1 ≤ 4 * j) :
    NestP (cU m ns j i) (cS m ns j i) (cV m ns j i) (qA m ns ds j i) (qB m ns ds j i)
      (vvH m ns ds j i) (cU m ns j (i + 1)) (cS m ns j (i + 1)) (cV m ns j (i + 1))
      (qA m ns ds j (i + 1)) (qB m ns ds j (i + 1)) (vvH m ns ds j (i + 1)) := by
  have hGL := gadget_lines hA
  have hTN := tight_nest hA
  unfold NestP
  rcases idx_cases i with rfl | ⟨k, rfl⟩ | ⟨k, rfl⟩ | ⟨k, rfl⟩ | ⟨k, rfl⟩
  · -- front → after xa_0: same line A_0, (1,1) → (−1,1)
    have hJ0 : 0 < Jn m ns := by omega
    obtain ⟨u0, s0, v0, k0⟩ := hdA m ns ds j 0 0 (by omega) (by norm_num) (by norm_num)
    obtain ⟨u1, s1, v1, k1⟩ := hdA m ns ds j (0 + 1) 0 (by omega) (by norm_num) (by norm_num)
    obtain ⟨r0e, r1e⟩ := rt_val (0 + 1) 0 (by norm_num) (by norm_num)
    have hr0 : rt0 0 = 1 := by simp [rt0]
    have hr1 : rt1 0 = 1 := by simp [rt1]
    have hv : vvH m ns ds j (0 + 1) = vvH m ns ds j 0 := by simp [vvH]
    obtain ⟨hS, hSU, -, hk, -⟩ := g_pos hA 0 0 hJ0
    simp only [gS, gU, ptV, if_pos (show (0:ℕ) < 2 by norm_num)] at hS hSU hk
    simp only [qA, qB]
    rw [u0, s0, v0, k0, u1, s1, v1, k1, hv, r0e, r1e, hr0, hr1]
    exact nest_same (by linarith) hS hk (by norm_num [r0of]) (by norm_num [r1of])
  · -- 4k+1 → 4k+2: same line A_k, −+ → low
    have hk : k < Jn m ns := by omega
    obtain ⟨u0, s0, v0, k0⟩ := hdA m ns ds j (4 * k + 1) k (by omega) (by omega) (by omega)
    obtain ⟨u1, s1, v1, k1⟩ := hdA m ns ds j (4 * k + 1 + 1) k (by omega) (by omega)
      (by omega)
    obtain ⟨r0e, r1e⟩ := rt_val (4 * k + 1) 0 (by omega) (by omega)
    obtain ⟨r0e', r1e'⟩ := rt_val (4 * k + 1 + 1) 1 (by omega) (by omega)
    have hv : vvH m ns ds j (4 * k + 1 + 1) = vvH m ns ds j (4 * k + 1) := by
      rw [vvH, if_neg (by omega), if_neg (by omega)]
    obtain ⟨hS, hSU, -, hκ, -⟩ := g_pos hA k 0 hk
    simp only [gS, gU, ptV, if_pos (show (0:ℕ) < 2 by norm_num)] at hS hSU hκ
    simp only [qA, qB]
    rw [u0, s0, v0, k0, u1, s1, v1, k1, hv, r0e, r1e, r0e', r1e']
    exact nest_same (by linarith) hS hκ (by simp [r0of]) (by simp [r1of]; norm_num)
  · -- 4k+2 → 4k+3: A_k → B_k, U–V binding
    have hk : k < Jn m ns := by omega
    obtain ⟨hkB0, hkBS⟩ := (g_pos hA k 2 hk).2.2.2
    obtain ⟨hSB0, hSBU, -⟩ := g_pos hA k 2 hk
    simp only [gS, gU, ptV, if_neg (show ¬ (2:ℕ) < 2 by norm_num)] at hkB0 hkBS hSB0 hSBU
    obtain ⟨u0, s0, v0, k0⟩ := hdA m ns ds j (4 * k + 2) k (by omega) (by omega) (by omega)
    obtain ⟨u1, s1, v1, k1⟩ := hdB m ns ds j (4 * k + 2 + 1) k (by omega) (by omega)
      (by omega)
    have hv : vvH m ns ds j (4 * k + 2 + 1) = vsolve (cU m ns j (4 * k + 2 + 1))
        (cK m ns ds j (4 * k + 2 + 1)) (rt0 (4 * k + 2 + 1))
        (qA m ns ds j (4 * k + 2) - vvH m ns ds j (4 * k + 2)) := by
      rw [vvH, if_pos (by omega)]; rfl
    have key : qA m ns ds j (4 * k + 2 + 1) - vvH m ns ds j (4 * k + 2 + 1) =
        qA m ns ds j (4 * k + 2) - vvH m ns ds j (4 * k + 2) := by
      unfold qA at hv ⊢; rw [hv]
      rw [u1, k1]
      exact aF_vsolve _ _ (by linarith) hkB0 (by linarith)
    obtain ⟨hSB1, hSBA, hSAU, -, hUBA⟩ := hGL.1 k hk
    obtain ⟨eUV, hSUc⟩ := hTN.1 k hk
    have hVA : 1 < VA m ns k := (cw_bound hA k hk).2.2.2.2.1
    rw [u0, s0, v0, u1, s1, v1]
    refine ⟨Or.inl hUBA, Or.inl hSBA, Or.inr ⟨by linear_combination -eUV, by linarith⟩,
      Or.inl ?_⟩
    have hUA : 0 < UA m ns k := by linarith
    refine lt_of_mul_lt_mul_right ?_ hUA.le
    have h1 : SB m ns k * UA m ns k * VA m ns k < UB m ns k * SA m ns k * VA m ns k :=
      mul_lt_mul_of_pos_right hSUc (by linarith)
    linear_combination h1 - SA m ns k * eUV
  · -- 4k+3 → 4k+4: same line B_k, +− → low
    have hk : k < Jn m ns := by omega
    obtain ⟨u0, s0, v0, k0⟩ := hdB m ns ds j (4 * k + 3) k (by omega) (by omega) (by omega)
    obtain ⟨u1, s1, v1, k1⟩ := hdB m ns ds j (4 * k + 3 + 1) k (by omega) (by omega)
      (by omega)
    obtain ⟨r0e, r1e⟩ := rt_val (4 * k + 3) 2 (by omega) (by omega)
    obtain ⟨r0e', r1e'⟩ := rt_val (4 * k + 3 + 1) 3 (by omega) (by omega)
    have hv : vvH m ns ds j (4 * k + 3 + 1) = vvH m ns ds j (4 * k + 3) := by
      rw [vvH, if_neg (by omega), if_neg (by omega)]
    obtain ⟨hS, hSU, -, hκ, -⟩ := g_pos hA k 2 hk
    simp only [gS, gU, ptV, if_neg (show ¬ (2:ℕ) < 2 by norm_num)] at hS hSU hκ
    simp only [qA, qB]
    rw [u0, s0, v0, k0, u1, s1, v1, k1, hv, r0e, r1e, r0e', r1e']
    exact nest_same (by linarith) hS hκ (by norm_num [r0of]) (by norm_num [r1of])
  · -- 4k+4 → 4k+5: B_k → A_{k+1}, S–V binding
    have hk : k + 1 < Jn m ns := by omega
    have hk' : k < Jn m ns := by omega
    obtain ⟨hkA0, hkAS⟩ := (g_pos hA (k + 1) 0 hk).2.2.2
    obtain ⟨hSA0, -⟩ := g_pos hA (k + 1) 0 hk
    simp only [gS, gU, ptV, if_pos (show (0:ℕ) < 2 by norm_num)] at hkA0 hkAS hSA0
    obtain ⟨u0, s0, v0, k0⟩ := hdB m ns ds j (4 * k + 4) k (by omega) (by omega) (by omega)
    obtain ⟨u1, s1, v1, k1⟩ := hdA m ns ds j (4 * k + 4 + 1) (k + 1) (by omega) (by omega)
      (by omega)
    have hv : vvH m ns ds j (4 * k + 4 + 1) = vsolve (cS m ns j (4 * k + 4 + 1))
        (cK m ns ds j (4 * k + 4 + 1)) (rt1 (4 * k + 4 + 1))
        (qB m ns ds j (4 * k + 4) - vvH m ns ds j (4 * k + 4)) := by
      rw [vvH, if_neg (by omega), if_pos ⟨by omega, by omega⟩]; rfl
    have key : qB m ns ds j (4 * k + 4 + 1) - vvH m ns ds j (4 * k + 4 + 1) =
        qB m ns ds j (4 * k + 4) - vvH m ns ds j (4 * k + 4) := by
      unfold qB at hv ⊢; rw [hv]
      rw [s1, k1]
      exact aF_vsolve _ _ hSA0 hkA0 hkAS
    obtain ⟨hU', hS'⟩ := hGL.2 k hk
    obtain ⟨eSV, hUSc, -⟩ := hTN.2 k hk
    have hSB1 := (hGL.1 k hk').1
    have hVB : 1 < VB m ns k := (cw_bound hA k hk').2.2.2.2.2.1
    rw [u0, s0, v0, u1, s1, v1]
    refine ⟨Or.inl hU', Or.inl hS', Or.inl ?_, Or.inr ⟨by linear_combination -eSV,
      by linarith⟩⟩
    have hSB : 0 < SB m ns k := by linarith [(gadget_lines hA).1 k hk']
    have hg1 := (J_spec hA).2.1
    have hSB' : 0 < SB m ns k := by linarith
    refine lt_of_mul_lt_mul_right ?_ hSB'.le
    have h1 : UA m ns (k + 1) * SB m ns k * VB m ns k <
        UB m ns k * SA m ns (k + 1) * VB m ns k :=
      mul_lt_mul_of_pos_right hUSc (by linarith)
    linear_combination h1 - UB m ns k * eSV

set_option maxHeartbeats 1600000 in
private lemma head_rel {m ns : ℕ} {ds : ℝ} (hA : Adm m ns ds) (j : ℕ) (hj : j < Jn m ns)
    (i : ℕ) (hi : i ≤ 4 * j) (hj1 : 1 ≤ j) :
    RelP (cU m ns j i) (cS m ns j i) (cV m ns j i) (qA m ns ds j i) (qB m ns ds j i)
      (vvH m ns ds j i) (Tpt m ns ds (skipIdx (4 * j + 2) i))
      (Tpt m ns ds (skipIdx (4 * j + 2) (i + 1))) := by
  have hm := hA.1
  have hns := ns_pos hA
  have hGL := gadget_lines hA
  unfold RelP
  simp only [qA, qB]
  rcases idx_cases i with rfl | ⟨k, rfl⟩ | ⟨k, rfl⟩ | ⟨k, rfl⟩ | ⟨k, rfl⟩
  · -- front: R(o0) and xa_0 against T_A(0) with rotation (1, 1)
    have hJ0 : 0 < Jn m ns := by omega
    obtain ⟨u0, s0, v0, k0⟩ := hdA m ns ds j 0 0 (by omega) (by norm_num) (by norm_num)
    have hr0 : rt0 0 = 1 := by simp [rt0]
    have hr1 : rt1 0 = 1 := by simp [rt1]
    have hv0 : vvH m ns ds j 0 = 2 := rfl
    have hp1 := pt_hd (m := m) (ns := ns) ds j (0 + 1) 0 0 hj (by norm_num) (by omega)
      (by norm_num) (by norm_num)
    rw [u0, s0, v0, k0, hr0, hr1, hv0, pt_zero, hp1]
    obtain ⟨h0, K, hK, hD⟩ := on_A hA 0 0 hJ0 (by norm_num) 1 1 2
    have hVA : VA m ns 0 = o0 * SA m ns 0 := by unfold VA wA; simp
    have ho : (0 : ℝ) < o0 := by unfold o0; norm_num
    obtain ⟨r1, r2⟩ := rlot_eval (UA m ns 0) (SA m ns 0) (VA m ns 0) o0
      (aE (UA m ns 0) (cOf (sig ns ds 0) * VA m ns 0) 1 2)
      (aE (SA m ns 0) (cOf (sig ns ds 0) * VA m ns 0) 1 2) 2 ho hVA
    refine ⟨Or.inr ⟨r1, ?_⟩, Or.inr ⟨h0, sgn_neg hK hD (by linarith)⟩⟩
    rw [r2]
    have hk : cOf (sig ns ds 0) * VA m ns 0 = 0 := by simp [sig, cOf]
    rw [hk, aE_zero]
    have hSB := (hGL.1 0 hJ0).1
    have hSBA := (hGL.1 0 hJ0).2.1
    have hg1 := (J_spec hA).2.1
    have hS2 : 1 / 2 < SA m ns 0 := by linarith
    have hS0 : 0 < SA m ns 0 := by linarith
    apply div_pos _ (by linarith)
    apply mul_pos (mul_pos hS0 ho)
    rw [sub_pos, div_lt_iff₀ hS0]; linarith
  · -- 4k+1: A_k, rotation −+, xa_k and ya_k on
    have hk : k < Jn m ns := by omega
    obtain ⟨u0, s0, v0, k0⟩ := hdA m ns ds j (4 * k + 1) k (by omega) (by omega) (by omega)
    obtain ⟨r0e, r1e⟩ := rt_val (4 * k + 1) 0 (by omega) (by omega)
    have hp := pt_hd (m := m) (ns := ns) ds j (4 * k + 1) k 0 hj (by omega) (by omega)
      (by omega) (by omega)
    have hp' := pt_hd (m := m) (ns := ns) ds j (4 * k + 1 + 1) k 1 hj (by omega) (by omega)
      (by omega) (by omega)
    rw [u0, s0, v0, k0, hp, hp']
    obtain ⟨h0, K, hK, hD⟩ := on_A hA k 0 hk (by norm_num) (rt0 (4 * k + 1))
      (rt1 (4 * k + 1)) (vvH m ns ds j (4 * k + 1))
    obtain ⟨h0', K', hK', hD'⟩ := on_A hA k 1 hk (by norm_num) (rt0 (4 * k + 1))
      (rt1 (4 * k + 1)) (vvH m ns ds j (4 * k + 1))
    obtain ⟨t0, -, t1, -⟩ := ptT_bounds m ns k hm hns
    have e0 : rt0 (4 * k + 1) = -1 := by rw [r0e]; simp [r0of]
    have e1 : rt1 (4 * k + 1) = 1 := by rw [r1e]; simp [r1of]
    refine ⟨Or.inr ⟨h0, sgn_pos hK hD ?_⟩, Or.inr ⟨h0', sgn_neg hK' hD' ?_⟩⟩
    · rw [e0, e1]; linarith
    · rw [e0, e1]; linarith
  · -- 4k+2: A_k, rotation low, ya_k on, yb_k strict (G2a)
    have hk : k < Jn m ns := by omega
    obtain ⟨u0, s0, v0, k0⟩ := hdA m ns ds j (4 * k + 2) k (by omega) (by omega) (by omega)
    obtain ⟨r0e, r1e⟩ := rt_val (4 * k + 2) 1 (by omega) (by omega)
    have hp := pt_hd (m := m) (ns := ns) ds j (4 * k + 2) k 1 hj (by omega) (by omega)
      (by omega) (by omega)
    have hp' := pt_hd (m := m) (ns := ns) ds j (4 * k + 2 + 1) k 2 hj (by omega) (by omega)
      (by omega) (by omega)
    rw [u0, s0, v0, k0, hp, hp']
    obtain ⟨h0, K, hK, hD⟩ := on_A hA k 1 hk (by norm_num) (rt0 (4 * k + 2))
      (rt1 (4 * k + 2)) (vvH m ns ds j (4 * k + 2))
    have e0 : rt0 (4 * k + 2) = -2 := by rw [r0e]; simp [r0of]
    have e1 : rt1 (4 * k + 2) = -2 := by rw [r1e]; simp [r1of]
    refine ⟨Or.inr ⟨h0, sgn_pos hK hD ?_⟩, Or.inl (lifted_rel_gadget hA k hk).1⟩
    rw [e0, e1]; linarith
  · -- 4k+3: B_k, rotation +−, yb_k and xb_k on
    have hk : k < Jn m ns := by omega
    obtain ⟨u0, s0, v0, k0⟩ := hdB m ns ds j (4 * k + 3) k (by omega) (by omega) (by omega)
    obtain ⟨r0e, r1e⟩ := rt_val (4 * k + 3) 2 (by omega) (by omega)
    have hp := pt_hd (m := m) (ns := ns) ds j (4 * k + 3) k 2 hj (by omega) (by omega)
      (by omega) (by omega)
    have hp' := pt_hd (m := m) (ns := ns) ds j (4 * k + 3 + 1) k 3 hj (by omega) (by omega)
      (by omega) (by omega)
    rw [u0, s0, v0, k0, hp, hp']
    obtain ⟨h0, K, hK, hD⟩ := on_B hA k 2 hk (by norm_num) (by norm_num) (rt0 (4 * k + 3))
      (rt1 (4 * k + 3)) (vvH m ns ds j (4 * k + 3))
    obtain ⟨h0', K', hK', hD'⟩ := on_B hA k 3 hk (by norm_num) (by norm_num)
      (rt0 (4 * k + 3)) (rt1 (4 * k + 3)) (vvH m ns ds j (4 * k + 3))
    obtain ⟨-, t3, -, t2⟩ := ptT_bounds m ns k hm hns
    have e0 : rt0 (4 * k + 3) = 1 := by rw [r0e]; simp [r0of]
    have e1 : rt1 (4 * k + 3) = -1 := by rw [r1e]; simp [r1of]
    refine ⟨Or.inr ⟨h0, sgn_pos hK hD ?_⟩, Or.inr ⟨h0', sgn_neg hK' hD' ?_⟩⟩
    · rw [e0, e1]; linarith
    · rw [e0, e1]; linarith
  · -- 4k+4: B_k, rotation low, xb_k on, xa_{k+1} strict (G4)
    have hk : k + 1 < Jn m ns := by omega
    obtain ⟨u0, s0, v0, k0⟩ := hdB m ns ds j (4 * k + 4) k (by omega) (by omega) (by omega)
    obtain ⟨r0e, r1e⟩ := rt_val (4 * k + 4) 3 (by omega) (by omega)
    have hp := pt_hd (m := m) (ns := ns) ds j (4 * k + 4) k 3 hj (by omega) (by omega)
      (by omega) (by omega)
    have hp' := pt_hd (m := m) (ns := ns) ds j (4 * k + 4 + 1) (k + 1) 0 hj (by omega)
      (by omega) (by omega) (by omega)
    rw [u0, s0, v0, k0, hp, hp']
    obtain ⟨h0, K, hK, hD⟩ := on_B hA k 3 (by omega) (by norm_num) (by norm_num)
      (rt0 (4 * k + 4)) (rt1 (4 * k + 4)) (vvH m ns ds j (4 * k + 4))
    have e0 : rt0 (4 * k + 4) = -2 := by rw [r0e]; simp [r0of]
    have e1 : rt1 (4 * k + 4) = -2 := by rw [r1e]; simp [r1of]
    refine ⟨Or.inr ⟨h0, sgn_pos hK hD ?_⟩, Or.inl (lifted_rel_trans hA k hk).1⟩
    rw [e0, e1]; linarith

/-! ### The saving step `B_{j-1} → B_j` (into `xa_j`'s vector) -/

private lemma saving_nest {m ns : ℕ} {ds : ℝ} (hA : Adm m ns ds) (j : ℕ) (hj : j < Jn m ns)
    (hj1 : 1 ≤ j) (a b c a' b' c' : ℝ) :
    NestP (cU m ns j (4 * j)) (cS m ns j (4 * j)) (cV m ns j (4 * j)) a b c
      (cU m ns j (4 * j + 1)) (cS m ns j (4 * j + 1)) (cV m ns j (4 * j + 1)) a' b' c' := by
  obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
  obtain ⟨u0, s0, v0, -⟩ := hdB m ns ds (k + 1) (4 * (k + 1)) k le_rfl (by omega) (by omega)
  obtain ⟨u1, s1, v1, -⟩ := mdB m ns ds (k + 1)
  have hGL := gadget_lines hA
  obtain ⟨-, hSBA, -, -, hUBA⟩ := hGL.1 (k + 1) hj
  obtain ⟨hU', hS'⟩ := hGL.2 k hj
  obtain ⟨-, -, t3, t4, -⟩ := (tight_nest hA).2 k hj
  unfold NestP
  rw [u0, s0, v0, u1, s1, v1]
  exact ⟨Or.inl (by linarith), Or.inl (by linarith), Or.inl t3, Or.inl t4⟩

/-! ### The front for `j = 0`: a scaled copy of `T_B(0)` -/

private def eps0 (m ns j : ℕ) : ℝ := SB m ns j / (2 * UA m ns j)

private lemma eps0_bounds {m ns : ℕ} {ds : ℝ} (hA : Adm m ns ds) (j : ℕ) (hj : j < Jn m ns) :
    0 < eps0 m ns j ∧ eps0 m ns j < 1 ∧ UA m ns j < UB m ns j / eps0 m ns j ∧
      SB m ns j / eps0 m ns j = 2 * UA m ns j := by
  obtain ⟨hg0, hg1, -, -, -, -⟩ := J_spec hA
  obtain ⟨hSB1, hSBA, hSAU, hSBU, -⟩ := (gadget_lines hA).1 j hj
  have hSB : 0 < SB m ns j := by linarith
  have hUA : 0 < UA m ns j := by linarith
  have he0 : 0 < eps0 m ns j := by unfold eps0; positivity
  refine ⟨he0, ?_, ?_, ?_⟩
  · unfold eps0; rw [div_lt_one (by positivity)]; linarith
  · rw [lt_div_iff₀ he0]
    have : UA m ns j * eps0 m ns j = SB m ns j / 2 := by unfold eps0; field_simp
    rw [this]; linarith
  · unfold eps0; field_simp

private lemma front0_pos {m ns : ℕ} {ds : ℝ} (hA : Adm m ns ds) (j : ℕ) (hj : j < Jn m ns) :
    0 < SB m ns j / eps0 m ns j ∧ SB m ns j / eps0 m ns j < UB m ns j / eps0 m ns j ∧
      1 < VB m ns j / eps0 m ns j := by
  obtain ⟨he0, he1, -, -⟩ := eps0_bounds hA j hj
  obtain ⟨hg0, hg1, -, -, -, -⟩ := J_spec hA
  obtain ⟨hSB1, hSBA, hSAU, hSBU, -⟩ := (gadget_lines hA).1 j hj
  have hVB : 1 < VB m ns j := (cw_bound hA j hj).2.2.2.2.2.1
  have hSB : 0 < SB m ns j := by linarith
  refine ⟨div_pos hSB he0, div_lt_div_of_pos_right hSBU he0, ?_⟩
  have := le_div_self (by linarith : (0 : ℝ) ≤ VB m ns j) he0 he1.le
  linarith

private lemma front0_nest {m ns : ℕ} {ds : ℝ} (hA : Adm m ns ds) (j : ℕ) (hj : j < Jn m ns)
    (a b c : ℝ) :
    NestP (UB m ns j / eps0 m ns j) (SB m ns j / eps0 m ns j) (VB m ns j / eps0 m ns j) a b c
      (UB m ns j) (SB m ns j) (VB m ns j) a b c := by
  obtain ⟨he0, he1, -, -⟩ := eps0_bounds hA j hj
  obtain ⟨hg0, hg1, -, -, -, -⟩ := J_spec hA
  obtain ⟨hSB1, hSBA, hSAU, hSBU, -⟩ := (gadget_lines hA).1 j hj
  have hSB : 0 < SB m ns j := by linarith
  have hUB : 0 < UB m ns j := by linarith
  unfold NestP
  have h1 : UB m ns j < UB m ns j / eps0 m ns j := by
    rw [lt_div_iff₀ he0]; nlinarith
  have h2 : SB m ns j < SB m ns j / eps0 m ns j := by
    rw [lt_div_iff₀ he0]; nlinarith
  refine ⟨Or.inl h1, Or.inl h2,
    Or.inr ⟨by ring, by linarith⟩, Or.inr ⟨by ring, by linarith⟩⟩

private lemma gpt_c (m ns : ℕ) (ds : ℝ) (k τ : ℕ) :
    gpt m ns ds k τ 0 = (1 - sig ns ds k) *
        (1 - hLift (sig ns ds k) (ptL m ns k τ) (ptV m ns k τ) /
          (1 + hLift (sig ns ds k) (ptL m ns k τ) (ptV m ns k τ))) * (1 - ptT m ns k τ) ∧
    gpt m ns ds k τ 1 = (1 - sig ns ds k) *
        (1 - hLift (sig ns ds k) (ptL m ns k τ) (ptV m ns k τ) /
          (1 + hLift (sig ns ds k) (ptL m ns k τ) (ptV m ns k τ))) * ptT m ns k τ ∧
    gpt m ns ds k τ 3 = sig ns ds k := by
  unfold gpt liftPt
  refine ⟨rfl, rfl, rfl⟩

/-- `R(o_0)` strictly above and `xa_0` strictly below the scaled front state. -/
private lemma front0_rel {m ns : ℕ} {ds : ℝ} (hA : Adm m ns ds) (hj : 0 < Jn m ns)
    (a b c : ℝ) :
    RelP (UB m ns 0 / eps0 m ns 0) (SB m ns 0 / eps0 m ns 0) (VB m ns 0 / eps0 m ns 0) a b c
      (Rlot o0) (gpt m ns ds 0 0) := by
  have hm := hA.1
  have hns := ns_pos hA
  obtain ⟨he0, he1, hUe, hSe⟩ := eps0_bounds hA 0 hj
  obtain ⟨hg0, hg1, -, -, -, -⟩ := J_spec hA
  obtain ⟨hSB1, hSBA, hSAU, hSBU, -⟩ := (gadget_lines hA).1 0 hj
  have hSB : 0 < SB m ns 0 := by linarith
  unfold RelP
  refine ⟨Or.inl ?_, Or.inl ?_⟩
  · have hrho := ((rho_bounds hA).1 0 hj).1
    have hH0 : Hh m ns 0 = 4 := by simp [Hh]
    rw [hH0] at hrho
    have hr1 : 1 < rho m ns 0 := by
      have : 0 < gP m ns / (2 * 4) := by positivity
      linarith
    have hVB : VB m ns 0 = o0 * rho m ns 0 * SB m ns 0 := by
      unfold VB wB wA; simp
    have hgap : 0 < VB m ns 0 - o0 * SB m ns 0 := by
      rw [hVB]; unfold o0; nlinarith
    simp only [fval, Rlot, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
      Matrix.head_cons]
    have e : -(UB m ns 0 / eps0 m ns 0) * 0 - SB m ns 0 / eps0 m ns 0 * (o0 / (1 + o0)) + 0 +
        VB m ns 0 / eps0 m ns 0 * (1 / (1 + o0)) =
        (VB m ns 0 - o0 * SB m ns 0) / (eps0 m ns 0 * (1 + o0)) := by
      unfold o0; field_simp; ring
    rw [e]
    apply div_pos hgap
    unfold o0; positivity
  · have hon := (on_A hA 0 0 hj (by norm_num) 0 0 0).1
    obtain ⟨c0, c1, c3⟩ := gpt_c m ns ds 0 0
    have hs : sig ns ds 0 = 0 := by simp [sig]
    have hH := (cw_bound hA 0 hj).2.2.2.2.2.2 0 (by norm_num)
    rw [hs] at hH c0 c1 c3
    generalize hLift 0 (ptL m ns 0 0) (ptV m ns 0 0) = H at hH c0 c1 c3
    have hfac : 0 < 1 - H / (1 + H) := by
      rw [sub_pos, div_lt_one (by linarith)]; linarith
    obtain ⟨t0, -, -, -⟩ := ptT_bounds m ns 0 hm hns
    have tpos : 0 ≤ ptT m ns 0 0 := by
      obtain ⟨hd0, hd5, hu0, hu1⟩ := (class_trans m ns 0 hm hns).1
      simp only [ptT, if_true]
      unfold fa' fa; nlinarith
    have hq0 : 0 < gpt m ns ds 0 0 0 := by
      rw [c0]; apply mul_pos (by nlinarith) (by linarith)
    have hq1 : 0 ≤ gpt m ns ds 0 0 1 := by
      rw [c1]; apply mul_nonneg (by nlinarith) tpos
    unfold fval at hon ⊢
    rw [c3] at hon ⊢
    have hU' : 0 < UB m ns 0 / eps0 m ns 0 - UA m ns 0 := by linarith
    have hS' : 0 < SB m ns 0 / eps0 m ns 0 - SA m ns 0 := by rw [hSe]; linarith
    nlinarith [mul_pos hU' hq0, mul_nonneg hS'.le hq1]

/-! ### The assembled direction data -/

private def FU (m ns j i : ℕ) : ℝ :=
  if j = 0 ∧ i = 0 then UB m ns 0 / eps0 m ns 0 else cU m ns j i
private def FS (m ns j i : ℕ) : ℝ :=
  if j = 0 ∧ i = 0 then SB m ns 0 / eps0 m ns 0 else cS m ns j i
private def FV (m ns j i : ℕ) : ℝ :=
  if j = 0 ∧ i = 0 then VB m ns 0 / eps0 m ns 0 else cV m ns j i
private def Fa (m ns : ℕ) (ds η q : ℝ) (j i : ℕ) : ℝ :=
  if j = 0 ∧ i = 0 then tA m ns ds j η q 1 else if i ≤ 4 * j then qA m ns ds j i
  else tA m ns ds j η q i
private def Fb (m ns : ℕ) (ds η q : ℝ) (j i : ℕ) : ℝ :=
  if j = 0 ∧ i = 0 then tB m ns ds j η q 1 else if i ≤ 4 * j then qB m ns ds j i
  else tB m ns ds j η q i
private def Fc (m ns : ℕ) (ds η q : ℝ) (j i : ℕ) : ℝ :=
  if j = 0 ∧ i = 0 then vt j q 1 else if i ≤ 4 * j then vvH m ns ds j i
  else vt j q i

private lemma F_front (m ns : ℕ) (ds η q : ℝ) (j i : ℕ) (h : j = 0 ∧ i = 0) :
    FU m ns j i = UB m ns 0 / eps0 m ns 0 ∧ FS m ns j i = SB m ns 0 / eps0 m ns 0 ∧
    FV m ns j i = VB m ns 0 / eps0 m ns 0 ∧ Fa m ns ds η q j i = tA m ns ds j η q 1 ∧
    Fb m ns ds η q j i = tB m ns ds j η q 1 ∧ Fc m ns ds η q j i = vt j q 1 := by
  simp only [FU, FS, FV, Fa, Fb, Fc, if_pos h, and_self]

private lemma F_hd (m ns : ℕ) (ds η q : ℝ) (j i : ℕ) (h : ¬ (j = 0 ∧ i = 0)) (hi : i ≤ 4 * j) :
    FU m ns j i = cU m ns j i ∧ FS m ns j i = cS m ns j i ∧ FV m ns j i = cV m ns j i ∧
    Fa m ns ds η q j i = qA m ns ds j i ∧ Fb m ns ds η q j i = qB m ns ds j i ∧
    Fc m ns ds η q j i = vvH m ns ds j i := by
  simp only [FU, FS, FV, Fa, Fb, Fc, if_neg h, if_pos hi, and_self]

private lemma F_tl (m ns : ℕ) (ds η q : ℝ) (j i : ℕ) (hi : 4 * j + 1 ≤ i) :
    FU m ns j i = cU m ns j i ∧ FS m ns j i = cS m ns j i ∧ FV m ns j i = cV m ns j i ∧
    Fa m ns ds η q j i = tA m ns ds j η q i ∧ Fb m ns ds η q j i = tB m ns ds j η q i ∧
    Fc m ns ds η q j i = vt j q i := by
  have h : ¬ (j = 0 ∧ i = 0) := by omega
  have h' : ¬ i ≤ 4 * j := by omega
  simp only [FU, FS, FV, Fa, Fb, Fc, if_neg h, if_neg h', and_self]

end

set_option maxHeartbeats 1600000 in
/-- Deleting `ya_j` (position `4j+2`) leaves a ranking with a chain. -/
theorem del_ya {m ns : ℕ} {ds : ℝ} (hA : Adm m ns ds) (j : ℕ) (hj : j < Jn m ns) :
    ∃ W, IsChainFn (4 * Jn m ns + 1) (fun i => Tpt m ns ds (skipIdx (4 * j + 2) i)) W := by
  obtain ⟨L, D, hL0, hL1, hD0, hfac⟩ := tail_setup hA j hj
  obtain ⟨q, hq⟩ : ∃ q : ℝ, q = L / 2 := ⟨_, rfl⟩
  obtain ⟨η, hη⟩ : ∃ η : ℝ, η = q ^ (2 * Jn m ns) * L / (4 * D) := ⟨_, rfl⟩
  have hq0 : 0 < q := by rw [hq]; linarith
  have hη0 : 0 < η := by rw [hη]; positivity
  have hJ0 : 0 < Jn m ns := by omega
  refine strictify (4 * Jn m ns + 1) _ (FU m ns j) (FS m ns j) (FV m ns j)
    (Fa m ns ds η q j) (Fb m ns ds η q j) (Fc m ns ds η q j) ?_ ?_ ?_
  · -- coordinates
    intro i hi
    by_cases h0 : j = 0 ∧ i = 0
    · obtain ⟨e1, e2, e3, -⟩ := F_front m ns ds η q j i h0
      rw [e1, e2, e3]
      exact front0_pos hA 0 hJ0
    · have e : FU m ns j i = cU m ns j i ∧ FS m ns j i = cS m ns j i ∧
          FV m ns j i = cV m ns j i := by
        simp only [FU, FS, FV, if_neg h0, and_self]
      rw [e.1, e.2.1, e.2.2]
      obtain ⟨a, b, c, -⟩ := c_pos hA j hj i (by omega)
      exact ⟨a, b, c⟩
  · -- nesting
    intro i hi
    show NestP (FU m ns j i) (FS m ns j i) (FV m ns j i) (Fa m ns ds η q j i)
      (Fb m ns ds η q j i) (Fc m ns ds η q j i) (FU m ns j (i + 1)) (FS m ns j (i + 1))
      (FV m ns j (i + 1)) (Fa m ns ds η q j (i + 1)) (Fb m ns ds η q j (i + 1))
      (Fc m ns ds η q j (i + 1))
    by_cases h0 : j = 0 ∧ i = 0
    · obtain ⟨rfl, rfl⟩ := h0
      obtain ⟨e1, e2, e3, e4, e5, e6⟩ := F_front m ns ds η q 0 0 ⟨rfl, rfl⟩
      obtain ⟨f1, f2, f3, f4, f5, f6⟩ := F_tl m ns ds η q 0 (0 + 1) (by omega)
      obtain ⟨g1, g2, g3, -⟩ := mdB m ns ds 0
      rw [e1, e2, e3, e4, e5, e6, f1, f2, f3, f4, f5, f6]
      have g1' : cU m ns 0 (0 + 1) = UB m ns 0 := g1
      have g2' : cS m ns 0 (0 + 1) = SB m ns 0 := g2
      have g3' : cV m ns 0 (0 + 1) = VB m ns 0 := g3
      rw [g1', g2', g3']
      exact front0_nest hA 0 hJ0 _ _ _
    by_cases h1 : i + 1 ≤ 4 * j
    · obtain ⟨e1, e2, e3, e4, e5, e6⟩ := F_hd m ns ds η q j i h0 (by omega)
      obtain ⟨f1, f2, f3, f4, f5, f6⟩ := F_hd m ns ds η q j (i + 1) (by omega) h1
      rw [e1, e2, e3, e4, e5, e6, f1, f2, f3, f4, f5, f6]
      exact head_nest hA j hj i h1
    by_cases h2 : i = 4 * j
    · obtain ⟨e1, e2, e3, -⟩ := F_hd m ns ds η q j i h0 (by omega)
      obtain ⟨f1, f2, f3, -⟩ := F_tl m ns ds η q j (i + 1) (by omega)
      rw [e1, e2, e3, f1, f2, f3, h2]
      exact saving_nest hA j hj (by omega) _ _ _ _ _ _
    · obtain ⟨e1, e2, e3, e4, e5, e6⟩ := F_tl m ns ds η q j i (by omega)
      obtain ⟨f1, f2, f3, f4, f5, f6⟩ := F_tl m ns ds η q j (i + 1) (by omega)
      rw [e1, e2, e3, e4, e5, e6, f1, f2, f3, f4, f5, f6]
      exact tail_nest hA j hj L D q η hL0 hL1 hD0 hq hη hfac i (by omega) hi
  · -- relations
    intro i hi
    show RelP (FU m ns j i) (FS m ns j i) (FV m ns j i) (Fa m ns ds η q j i)
      (Fb m ns ds η q j i) (Fc m ns ds η q j i) (Tpt m ns ds (skipIdx (4 * j + 2) i))
      (Tpt m ns ds (skipIdx (4 * j + 2) (i + 1)))
    by_cases h0 : j = 0 ∧ i = 0
    · obtain ⟨rfl, rfl⟩ := h0
      obtain ⟨e1, e2, e3, e4, e5, e6⟩ := F_front m ns ds η q 0 0 ⟨rfl, rfl⟩
      rw [e1, e2, e3, e4, e5, e6, pt_zero,
        pt_hd (m := m) (ns := ns) ds 0 (0 + 1) 0 0 hj (by norm_num) (by norm_num)
          (by norm_num) (by norm_num)]
      exact front0_rel hA hJ0 _ _ _
    by_cases h1 : i ≤ 4 * j
    · obtain ⟨e1, e2, e3, e4, e5, e6⟩ := F_hd m ns ds η q j i h0 h1
      rw [e1, e2, e3, e4, e5, e6]
      exact head_rel hA j hj i h1 (by omega)
    · obtain ⟨e1, e2, e3, e4, e5, e6⟩ := F_tl m ns ds η q j i (by omega)
      rw [e1, e2, e3, e4, e5, e6]
      exact tail_rel hA j hj L D q η hL0 hL1 hD0 hq hη hη0 hfac i (by omega) hi

end Q2CL
