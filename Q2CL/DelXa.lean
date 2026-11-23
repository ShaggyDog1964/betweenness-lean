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
import Q2CL.RhoBounds
import Q2CL.WEnvelope

namespace Q2CL

open K4

noncomputable section

/-! ### Generic shapes of the `strictify` conditions -/

private def NestP (U S V a b c U' S' V' a' b' c' : ℝ) : Prop :=
  (U' < U ∨ (U' = U ∧ a' ≤ a)) ∧ (S' < S ∨ (S' = S ∧ b' ≤ b)) ∧
  (U' * V < V' * U ∨ (U' * V = V' * U ∧ a' - a ≤ c' - c)) ∧
  (S' * V < V' * S ∨ (S' * V = V' * S ∧ b' - b ≤ c' - c))

private def RelP (U S V a b c : ℝ) (p p' : Lot 4) : Prop :=
  (0 < fval U S V p ∨ (fval U S V p = 0 ∧ 0 < -(U * a) * p 0 - S * b * p 1 + V * c * p 3)) ∧
  (fval U S V p' < 0 ∨ (fval U S V p' = 0 ∧ -(U * a) * p' 0 - S * b * p' 1 + V * c * p' 3 < 0))

/-! ### Post-saving scheme (as in the `R(o_0)` deletion) -/

private def sU (m ns i : ℕ) : ℝ := if i % 4 < 2 then UA m ns (i / 4) else UB m ns (i / 4)
private def sS (m ns i : ℕ) : ℝ := if i % 4 < 2 then SA m ns (i / 4) else SB m ns (i / 4)
private def sV (m ns i : ℕ) : ℝ := if i % 4 < 2 then VA m ns (i / 4) else VB m ns (i / 4)
private def sK (m ns : ℕ) (ds : ℝ) (i : ℕ) : ℝ := cOf (sig ns ds (i / 4)) * sV m ns i
private def r0f (i : ℕ) : ℝ := if i % 4 = 2 then 1 else -1
private def r1f (i : ℕ) : ℝ := if i % 4 = 0 then 1 else -1
private def vf (q : ℝ) (i : ℕ) : ℝ := -q ^ (i / 2)
private def aE (U K r v : ℝ) : ℝ := ((1 + K) * r + ((U - K) / (1 + K) + 1) * K * v) / U

private lemma st_A (m ns i j : ℕ) (h1 : i / 4 = j) (h2 : i % 4 < 2) :
    sU m ns i = UA m ns j ∧ sS m ns i = SA m ns j ∧ sV m ns i = VA m ns j := by
  subst h1; simp [sU, sS, sV, h2]

private lemma st_B (m ns i j : ℕ) (h1 : i / 4 = j) (h2 : 2 ≤ i % 4) :
    sU m ns i = UB m ns j ∧ sS m ns i = SB m ns j ∧ sV m ns i = VB m ns j := by
  subst h1
  have : ¬ i % 4 < 2 := by omega
  simp [sU, sS, sV, this]

private lemma vf_eq (q : ℝ) (i k : ℕ) (h : i / 2 = k) : vf q i = -q ^ k := by
  unfold vf; rw [h]

private lemma aE_sub (U K r v : ℝ) (hU : 0 < U) (hK : 0 ≤ K) :
    aE U K r v - v = (1 + K) / U * r - (U - K) / ((1 + K) * U) * v := by
  have h1 : (1 + K) ≠ 0 := by positivity
  unfold aE; field_simp; ring

private lemma aE_mono (U K r r' v : ℝ) (hU : 0 < U) (hK : 0 ≤ K) (h : r' ≤ r) :
    aE U K r' v ≤ aE U K r v := by
  unfold aE
  apply div_le_div_of_nonneg_right _ hU.le
  nlinarith

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

private lemma on_pt (U S V s t r0 r1 v : ℝ) (hs0 : 0 ≤ s) (hs : s < 1) (hV : 0 < V)
    (hU : 0 < U) (hS : 0 < S) (hH : 0 < hLift s (U * (1 - t) + S * t) V) :
    fval U S V (liftPt s t (U * (1 - t) + S * t) V) = 0 ∧
    (r0 * (1 - t) + r1 * t < 0 →
      0 < -(U * aE U (cOf s * V) r0 v) * liftPt s t (U * (1 - t) + S * t) V 0 -
        S * aE S (cOf s * V) r1 v * liftPt s t (U * (1 - t) + S * t) V 1 +
        V * v * liftPt s t (U * (1 - t) + S * t) V 3) ∧
    (0 < r0 * (1 - t) + r1 * t →
      -(U * aE U (cOf s * V) r0 v) * liftPt s t (U * (1 - t) + S * t) V 0 -
        S * aE S (cOf s * V) r1 v * liftPt s t (U * (1 - t) + S * t) V 1 +
        V * v * liftPt s t (U * (1 - t) + S * t) V 3 < 0) := by
  have hc : 0 ≤ cOf s := div_nonneg hs0 (by linarith)
  have hk : 0 < 1 + cOf s * V := by have := mul_nonneg hc hV.le; linarith
  have hH' : 1 + hLift s (U * (1 - t) + S * t) V ≠ 0 := by linarith
  refine ⟨lift_on U S V s t hs hk.ne' hH', ?_, ?_⟩
  all_goals
    have e := relift_dval U S V s t r0 r1 v hs hk hU.ne' hS.ne' hH'
    unfold aE
    rw [e]
    have hpos : 0 < (1 - s) * (1 + cOf s * V) / (1 + hLift s (U * (1 - t) + S * t) V) :=
      div_pos (mul_pos (by linarith) hk) (by linarith)
    intro h
    nlinarith

private lemma stA_all (m ns : ℕ) (ds : ℝ) (i j : ℕ) (h1 : i / 4 = j) (h2 : i % 4 < 2) :
    sU m ns i = UA m ns j ∧ sS m ns i = SA m ns j ∧ sV m ns i = VA m ns j ∧
      sK m ns ds i = cOf (sig ns ds j) * VA m ns j := by
  obtain ⟨e1, e2, e3⟩ := st_A m ns i j h1 h2
  refine ⟨e1, e2, e3, ?_⟩
  unfold sK; rw [e3, h1]

private lemma stB_all (m ns : ℕ) (ds : ℝ) (i j : ℕ) (h1 : i / 4 = j) (h2 : 2 ≤ i % 4) :
    sU m ns i = UB m ns j ∧ sS m ns i = SB m ns j ∧ sV m ns i = VB m ns j ∧
      sK m ns ds i = cOf (sig ns ds j) * VB m ns j := by
  obtain ⟨e1, e2, e3⟩ := st_B m ns i j h1 h2
  refine ⟨e1, e2, e3, ?_⟩
  unfold sK; rw [e3, h1]

/-- Entry `i + 1` of `T` (gadget position `i`). -/
private lemma pt_eq {m ns : ℕ} {ds : ℝ} (i j τ : ℕ) (hi : i < 4 * Jn m ns) (h1 : i / 4 = j)
    (h2 : i % 4 = τ) : Tpt m ns ds (i + 1) = gpt m ns ds j τ := by
  unfold Tpt
  rw [if_neg (by omega), if_neg (by omega)]
  rw [show i + 1 - 1 = i by omega, h1, h2]

private lemma pt_last {m ns : ℕ} {ds : ℝ} :
    Tpt m ns ds (4 * Jn m ns + 1) = Rlot (o1 m ns) := by
  unfold Tpt
  rw [if_neg (by omega), if_pos rfl]

private lemma ns_pos {m ns : ℕ} {ds : ℝ} (hA : Adm m ns ds) : 1 ≤ ns := by
  rcases Nat.eq_zero_or_pos ns with h | h
  · have := hA.2.1; subst h; simp at this
  · exact h

private lemma t_bounds (m ns j : ℕ) (hm : 2 ≤ m) (hns : 1 ≤ ns) :
    ptT m ns j 0 < 1 / 2 ∧ 1 / 2 < ptT m ns j 1 ∧ 1 / 2 < ptT m ns j 2 ∧
      ptT m ns j 3 < 1 / 2 := by
  obtain ⟨h1, h2, h3, h4⟩ := (class_trans m ns j hm hns).1
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [ptT] <;> norm_num <;> simp only [fa', fa, fb', fb] <;>
    linarith

private lemma on_gadget {m ns : ℕ} {ds : ℝ} (hA : Adm m ns ds) (j τ : ℕ) (hj : j < Jn m ns)
    (hτ : τ < 4) (U S V : ℝ) (hU : U = if τ < 2 then UA m ns j else UB m ns j)
    (hS : S = if τ < 2 then SA m ns j else SB m ns j)
    (hV : V = if τ < 2 then VA m ns j else VB m ns j) (r0 r1 v : ℝ) :
    fval U S V (gpt m ns ds j τ) = 0 ∧
    (r0 * (1 - ptT m ns j τ) + r1 * ptT m ns j τ < 0 →
      0 < -(U * aE U (cOf (sig ns ds j) * V) r0 v) * gpt m ns ds j τ 0 -
        S * aE S (cOf (sig ns ds j) * V) r1 v * gpt m ns ds j τ 1 +
        V * v * gpt m ns ds j τ 3) ∧
    (0 < r0 * (1 - ptT m ns j τ) + r1 * ptT m ns j τ →
      -(U * aE U (cOf (sig ns ds j) * V) r0 v) * gpt m ns ds j τ 0 -
        S * aE S (cOf (sig ns ds j) * V) r1 v * gpt m ns ds j τ 1 +
        V * v * gpt m ns ds j τ 3 < 0) := by
  have hm : 2 ≤ m := hA.1
  obtain ⟨hg0, hg1, -, -, -, -⟩ := J_spec hA
  obtain ⟨hs0, hs1, -, -, hVA, hVB, hH⟩ := cw_bound hA j hj
  obtain ⟨hSB1, hSBA, hSAU, hSBU, -⟩ := (gadget_lines hA).1 j hj
  have hN := normalization m ns j hm
  have hL : ptL m ns j τ = U * (1 - ptT m ns j τ) + S * ptT m ns j τ := by
    by_cases h : τ < 2
    · rw [hU, hS, if_pos h, if_pos h]; exact hN.2.2.1 τ h
    · rw [hU, hS, if_neg h, if_neg h]; exact hN.2.2.2 τ (by omega) hτ
  have hVe : ptV m ns j τ = V := by rw [hV]; rfl
  have e : gpt m ns ds j τ =
      liftPt (sig ns ds j) (ptT m ns j τ) (U * (1 - ptT m ns j τ) + S * ptT m ns j τ) V := by
    unfold gpt; rw [hL, hVe]
  have hpos : 0 < U ∧ 0 < S ∧ 0 < V := by
    by_cases h : τ < 2
    · rw [hU, hS, hV, if_pos h, if_pos h, if_pos h]
      refine ⟨by linarith, by linarith, by linarith⟩
    · rw [hU, hS, hV, if_neg h, if_neg h, if_neg h]
      refine ⟨by linarith, by linarith, by linarith⟩
  rw [e]
  have hH' := hH τ hτ
  rw [hL, hVe] at hH'
  exact on_pt U S V _ _ r0 r1 v hs0 (by linarith) hpos.2.2 hpos.1 hpos.2.1 hH'

private lemma rlot_rel (U S V o a b c : ℝ) (ho : 0 < o) (hS : 0 < S) (hV : V = o * S)
    (hcb : c - b < 0) :
    fval U S V (Rlot o) = 0 ∧ -(U * a) * Rlot o 0 - S * b * Rlot o 1 + V * c * Rlot o 3 < 0 := by
  subst hV
  have ho1 : (0 : ℝ) < 1 + o := by linarith
  simp only [fval, Rlot, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Matrix.cons_val_three]
  constructor
  · field_simp; ring
  · have e : -(U * a) * 0 - S * b * (o / (1 + o)) + o * S * c * (1 / (1 + o)) =
        S * o * (c - b) / (1 + o) := by field_simp; ring
    rw [e]
    exact div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg (mul_pos hS ho) hcb) ho1

private lemma hst_lem {m ns : ℕ} {ds : ℝ} (hA : Adm m ns ds) :
    ∀ i, i < 4 * Jn m ns → 0 < sS m ns i ∧ sS m ns i < sU m ns i ∧ 1 < sV m ns i ∧
      0 ≤ sK m ns ds i ∧ sK m ns ds i < sS m ns i := by
  have hGL := gadget_lines hA
  obtain ⟨hg0, hg1, -, -, -, -⟩ := J_spec hA
  intro i hi
  have hj : i / 4 < Jn m ns := by omega
  obtain ⟨hs0, hs1, hcA, hcB, hVA, hVB, -⟩ := cw_bound hA (i / 4) hj
  obtain ⟨hSB1, hSBA, hSAU, hSBU, -⟩ := hGL.1 (i / 4) hj
  have hc : 0 ≤ cOf (sig ns ds (i / 4)) := div_nonneg hs0 (by linarith)
  by_cases h : i % 4 < 2
  · obtain ⟨e1, e2, e3, e4⟩ := stA_all m ns ds i (i / 4) rfl h
    rw [e1, e2, e3, e4]
    have eK : cOf (sig ns ds (i / 4)) * VA m ns (i / 4) =
        cOf (sig ns ds (i / 4)) * wA m ns (i / 4) * SA m ns (i / 4) := by unfold VA; ring
    have hSA : 0 < SA m ns (i / 4) := by linarith
    have := mul_le_mul_of_nonneg_right hcA hSA.le
    refine ⟨hSA, hSAU, hVA, mul_nonneg hc (by linarith), ?_⟩
    rw [eK]; linarith
  · obtain ⟨e1, e2, e3, e4⟩ := stB_all m ns ds i (i / 4) rfl (by omega)
    rw [e1, e2, e3, e4]
    have eK : cOf (sig ns ds (i / 4)) * VB m ns (i / 4) =
        cOf (sig ns ds (i / 4)) * wB m ns (i / 4) * SB m ns (i / 4) := by unfold VB; ring
    have hSB : 0 < SB m ns (i / 4) := by linarith
    have := mul_le_mul_of_nonneg_right hcB hSB.le
    refine ⟨hSB, hSBU, hVB, mul_nonneg hc (by linarith), ?_⟩
    rw [eK]; linarith

private lemma hlam_lem {m ns : ℕ} {ds : ℝ} (hA : Adm m ns ds) :
    ∀ i, i < 4 * Jn m ns →
      0 < (sU m ns i - sK m ns ds i) / ((1 + sK m ns ds i) * sU m ns i) ∧
      (sU m ns i - sK m ns ds i) / ((1 + sK m ns ds i) * sU m ns i) ≤ 1 ∧
      0 < (sS m ns i - sK m ns ds i) / ((1 + sK m ns ds i) * sS m ns i) ∧
      (sS m ns i - sK m ns ds i) / ((1 + sK m ns ds i) * sS m ns i) ≤ 1 := by
  intro i hi
  obtain ⟨hS0, hSU, -, hK0, hKS⟩ := hst_lem hA i hi
  have hU0 : 0 < sU m ns i := by linarith
  have d1 : 0 < (1 + sK m ns ds i) * sU m ns i := by positivity
  have d2 : 0 < (1 + sK m ns ds i) * sS m ns i := by positivity
  refine ⟨div_pos (by linarith) d1, (div_le_one d1).2 (by nlinarith),
    div_pos (by linarith) d2, (div_le_one d2).2 (by nlinarith)⟩

private lemma hfac_lem {m ns : ℕ} {ds : ℝ} (hA : Adm m ns ds) (L D : ℝ)
    (hL : ∀ i, i < 4 * Jn m ns →
      L ≤ min ((sU m ns i - sK m ns ds i) / ((1 + sK m ns ds i) * sU m ns i))
        ((sS m ns i - sK m ns ds i) / ((1 + sK m ns ds i) * sS m ns i)))
    (hD : ∀ i, i < 4 * Jn m ns →
      (1 + sK m ns ds i) / sU m ns i + (1 + sK m ns ds i) / sS m ns i ≤ D) :
    ∀ i, i < 4 * Jn m ns →
      L ≤ (sU m ns i - sK m ns ds i) / ((1 + sK m ns ds i) * sU m ns i) ∧
      L ≤ (sS m ns i - sK m ns ds i) / ((1 + sK m ns ds i) * sS m ns i) ∧
      (1 + sK m ns ds i) / sU m ns i ≤ D ∧ (1 + sK m ns ds i) / sS m ns i ≤ D ∧
      0 ≤ (1 + sK m ns ds i) / sU m ns i ∧ 0 ≤ (1 + sK m ns ds i) / sS m ns i := by
  intro i hi
  obtain ⟨hS0, hSU, -, hK0, -⟩ := hst_lem hA i hi
  have h1 := hL i hi
  have h2 := hD i hi
  have p1 : 0 ≤ (1 + sK m ns ds i) / sU m ns i := div_nonneg (by linarith) (by linarith)
  have p2 : 0 ≤ (1 + sK m ns ds i) / sS m ns i := div_nonneg (by linarith) (by linarith)
  exact ⟨h1.trans (min_le_left _ _), h1.trans (min_le_right _ _), by linarith,
    by linarith, p1, p2⟩

set_option maxHeartbeats 1600000 in
/-- Nesting of the post-saving scheme (every index of the `R(o_0)`-deletion chain). -/
private lemma post_nest {m ns : ℕ} {ds : ℝ} (hA : Adm m ns ds) (L D q η : ℝ) (hL0 : 0 < L)
    (hL1 : L ≤ 1)
    (hL : ∀ i, i < 4 * Jn m ns →
      L ≤ min ((sU m ns i - sK m ns ds i) / ((1 + sK m ns ds i) * sU m ns i))
        ((sS m ns i - sK m ns ds i) / ((1 + sK m ns ds i) * sS m ns i)))
    (hD0 : 0 < D) (hD : ∀ i, i < 4 * Jn m ns →
      (1 + sK m ns ds i) / sU m ns i + (1 + sK m ns ds i) / sS m ns i ≤ D)
    (hq : q = L / 2) (hη : η = q ^ (2 * Jn m ns) * L / (4 * D)) (i : ℕ)
    (hi : i + 2 < 4 * Jn m ns + 1) :
    NestP (sU m ns i) (sS m ns i) (sV m ns i) (aE (sU m ns i) (sK m ns ds i) (η * r0f i) (vf q i))
      (aE (sS m ns i) (sK m ns ds i) (η * r1f i) (vf q i)) (vf q i)
      (sU m ns (i + 1)) (sS m ns (i + 1)) (sV m ns (i + 1))
      (aE (sU m ns (i + 1)) (sK m ns ds (i + 1)) (η * r0f (i + 1)) (vf q (i + 1)))
      (aE (sS m ns (i + 1)) (sK m ns ds (i + 1)) (η * r1f (i + 1)) (vf q (i + 1)))
      (vf q (i + 1)) := by
  have hGL := gadget_lines hA
  have hTN := tight_nest hA
  have hst := hst_lem hA
  have hlam := hlam_lem hA
  have hfac := hfac_lem hA L D hL hD
  have hq0 : 0 < q := by rw [hq]; linarith
  have hη0 : 0 < η := by rw [hη]; positivity
  unfold NestP
  have hi1 : i + 1 < 4 * Jn m ns := by omega
  have hi0 : i < 4 * Jn m ns := by omega
  have hj : i / 4 < Jn m ns := by omega
  obtain ⟨hS0, hSU, hV1, hK0, hKS⟩ := hst i hi0
  obtain ⟨hS0', hSU', hV1', hK0', hKS'⟩ := hst (i + 1) hi1
  obtain ⟨hLU, hLS, hDU, hDS, hPU, hPS⟩ := hfac i hi0
  obtain ⟨hLU', hLS', hDU', hDS', hPU', hPS'⟩ := hfac (i + 1) hi1
  obtain ⟨-, hlU1, -, hlS1⟩ := hlam i hi0
  obtain ⟨-, hlU1', -, hlS1'⟩ := hlam (i + 1) hi1
  have hU0 : 0 < sU m ns i := by linarith
  have hU0' : 0 < sU m ns (i + 1) := by linarith
  rcases (by omega : i % 4 = 0 ∨ i % 4 = 1 ∨ i % 4 = 2 ∨ i % 4 = 3) with h | h | h | h
  · -- xa_j → ya_j : same state A_j
    have hv : vf q (i + 1) = vf q i := by unfold vf; rw [show (i + 1) / 2 = i / 2 by omega]
    have r0a : r0f i = -1 := by simp [r0f, h]
    have r0b : r0f (i + 1) = -1 := by simp [r0f, show (i + 1) % 4 = 1 by omega]
    have r1a : r1f i = 1 := by simp [r1f, h]
    have r1b : r1f (i + 1) = -1 := by simp [r1f, show (i + 1) % 4 = 1 by omega]
    obtain ⟨e1, e2, e3, e4⟩ := stA_all m ns ds i (i / 4) rfl (by omega)
    obtain ⟨f1, f2, f3, f4⟩ := stA_all m ns ds (i + 1) (i / 4) (by omega) (by omega)
    simp only [e1, e2, e3, e4] at hS0 hK0 ⊢
    rw [hv, r0a, r0b, r1a, r1b, f1, f2, f3, f4]
    have hm : aE (SA m ns (i / 4)) (cOf (sig ns ds (i / 4)) * VA m ns (i / 4)) (η * -1)
        (vf q i) ≤ aE (SA m ns (i / 4)) (cOf (sig ns ds (i / 4)) * VA m ns (i / 4)) (η * 1)
        (vf q i) := aE_mono _ _ _ _ _ hS0 hK0 (by linarith)
    refine ⟨Or.inr ⟨rfl, le_rfl⟩, Or.inr ⟨rfl, hm⟩, Or.inr ⟨mul_comm _ _, by simp⟩,
      Or.inr ⟨mul_comm _ _, by linarith⟩⟩
  · -- ya_j → yb_j : A_j → B_j, equality in (U, V)
    have hv : vf q i = -q ^ (i / 2) := vf_eq q i _ rfl
    have hv' : vf q (i + 1) = -q ^ (i / 2 + 1) := vf_eq q (i + 1) _ (by omega)
    have r0a : r0f i = -1 := by simp [r0f, h]
    have r0b : r0f (i + 1) = 1 := by simp [r0f, show (i + 1) % 4 = 2 by omega]
    have r1a : r1f i = -1 := by simp [r1f, h]
    have r1b : r1f (i + 1) = -1 := by simp [r1f, show (i + 1) % 4 = 2 by omega]
    obtain ⟨e1, e2, e3, e4⟩ := stA_all m ns ds i (i / 4) rfl (by omega)
    obtain ⟨f1, f2, f3, f4⟩ := stB_all m ns ds (i + 1) (i / 4) (by omega) (by omega)
    simp only [e1, e2, e3, e4] at hS0 hU0 hK0 hLU hDU ⊢
    simp only [f1, f2, f3, f4] at hS0' hU0' hK0' hlU1' hDU' ⊢
    rw [e1, e4] at hPU
    rw [f1, f4] at hPU'
    rw [hv, hv', r0a, r0b, r1a, r1b]
    obtain ⟨hSB1, hSBA, hSAU, hSBU, hUBA⟩ := hGL.1 (i / 4) hj
    obtain ⟨tq, tl⟩ := hTN.1 (i / 4) hj
    obtain ⟨-, -, -, -, hVA, -, -⟩ := cw_bound hA (i / 4) hj
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
  · -- yb_j → xb_j : same state B_j
    have hv : vf q (i + 1) = vf q i := by unfold vf; rw [show (i + 1) / 2 = i / 2 by omega]
    have r0a : r0f i = 1 := by simp [r0f, h]
    have r0b : r0f (i + 1) = -1 := by simp [r0f, show (i + 1) % 4 = 3 by omega]
    have r1a : r1f i = -1 := by simp [r1f, h]
    have r1b : r1f (i + 1) = -1 := by simp [r1f, show (i + 1) % 4 = 3 by omega]
    obtain ⟨e1, e2, e3, e4⟩ := stB_all m ns ds i (i / 4) rfl (by omega)
    obtain ⟨f1, f2, f3, f4⟩ := stB_all m ns ds (i + 1) (i / 4) (by omega) (by omega)
    simp only [e1, e2, e3, e4] at hU0 hK0 ⊢
    rw [hv, r0a, r0b, r1a, r1b, f1, f2, f3, f4]
    have hm : aE (UB m ns (i / 4)) (cOf (sig ns ds (i / 4)) * VB m ns (i / 4)) (η * -1)
        (vf q i) ≤ aE (UB m ns (i / 4)) (cOf (sig ns ds (i / 4)) * VB m ns (i / 4)) (η * 1)
        (vf q i) := aE_mono _ _ _ _ _ hU0 hK0 (by linarith)
    refine ⟨Or.inr ⟨rfl, hm⟩, Or.inr ⟨rfl, le_rfl⟩, Or.inr ⟨mul_comm _ _, by linarith⟩,
      Or.inr ⟨mul_comm _ _, by simp⟩⟩
  · -- xb_j → xa_{j+1} : B_j → A_{j+1}, equality in (S, V)
    have hj1 : i / 4 + 1 < Jn m ns := by omega
    have hv : vf q i = -q ^ (i / 2) := vf_eq q i _ rfl
    have hv' : vf q (i + 1) = -q ^ (i / 2 + 1) := vf_eq q (i + 1) _ (by omega)
    have r0a : r0f i = -1 := by simp [r0f, h]
    have r0b : r0f (i + 1) = -1 := by simp [r0f, show (i + 1) % 4 = 0 by omega]
    have r1a : r1f i = -1 := by simp [r1f, h]
    have r1b : r1f (i + 1) = 1 := by simp [r1f, show (i + 1) % 4 = 0 by omega]
    obtain ⟨e1, e2, e3, e4⟩ := stB_all m ns ds i (i / 4) rfl (by omega)
    obtain ⟨f1, f2, f3, f4⟩ := stA_all m ns ds (i + 1) (i / 4 + 1) (by omega) (by omega)
    simp only [e1, e2, e3, e4] at hS0 hK0 hLS hDS ⊢
    simp only [f1, f2, f3, f4] at hS0' hK0' hlS1' hDS' ⊢
    rw [e2, e4] at hPS
    rw [f2, f4] at hPS'
    rw [hv, hv', r0a, r0b, r1a, r1b]
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
/-- Relations of the post-saving scheme, entries `T(i+1), T(i+2)`. -/
private lemma post_rel {m ns : ℕ} {ds : ℝ} (hA : Adm m ns ds) (L D q η : ℝ) (hL0 : 0 < L)
    (hL1 : L ≤ 1)
    (hL : ∀ i, i < 4 * Jn m ns →
      L ≤ min ((sU m ns i - sK m ns ds i) / ((1 + sK m ns ds i) * sU m ns i))
        ((sS m ns i - sK m ns ds i) / ((1 + sK m ns ds i) * sS m ns i)))
    (hD0 : 0 < D) (hD : ∀ i, i < 4 * Jn m ns →
      (1 + sK m ns ds i) / sU m ns i + (1 + sK m ns ds i) / sS m ns i ≤ D)
    (hq : q = L / 2) (hη : η = q ^ (2 * Jn m ns) * L / (4 * D)) (i : ℕ)
    (hi : i + 1 < 4 * Jn m ns + 1) :
    RelP (sU m ns i) (sS m ns i) (sV m ns i) (aE (sU m ns i) (sK m ns ds i) (η * r0f i) (vf q i))
      (aE (sS m ns i) (sK m ns ds i) (η * r1f i) (vf q i)) (vf q i)
      (Tpt m ns ds (i + 1)) (Tpt m ns ds (i + 1 + 1)) := by
  have hm : 2 ≤ m := hA.1
  have hns := ns_pos hA
  have hst := hst_lem hA
  have hfac := hfac_lem hA L D hL hD
  have hq0 : 0 < q := by rw [hq]; linarith
  have hη0 : 0 < η := by rw [hη]; positivity
  unfold RelP
  have hi0 : i < 4 * Jn m ns := by omega
  have hj : i / 4 < Jn m ns := by omega
  obtain ⟨hS0, hSU, hV1, hK0, hKS⟩ := hst i hi0
  obtain ⟨hLU, hLS, hDU, hDS, hPU, hPS⟩ := hfac i hi0
  have tb := t_bounds m ns (i / 4) hm hns
  rcases (by omega : i % 4 = 0 ∨ i % 4 = 1 ∨ i % 4 = 2 ∨ i % 4 = 3) with h | h | h | h
  · have r0a : r0f i = -1 := by simp [r0f, h]
    have r1a : r1f i = 1 := by simp [r1f, h]
    obtain ⟨e1, e2, e3, e4⟩ := stA_all m ns ds i (i / 4) rfl (by omega)
    rw [e1, e2, e3, e4, r0a, r1a, pt_eq i (i / 4) 0 hi0 rfl h,
      pt_eq (i + 1) (i / 4) 1 (by omega) (by omega) (by omega)]
    have o0 := on_gadget hA (i / 4) 0 hj (by norm_num) (UA m ns (i / 4)) (SA m ns (i / 4))
      (VA m ns (i / 4)) rfl rfl rfl (η * -1) (η * 1) (vf q i)
    have o1 := on_gadget hA (i / 4) 1 hj (by norm_num) (UA m ns (i / 4)) (SA m ns (i / 4))
      (VA m ns (i / 4)) rfl rfl rfl (η * -1) (η * 1) (vf q i)
    exact ⟨Or.inr ⟨o0.1, o0.2.1 (by nlinarith [tb.1])⟩,
      Or.inr ⟨o1.1, o1.2.2 (by nlinarith [tb.2.1])⟩⟩
  · have r0a : r0f i = -1 := by simp [r0f, h]
    have r1a : r1f i = -1 := by simp [r1f, h]
    obtain ⟨e1, e2, e3, e4⟩ := stA_all m ns ds i (i / 4) rfl (by omega)
    rw [e1, e2, e3, e4, r0a, r1a, pt_eq i (i / 4) 1 hi0 rfl h,
      pt_eq (i + 1) (i / 4) 2 (by omega) (by omega) (by omega)]
    have o1 := on_gadget hA (i / 4) 1 hj (by norm_num) (UA m ns (i / 4)) (SA m ns (i / 4))
      (VA m ns (i / 4)) rfl rfl rfl (η * -1) (η * -1) (vf q i)
    exact ⟨Or.inr ⟨o1.1, o1.2.1 (by nlinarith)⟩,
      Or.inl (lifted_rel_gadget hA (i / 4) hj).1⟩
  · have r0a : r0f i = 1 := by simp [r0f, h]
    have r1a : r1f i = -1 := by simp [r1f, h]
    obtain ⟨e1, e2, e3, e4⟩ := stB_all m ns ds i (i / 4) rfl (by omega)
    rw [e1, e2, e3, e4, r0a, r1a, pt_eq i (i / 4) 2 hi0 rfl h,
      pt_eq (i + 1) (i / 4) 3 (by omega) (by omega) (by omega)]
    have o2 := on_gadget hA (i / 4) 2 hj (by norm_num) (UB m ns (i / 4)) (SB m ns (i / 4))
      (VB m ns (i / 4)) rfl rfl rfl (η * 1) (η * -1) (vf q i)
    have o3 := on_gadget hA (i / 4) 3 hj (by norm_num) (UB m ns (i / 4)) (SB m ns (i / 4))
      (VB m ns (i / 4)) rfl rfl rfl (η * 1) (η * -1) (vf q i)
    exact ⟨Or.inr ⟨o2.1, o2.2.1 (by nlinarith [tb.2.2.1])⟩,
      Or.inr ⟨o3.1, o3.2.2 (by nlinarith [tb.2.2.2])⟩⟩
  · have r0a : r0f i = -1 := by simp [r0f, h]
    have r1a : r1f i = -1 := by simp [r1f, h]
    obtain ⟨e1, e2, e3, e4⟩ := stB_all m ns ds i (i / 4) rfl (by omega)
    simp only [e1, e2, e3, e4] at hS0 hK0 hLS hDS ⊢
    rw [e2, e4] at hPS
    rw [r0a, r1a, pt_eq i (i / 4) 3 hi0 rfl h]
    have o3 := on_gadget hA (i / 4) 3 hj (by norm_num) (UB m ns (i / 4)) (SB m ns (i / 4))
      (VB m ns (i / 4)) rfl rfl rfl (η * -1) (η * -1) (vf q i)
    refine ⟨Or.inr ⟨o3.1, o3.2.1 (by nlinarith)⟩, ?_⟩
    by_cases hl : i + 1 < 4 * Jn m ns
    · rw [pt_eq (i + 1) (i / 4 + 1) 0 hl (by omega) (by omega)]
      exact Or.inl (lifted_rel_trans hA (i / 4) (by omega)).1
    · have hJe : Jn m ns = i / 4 + 1 := by omega
      rw [show i + 1 + 1 = 4 * Jn m ns + 1 by omega, pt_last]
      have hwB : wB m ns (i / 4) = o1 m ns := by
        unfold wB o1 wA; rw [hJe, Finset.prod_range_succ]; ring
      have ho1 : 0 < o1 m ns := by
        have := ((w_envelope hA).1 (Jn m ns) le_rfl).1
        unfold o1; unfold o0 at this; linarith
      have hVB : VB m ns (i / 4) = o1 m ns * SB m ns (i / 4) := by unfold VB; rw [hwB]
      have hv : vf q i = -q ^ (i / 2) := vf_eq q i _ rfl
      have h1 := aE_sub _ _ (η * -1) (-q ^ (i / 2)) hS0 hK0
      have hk := last_step q L D η _ _ (i / 2) (2 * Jn m ns) hL0 hL1 hq (by omega) hLS hDS
        hPS hD0 hη
      have hcb : vf q i - aE (SB m ns (i / 4)) (cOf (sig ns ds (i / 4)) * VB m ns (i / 4))
          (η * -1) (vf q i) < 0 := by
        rw [hv]; nlinarith
      exact Or.inr (rlot_rel _ _ _ _ _ _ _ ho1 hS0 hVB hcb)

/-! ### Pre-saving scheme (as in the `R(o_1)` deletion) -/

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

private lemma st_val (m ns : ℕ) (ds : ℝ) (i j τ : ℕ) (h1 : (i - 1) / 4 = j)
    (h2 : (i - 1) % 4 = τ) :
    stU m ns i = gU m ns j τ ∧ stS m ns i = gS m ns j τ ∧ stV m ns i = ptV m ns j τ ∧
    stK m ns ds i = cOf (sig ns ds j) * ptV m ns j τ := by
  unfold stK stV stU stS; rw [h1, h2]; exact ⟨rfl, rfl, rfl, rfl⟩

private lemma rt_val (i τ : ℕ) (hi : 1 ≤ i) (h2 : (i - 1) % 4 = τ) :
    rt0 i = r0of τ ∧ rt1 i = r1of τ := by
  unfold rt0 rt1; rw [if_neg (by omega), if_neg (by omega), h2]; exact ⟨rfl, rfl⟩

/-- Entries before the deleted point. -/
private lemma pt_pre {m ns j0 : ℕ} (hj0 : j0 < Jn m ns) (ds : ℝ) (i j τ : ℕ) (hi1 : 1 ≤ i)
    (hi : i ≤ 4 * j0) (h1 : (i - 1) / 4 = j) (h2 : (i - 1) % 4 = τ) :
    Tpt m ns ds (skipIdx (4 * j0 + 1) i) = gpt m ns ds j τ := by
  have hs : skipIdx (4 * j0 + 1) i = i := by unfold skipIdx; rw [if_pos (by omega)]
  rw [hs]; unfold Tpt
  rw [if_neg (by omega : i ≠ 0), if_neg (by omega : i ≠ 4 * Jn m ns + 1), h1, h2]

/-- Entries after the deleted point. -/
private lemma skip_post (j0 i : ℕ) (h : 4 * j0 + 1 ≤ i) : skipIdx (4 * j0 + 1) i = i + 1 := by
  unfold skipIdx; rw [if_neg (by omega)]

private lemma ptT_bounds (m ns j : ℕ) (hm : 2 ≤ m) (hns : 1 ≤ ns) :
    ptT m ns j 0 ≤ 3 / 10 ∧ ptT m ns j 3 ≤ 3 / 10 ∧ 31 / 50 ≤ ptT m ns j 1 ∧
      31 / 50 ≤ ptT m ns j 2 := by
  obtain ⟨hd0, hd5, hu0, hu1⟩ := (class_trans m ns j hm hns).1
  simp only [ptT, if_true, show (1:ℕ) ≠ 0 by decide, show (2:ℕ) ≠ 0 by decide,
    show (3:ℕ) ≠ 0 by decide, show (2:ℕ) ≠ 1 by decide, show (3:ℕ) ≠ 1 by decide,
    show (3:ℕ) ≠ 2 by decide, if_false]
  unfold fa' fa fb' fb
  refine ⟨by linarith, by linarith, by linarith, by linarith⟩

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

private lemma on_pt2 {m ns : ℕ} {ds : ℝ} (hA : Adm m ns ds) (j τ : ℕ) (hj : j < Jn m ns)
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
  have h := on_pt2 hA j τ hj (by omega) r0 r1 v
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
  have h := on_pt2 hA j τ hj hτ4 r0 r1 v
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

set_option maxHeartbeats 1600000 in
/-- Nesting of the pre-saving scheme, both indices `≤ 4 j0`. -/
private lemma pre_nest {m ns : ℕ} {ds : ℝ} (hA : Adm m ns ds) (j0 : ℕ) (hj0 : j0 < Jn m ns)
    (i : ℕ) (hi : i + 1 ≤ 4 * j0) :
    NestP (stU m ns i) (stS m ns i) (stV m ns i) (aS m ns ds i) (bS m ns ds i) (vv m ns ds i)
      (stU m ns (i + 1)) (stS m ns (i + 1)) (stV m ns (i + 1)) (aS m ns ds (i + 1))
      (bS m ns ds (i + 1)) (vv m ns ds (i + 1)) := by
  have hGL := gadget_lines hA
  have hTN := tight_nest hA
  unfold NestP
  rcases idx_cases i with rfl | ⟨j, rfl⟩ | ⟨j, rfl⟩ | ⟨j, rfl⟩ | ⟨j, rfl⟩
  · have hJ0 : 0 < Jn m ns := by omega
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
    obtain ⟨hg0, hg1, -, -, -, -⟩ := J_spec hA
    rw [u0, s0, v0, u1, s1, v1]
    refine ⟨Or.inl hU', Or.inl hS', Or.inl ?_, Or.inr ⟨by linear_combination -eSV,
      by linarith⟩⟩
    have hSB : 0 < SB m ns j := by linarith
    refine lt_of_mul_lt_mul_right ?_ hSB.le
    have h1 : UA m ns (j + 1) * SB m ns j * VB m ns j <
        UB m ns j * SA m ns (j + 1) * VB m ns j :=
      mul_lt_mul_of_pos_right hUSc (by linarith)
    linear_combination h1 - UB m ns j * eSV

set_option maxHeartbeats 1600000 in
/-- Relations of the pre-saving scheme, steps `i < 4 j0` (all entries undeleted and standard). -/
private lemma pre_rel {m ns : ℕ} {ds : ℝ} (hA : Adm m ns ds) (j0 : ℕ) (hj0 : j0 < Jn m ns)
    (i : ℕ) (hi : i < 4 * j0) :
    RelP (stU m ns i) (stS m ns i) (stV m ns i) (aS m ns ds i) (bS m ns ds i) (vv m ns ds i)
      (Tpt m ns ds (skipIdx (4 * j0 + 1) i)) (Tpt m ns ds (skipIdx (4 * j0 + 1) (i + 1))) := by
  have hm := hA.1
  have hns := ns_pos hA
  have hGL := gadget_lines hA
  have hp0 : Tpt m ns ds (skipIdx (4 * j0 + 1) 0) = Rlot o0 := by
    unfold skipIdx Tpt; simp
  unfold RelP
  simp only [aS, bS]
  rcases idx_cases i with rfl | ⟨j, rfl⟩ | ⟨j, rfl⟩ | ⟨j, rfl⟩ | ⟨j, rfl⟩
  · have hJ0 : 0 < Jn m ns := by omega
    obtain ⟨u0, s0, v0, k0⟩ := stA m ns ds 0 0 (by norm_num) (by norm_num)
    have hr0 : rt0 0 = 1 := by simp [rt0]
    have hr1 : rt1 0 = 1 := by simp [rt1]
    have hv0 : vv m ns ds 0 = 2 := rfl
    have hp1 := pt_pre hj0 ds (0 + 1) 0 0 (by norm_num) (by omega) (by norm_num) (by norm_num)
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
      obtain ⟨hg0, hg1, -, -, -, -⟩ := J_spec hA
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
    have hp := pt_pre hj0 ds (4 * j + 1) j 0 (by omega) (by omega) (by omega) (by omega)
    have hp' := pt_pre hj0 ds (4 * j + 1 + 1) j 1 (by omega) (by omega) (by omega) (by omega)
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
    have hp := pt_pre hj0 ds (4 * j + 2) j 1 (by omega) (by omega) (by omega) (by omega)
    have hp' := pt_pre hj0 ds (4 * j + 2 + 1) j 2 (by omega) (by omega) (by omega) (by omega)
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
    have hp := pt_pre hj0 ds (4 * j + 3) j 2 (by omega) (by omega) (by omega) (by omega)
    have hp' := pt_pre hj0 ds (4 * j + 3 + 1) j 3 (by omega) (by omega) (by omega) (by omega)
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
    have hp := pt_pre hj0 ds (4 * j + 4) j 3 (by omega) (by omega) (by omega) (by omega)
    have hp' := pt_pre hj0 ds (4 * j + 4 + 1) (j + 1) 0 (by omega) (by omega) (by omega)
      (by omega)
    rw [u0, s0, v0, k0, hp, hp']
    obtain ⟨h0, K, hK, hD⟩ := on_B hA j 3 (by omega) (by norm_num) (by norm_num)
      (rt0 (4 * j + 4)) (rt1 (4 * j + 4)) (vv m ns ds (4 * j + 4))
    have e0 : rt0 (4 * j + 4) = -2 := by rw [r0e]; simp [r0of]
    have e1 : rt1 (4 * j + 4) = -2 := by rw [r1e]; simp [r1of]
    refine ⟨Or.inr ⟨h0, sgn_pos hK hD ?_⟩, Or.inl (lifted_rel_trans hA j hj).1⟩
    rw [e0, e1]; linarith

/-- The step out of `xb_{j0-1}` into the (now adjacent) `ya_{j0}`: `B_{j0-1}`, rotation low;
`ya_{j0}` is strictly below `T_B(j0-1)` (R1). -/
private lemma pre_last_rel {m ns : ℕ} {ds : ℝ} (hA : Adm m ns ds) (j0 : ℕ)
    (hj0 : j0 < Jn m ns) (hj1 : 1 ≤ j0) :
    RelP (stU m ns (4 * j0)) (stS m ns (4 * j0)) (stV m ns (4 * j0)) (aS m ns ds (4 * j0))
      (bS m ns ds (4 * j0)) (vv m ns ds (4 * j0))
      (Tpt m ns ds (skipIdx (4 * j0 + 1) (4 * j0)))
      (Tpt m ns ds (skipIdx (4 * j0 + 1) (4 * j0 + 1))) := by
  obtain ⟨k, rfl⟩ : ∃ k, j0 = k + 1 := ⟨j0 - 1, by omega⟩
  unfold RelP
  simp only [aS, bS]
  obtain ⟨u0, s0, v0, k0⟩ := stB m ns ds (4 * (k + 1)) k (by omega) (by omega)
  obtain ⟨r0e, r1e⟩ := rt_val (4 * (k + 1)) 3 (by omega) (by omega)
  have hp := pt_pre hj0 ds (4 * (k + 1)) k 3 (by omega) (by omega) (by omega) (by omega)
  have hp' : Tpt m ns ds (skipIdx (4 * (k + 1) + 1) (4 * (k + 1) + 1)) =
      gpt m ns ds (k + 1) 1 := by
    rw [skip_post _ _ le_rfl]
    exact pt_eq (4 * (k + 1) + 1) (k + 1) 1 (by omega) (by omega) (by omega)
  rw [u0, s0, v0, k0, hp, hp']
  obtain ⟨h0, K, hK, hD⟩ := on_B hA k 3 (by omega) (by norm_num) (by norm_num)
    (rt0 (4 * (k + 1))) (rt1 (4 * (k + 1))) (vv m ns ds (4 * (k + 1)))
  have e0 : rt0 (4 * (k + 1)) = -2 := by rw [r0e]; simp [r0of]
  have e1 : rt1 (4 * (k + 1)) = -2 := by rw [r1e]; simp [r1of]
  refine ⟨Or.inr ⟨h0, sgn_pos hK hD ?_⟩, Or.inl (lifted_rel_trans hA k hj0).2.1⟩
  rw [e0, e1]; linarith

/-- The saving step `B_{j0-1} → B_{j0}` is strict in every coordinate. -/
private lemma saving_nest {m ns : ℕ} {ds : ℝ} (hA : Adm m ns ds) (j0 : ℕ)
    (hj0 : j0 < Jn m ns) (hj1 : 1 ≤ j0) (a b c a' b' c' : ℝ) :
    NestP (stU m ns (4 * j0)) (stS m ns (4 * j0)) (stV m ns (4 * j0)) a b c
      (UB m ns j0) (SB m ns j0) (VB m ns j0) a' b' c' := by
  obtain ⟨k, rfl⟩ : ∃ k, j0 = k + 1 := ⟨j0 - 1, by omega⟩
  obtain ⟨u0, s0, v0, -⟩ := stB m ns ds (4 * (k + 1)) k (by omega) (by omega)
  have hGL := gadget_lines hA
  obtain ⟨-, hSBA, -, -, hUBA⟩ := hGL.1 (k + 1) hj0
  obtain ⟨hU', hS'⟩ := hGL.2 k hj0
  obtain ⟨-, -, t3, t4, -⟩ := (tight_nest hA).2 k hj0
  unfold NestP
  rw [u0, s0, v0]
  exact ⟨Or.inl (by linarith), Or.inl (by linarith), Or.inl t3, Or.inl t4⟩

/-! ### The patched gadget `j0` and the front for `j0 = 0` -/

private lemma patch_rel {m ns : ℕ} {ds : ℝ} (hA : Adm m ns ds) (j : ℕ) (hj : j < Jn m ns)
    (η v : ℝ) (hη : 0 < η) :
    RelP (UB m ns j) (SB m ns j) (VB m ns j)
      (aE (UB m ns j) (cOf (sig ns ds j) * VB m ns j) (η * 2) v)
      (aE (SB m ns j) (cOf (sig ns ds j) * VB m ns j) (η * 2) v) v
      (gpt m ns ds j 1) (gpt m ns ds j 2) := by
  have o2 := on_gadget hA j 2 hj (by norm_num) (UB m ns j) (SB m ns j) (VB m ns j) rfl rfl rfl
    (η * 2) (η * 2) v
  have e : η * 2 * (1 - ptT m ns j 2) + η * 2 * ptT m ns j 2 = 2 * η := by ring
  exact ⟨Or.inl (lifted_rel_gadget hA j hj).2.2.2, Or.inr ⟨o2.1, o2.2.2 (by linarith)⟩⟩

private lemma patch_nest {m ns : ℕ} {ds : ℝ} (hA : Adm m ns ds) (j : ℕ) (hj : j < Jn m ns)
    (q η : ℝ) (hη : 0 ≤ η) :
    NestP (UB m ns j) (SB m ns j) (VB m ns j)
      (aE (UB m ns j) (cOf (sig ns ds j) * VB m ns j) (η * 2) (vf q (4 * j + 2)))
      (aE (SB m ns j) (cOf (sig ns ds j) * VB m ns j) (η * 2) (vf q (4 * j + 2)))
      (vf q (4 * j + 2))
      (sU m ns (4 * j + 2)) (sS m ns (4 * j + 2)) (sV m ns (4 * j + 2))
      (aE (sU m ns (4 * j + 2)) (sK m ns ds (4 * j + 2)) (η * r0f (4 * j + 2))
        (vf q (4 * j + 2)))
      (aE (sS m ns (4 * j + 2)) (sK m ns ds (4 * j + 2)) (η * r1f (4 * j + 2))
        (vf q (4 * j + 2)))
      (vf q (4 * j + 2)) := by
  obtain ⟨e1, e2, e3, e4⟩ := stB_all m ns ds (4 * j + 2) j (by omega) (by omega)
  have r0a : r0f (4 * j + 2) = 1 := by simp [r0f, show (4 * j + 2) % 4 = 2 by omega]
  have r1a : r1f (4 * j + 2) = -1 := by simp [r1f, show (4 * j + 2) % 4 = 2 by omega]
  obtain ⟨hS, hSU, -, hk, -⟩ := g_pos hA j 2 hj
  simp only [gS, gU, ptV, if_neg (show ¬ (2:ℕ) < 2 by norm_num)] at hS hSU hk
  unfold NestP
  rw [e1, e2, e3, e4, r0a, r1a]
  have ha := aE_mono (UB m ns j) _ (η * 2) (η * 1) (vf q (4 * j + 2)) (by linarith) hk
    (by linarith)
  have hb := aE_mono (SB m ns j) _ (η * 2) (η * -1) (vf q (4 * j + 2)) hS hk (by linarith)
  exact ⟨Or.inr ⟨rfl, ha⟩, Or.inr ⟨rfl, hb⟩, Or.inr ⟨mul_comm _ _, by linarith⟩,
    Or.inr ⟨mul_comm _ _, by linarith⟩⟩

/-- Scale of the front state for `j0 = 0`. -/
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

private lemma front0_rel {m ns : ℕ} {ds : ℝ} (hA : Adm m ns ds) (j : ℕ) (hj : j < Jn m ns)
    (hj0 : j = 0) (a b c : ℝ) :
    RelP (UB m ns j / eps0 m ns j) (SB m ns j / eps0 m ns j) (VB m ns j / eps0 m ns j) a b c
      (Rlot o0) (gpt m ns ds j 1) := by
  subst hj0
  have hm := hA.1
  have hns := ns_pos hA
  obtain ⟨he0, he1, hUe, hSe⟩ := eps0_bounds hA 0 hj
  obtain ⟨hg0, hg1, -, -, -, -⟩ := J_spec hA
  obtain ⟨hSB1, hSBA, hSAU, hSBU, -⟩ := (gadget_lines hA).1 0 hj
  have hSB : 0 < SB m ns 0 := by linarith
  unfold RelP
  refine ⟨Or.inl ?_, Or.inl ?_⟩
  · -- R(o0) strictly above: V/S = ρ_0 o_0 > o_0
    have hrho := ((rho_bounds hA).1 0 hj).1
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
  · -- ya_0 strictly below: compare with T_A(0), on which ya_0 lies
    have hon := (on_gadget hA 0 1 hj (by norm_num) (UA m ns 0) (SA m ns 0) (VA m ns 0) rfl rfl
      rfl 0 0 0).1
    obtain ⟨c0, c1, c3⟩ := gpt_c m ns ds 0 1
    have hs : sig ns ds 0 = 0 := by simp [sig]
    have hH := (cw_bound hA 0 hj).2.2.2.2.2.2 1 (by norm_num)
    rw [hs] at hH c0 c1 c3
    generalize hLift 0 (ptL m ns 0 1) (ptV m ns 0 1) = H at hH c0 c1 c3
    have hfac : 0 < 1 - H / (1 + H) := by
      rw [sub_pos, div_lt_one (by linarith)]; linarith
    obtain ⟨-, -, t1, -⟩ := ptT_bounds m ns 0 hm hns
    have tlt : ptT m ns 0 1 < 1 := by
      obtain ⟨hd0, hd5, hu0, hu1⟩ := (class_trans m ns 0 hm hns).1
      simp only [ptT, show (1:ℕ) ≠ 0 by decide, if_false, if_true]
      unfold fb; linarith
    have hq0 : 0 ≤ gpt m ns ds 0 1 0 := by
      rw [c0]; apply mul_nonneg (by nlinarith) (by linarith)
    have hq1 : 0 < gpt m ns ds 0 1 1 := by
      rw [c1]; apply mul_pos (by nlinarith) (by linarith)
    unfold fval at hon ⊢
    rw [c3] at hon ⊢
    have hU' : 0 < UB m ns 0 / eps0 m ns 0 - UA m ns 0 := by linarith
    have hS' : 0 < SB m ns 0 / eps0 m ns 0 - SA m ns 0 := by rw [hSe]; linarith
    nlinarith [mul_nonneg hU'.le hq0, mul_pos hS' hq1]

/-! ### The assembled direction data -/

private def FU (m ns j i : ℕ) : ℝ :=
  if j = 0 ∧ i = 0 then UB m ns j / eps0 m ns j else if i ≤ 4 * j then stU m ns i
  else if i = 4 * j + 1 then UB m ns j else sU m ns i
private def FS (m ns j i : ℕ) : ℝ :=
  if j = 0 ∧ i = 0 then SB m ns j / eps0 m ns j else if i ≤ 4 * j then stS m ns i
  else if i = 4 * j + 1 then SB m ns j else sS m ns i
private def FV (m ns j i : ℕ) : ℝ :=
  if j = 0 ∧ i = 0 then VB m ns j / eps0 m ns j else if i ≤ 4 * j then stV m ns i
  else if i = 4 * j + 1 then VB m ns j else sV m ns i
private def Fa (m ns : ℕ) (ds q η : ℝ) (j i : ℕ) : ℝ :=
  if j = 0 ∧ i = 0 then
    aE (UB m ns j) (cOf (sig ns ds j) * VB m ns j) (η * 2) (vf q (4 * j + 2))
  else if i ≤ 4 * j then aS m ns ds i
  else if i = 4 * j + 1 then
    aE (UB m ns j) (cOf (sig ns ds j) * VB m ns j) (η * 2) (vf q (4 * j + 2))
  else aE (sU m ns i) (sK m ns ds i) (η * r0f i) (vf q i)
private def Fb (m ns : ℕ) (ds q η : ℝ) (j i : ℕ) : ℝ :=
  if j = 0 ∧ i = 0 then
    aE (SB m ns j) (cOf (sig ns ds j) * VB m ns j) (η * 2) (vf q (4 * j + 2))
  else if i ≤ 4 * j then bS m ns ds i
  else if i = 4 * j + 1 then
    aE (SB m ns j) (cOf (sig ns ds j) * VB m ns j) (η * 2) (vf q (4 * j + 2))
  else aE (sS m ns i) (sK m ns ds i) (η * r1f i) (vf q i)
private def Fc (m ns : ℕ) (ds q : ℝ) (j i : ℕ) : ℝ :=
  if j = 0 ∧ i = 0 then vf q (4 * j + 2)
  else if i ≤ 4 * j then vv m ns ds i
  else if i = 4 * j + 1 then vf q (4 * j + 2)
  else vf q i

private lemma F_front0 (m ns : ℕ) (ds q η : ℝ) (j i : ℕ) (h : j = 0 ∧ i = 0) :
    FU m ns j i = UB m ns j / eps0 m ns j ∧ FS m ns j i = SB m ns j / eps0 m ns j ∧
    FV m ns j i = VB m ns j / eps0 m ns j ∧
    Fa m ns ds q η j i =
      aE (UB m ns j) (cOf (sig ns ds j) * VB m ns j) (η * 2) (vf q (4 * j + 2)) ∧
    Fb m ns ds q η j i =
      aE (SB m ns j) (cOf (sig ns ds j) * VB m ns j) (η * 2) (vf q (4 * j + 2)) ∧
    Fc m ns ds q j i = vf q (4 * j + 2) := by
  simp only [FU, FS, FV, Fa, Fb, Fc, if_pos h, and_self]

private lemma F_pre (m ns : ℕ) (ds q η : ℝ) (j i : ℕ) (hj : 1 ≤ j) (hi : i ≤ 4 * j) :
    FU m ns j i = stU m ns i ∧ FS m ns j i = stS m ns i ∧ FV m ns j i = stV m ns i ∧
    Fa m ns ds q η j i = aS m ns ds i ∧ Fb m ns ds q η j i = bS m ns ds i ∧
    Fc m ns ds q j i = vv m ns ds i := by
  have c0 : ¬ (j = 0 ∧ i = 0) := by omega
  simp only [FU, FS, FV, Fa, Fb, Fc, if_neg c0, if_pos hi, and_self]

private lemma F_patch (m ns : ℕ) (ds q η : ℝ) (j i : ℕ) (hi : i = 4 * j + 1) :
    FU m ns j i = UB m ns j ∧ FS m ns j i = SB m ns j ∧ FV m ns j i = VB m ns j ∧
    Fa m ns ds q η j i =
      aE (UB m ns j) (cOf (sig ns ds j) * VB m ns j) (η * 2) (vf q (4 * j + 2)) ∧
    Fb m ns ds q η j i =
      aE (SB m ns j) (cOf (sig ns ds j) * VB m ns j) (η * 2) (vf q (4 * j + 2)) ∧
    Fc m ns ds q j i = vf q (4 * j + 2) := by
  have c0 : ¬ (j = 0 ∧ i = 0) := by omega
  have c1 : ¬ i ≤ 4 * j := by omega
  simp only [FU, FS, FV, Fa, Fb, Fc, if_neg c0, if_neg c1, if_pos hi, and_self]

private lemma F_post (m ns : ℕ) (ds q η : ℝ) (j i : ℕ) (hi : 4 * j + 2 ≤ i) :
    FU m ns j i = sU m ns i ∧ FS m ns j i = sS m ns i ∧ FV m ns j i = sV m ns i ∧
    Fa m ns ds q η j i = aE (sU m ns i) (sK m ns ds i) (η * r0f i) (vf q i) ∧
    Fb m ns ds q η j i = aE (sS m ns i) (sK m ns ds i) (η * r1f i) (vf q i) ∧
    Fc m ns ds q j i = vf q i := by
  have c0 : ¬ (j = 0 ∧ i = 0) := by omega
  have c1 : ¬ i ≤ 4 * j := by omega
  have c2 : ¬ i = 4 * j + 1 := by omega
  simp only [FU, FS, FV, Fa, Fb, Fc, if_neg c0, if_neg c1, if_neg c2, and_self]

end

set_option maxHeartbeats 1600000 in
/-- Deleting `xa_j` (position `4j+1`) leaves a ranking with a chain. -/
theorem del_xa {m ns : ℕ} {ds : ℝ} (hA : Adm m ns ds) (j : ℕ) (hj : j < Jn m ns) :
    ∃ W, IsChainFn (4 * Jn m ns + 1) (fun i => Tpt m ns ds (skipIdx (4 * j + 1) i)) W := by
  obtain ⟨L, hL0, hL1, hL⟩ := fin_lower (4 * Jn m ns)
    (fun i => min ((sU m ns i - sK m ns ds i) / ((1 + sK m ns ds i) * sU m ns i))
      ((sS m ns i - sK m ns ds i) / ((1 + sK m ns ds i) * sS m ns i)))
    (fun i hi => lt_min (hlam_lem hA i hi).1 (hlam_lem hA i hi).2.2.1)
  obtain ⟨D, hD0, hD⟩ := fin_upper (4 * Jn m ns)
    (fun i => (1 + sK m ns ds i) / sU m ns i + (1 + sK m ns ds i) / sS m ns i)
  obtain ⟨q, hq⟩ : ∃ q : ℝ, q = L / 2 := ⟨_, rfl⟩
  obtain ⟨η, hη⟩ : ∃ η : ℝ, η = q ^ (2 * Jn m ns) * L / (4 * D) := ⟨_, rfl⟩
  have hq0 : 0 < q := by rw [hq]; linarith
  have hη0 : 0 < η := by rw [hη]; positivity
  have hst := hst_lem hA
  refine strictify (4 * Jn m ns + 1) _ (FU m ns j) (FS m ns j) (FV m ns j)
    (Fa m ns ds q η j) (Fb m ns ds q η j) (Fc m ns ds q j) ?_ ?_ ?_
  · -- coordinates
    intro i hi
    by_cases h0 : j = 0 ∧ i = 0
    · obtain ⟨e1, e2, e3, -⟩ := F_front0 m ns ds q η j i h0
      rw [e1, e2, e3]
      exact front0_pos hA j hj
    by_cases h1 : i ≤ 4 * j
    · obtain ⟨e1, e2, e3, -⟩ := F_pre m ns ds q η j i (by omega) h1
      rw [e1, e2, e3]
      obtain ⟨u1, s1, v1, -⟩ := st_val m ns ds i ((i - 1) / 4) ((i - 1) % 4) rfl rfl
      obtain ⟨h1, h2, h3, -⟩ := g_pos hA ((i - 1) / 4) ((i - 1) % 4) (by omega)
      rw [u1, s1, v1]; exact ⟨h1, h2, h3⟩
    by_cases h2 : i = 4 * j + 1
    · obtain ⟨e1, e2, e3, -⟩ := F_patch m ns ds q η j i h2
      rw [e1, e2, e3]
      obtain ⟨hS, hSU, hV, -⟩ := g_pos hA j 2 hj
      simp only [gS, gU, ptV, if_neg (show ¬ (2:ℕ) < 2 by norm_num)] at hS hSU hV
      exact ⟨hS, hSU, hV⟩
    · obtain ⟨e1, e2, e3, -⟩ := F_post m ns ds q η j i (by omega)
      rw [e1, e2, e3]
      obtain ⟨a, b, c, -⟩ := hst i (by omega)
      exact ⟨a, b, c⟩
  · -- nesting
    intro i hi
    show NestP (FU m ns j i) (FS m ns j i) (FV m ns j i) (Fa m ns ds q η j i)
      (Fb m ns ds q η j i) (Fc m ns ds q j i) (FU m ns j (i + 1)) (FS m ns j (i + 1))
      (FV m ns j (i + 1)) (Fa m ns ds q η j (i + 1)) (Fb m ns ds q η j (i + 1))
      (Fc m ns ds q j (i + 1))
    by_cases h0 : j = 0 ∧ i = 0
    · obtain ⟨e1, e2, e3, e4, e5, e6⟩ := F_front0 m ns ds q η j i h0
      obtain ⟨f1, f2, f3, f4, f5, f6⟩ := F_patch m ns ds q η j (i + 1) (by omega)
      rw [e1, e2, e3, e4, e5, e6, f1, f2, f3, f4, f5, f6]
      exact front0_nest hA j hj _ _ _
    by_cases h1 : i + 1 ≤ 4 * j
    · obtain ⟨e1, e2, e3, e4, e5, e6⟩ := F_pre m ns ds q η j i (by omega) (by omega)
      obtain ⟨f1, f2, f3, f4, f5, f6⟩ := F_pre m ns ds q η j (i + 1) (by omega) h1
      rw [e1, e2, e3, e4, e5, e6, f1, f2, f3, f4, f5, f6]
      exact pre_nest hA j hj i h1
    by_cases h2 : i = 4 * j
    · obtain ⟨e1, e2, e3, e4, e5, e6⟩ := F_pre m ns ds q η j i (by omega) (by omega)
      obtain ⟨f1, f2, f3, f4, f5, f6⟩ := F_patch m ns ds q η j (i + 1) (by omega)
      rw [e1, e2, e3, e4, e5, e6, f1, f2, f3, f4, f5, f6, h2]
      exact saving_nest hA j hj (by omega) _ _ _ _ _ _
    by_cases h3 : i = 4 * j + 1
    · obtain ⟨e1, e2, e3, e4, e5, e6⟩ := F_patch m ns ds q η j i h3
      obtain ⟨f1, f2, f3, f4, f5, f6⟩ := F_post m ns ds q η j (i + 1) (by omega)
      rw [e1, e2, e3, e4, e5, e6, f1, f2, f3, f4, f5, f6]
      rw [show i + 1 = 4 * j + 2 by omega]
      exact patch_nest hA j hj q η hη0.le
    · obtain ⟨e1, e2, e3, e4, e5, e6⟩ := F_post m ns ds q η j i (by omega)
      obtain ⟨f1, f2, f3, f4, f5, f6⟩ := F_post m ns ds q η j (i + 1) (by omega)
      rw [e1, e2, e3, e4, e5, e6, f1, f2, f3, f4, f5, f6]
      exact post_nest hA L D q η hL0 hL1 hL hD0 hD hq hη i hi
  · -- relations
    intro i hi
    show RelP (FU m ns j i) (FS m ns j i) (FV m ns j i) (Fa m ns ds q η j i)
      (Fb m ns ds q η j i) (Fc m ns ds q j i) (Tpt m ns ds (skipIdx (4 * j + 1) i))
      (Tpt m ns ds (skipIdx (4 * j + 1) (i + 1)))
    by_cases h0 : j = 0 ∧ i = 0
    · obtain ⟨e1, e2, e3, e4, e5, e6⟩ := F_front0 m ns ds q η j i h0
      rw [e1, e2, e3, e4, e5, e6]
      obtain ⟨rfl, rfl⟩ := h0
      have hp0 : Tpt m ns ds (skipIdx (4 * 0 + 1) 0) = Rlot o0 := by
        unfold skipIdx Tpt; simp
      have hp1 : Tpt m ns ds (skipIdx (4 * 0 + 1) (0 + 1)) = gpt m ns ds 0 1 := by
        rw [skip_post 0 (0 + 1) (by omega)]
        exact pt_eq (0 + 1) 0 1 (by omega) (by omega) (by omega)
      rw [hp0, hp1]
      exact front0_rel hA 0 hj rfl _ _ _
    by_cases h1 : i < 4 * j
    · obtain ⟨e1, e2, e3, e4, e5, e6⟩ := F_pre m ns ds q η j i (by omega) (by omega)
      rw [e1, e2, e3, e4, e5, e6]
      exact pre_rel hA j hj i h1
    by_cases h2 : i = 4 * j
    · obtain ⟨e1, e2, e3, e4, e5, e6⟩ := F_pre m ns ds q η j i (by omega) (by omega)
      rw [e1, e2, e3, e4, e5, e6, h2]
      exact pre_last_rel hA j hj (by omega)
    by_cases h3 : i = 4 * j + 1
    · obtain ⟨e1, e2, e3, e4, e5, e6⟩ := F_patch m ns ds q η j i h3
      rw [e1, e2, e3, e4, e5, e6, skip_post j i (by omega), skip_post j (i + 1) (by omega)]
      rw [pt_eq i j 1 (by omega) (by omega) (by omega),
        pt_eq (i + 1) j 2 (by omega) (by omega) (by omega)]
      exact patch_rel hA j hj η _ hη0
    · obtain ⟨e1, e2, e3, e4, e5, e6⟩ := F_post m ns ds q η j i (by omega)
      rw [e1, e2, e3, e4, e5, e6, skip_post j i (by omega), skip_post j (i + 1) (by omega)]
      exact post_rel hA L D q η hL0 hL1 hL hD0 hD hq hη i hi

end Q2CL
