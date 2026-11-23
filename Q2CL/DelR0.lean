import Q2CL.Defs
import Q2CL.Strictify
import Q2CL.TightNest
import Q2CL.LiftedRelGadget
import Q2CL.LiftedRelTrans
import Q2CL.ReliftDval
import Q2CL.LiftOn
import Q2CL.Normalization
import Q2CL.ClassTrans

namespace Q2CL

open K4

noncomputable section

/-! ### States, rotations and the re-lift direction -/

private def sU (m ns i : ℕ) : ℝ := if i % 4 < 2 then UA m ns (i / 4) else UB m ns (i / 4)
private def sS (m ns i : ℕ) : ℝ := if i % 4 < 2 then SA m ns (i / 4) else SB m ns (i / 4)
private def sV (m ns i : ℕ) : ℝ := if i % 4 < 2 then VA m ns (i / 4) else VB m ns (i / 4)
private def sK (m ns : ℕ) (ds : ℝ) (i : ℕ) : ℝ := cOf (sig ns ds (i / 4)) * sV m ns i
private def r0f (i : ℕ) : ℝ := if i % 4 = 2 then 1 else -1
private def r1f (i : ℕ) : ℝ := if i % 4 = 0 then 1 else -1
private def vf (q : ℝ) (i : ℕ) : ℝ := -q ^ (i / 2)
/-- re-lift log-direction of a coordinate `U` (or `S`) for rotation `r` and `log V`-move `v`. -/
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

/-- An on-point: value `0`, and the first-order value along the re-lift direction has the sign
opposite to the rotation at `t`. -/
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

private lemma pt_eq {m ns : ℕ} {ds : ℝ} (i j τ : ℕ) (hi : i < 4 * Jn m ns) (h1 : i / 4 = j)
    (h2 : i % 4 = τ) : Tpt m ns ds (skipIdx 0 i) = gpt m ns ds j τ := by
  unfold skipIdx Tpt
  rw [if_neg (Nat.not_lt_zero _), if_neg (by omega), if_neg (by omega)]
  rw [show i + 1 - 1 = i by omega, h1, h2]

private lemma pt_last {m ns : ℕ} {ds : ℝ} :
    Tpt m ns ds (skipIdx 0 (4 * Jn m ns)) = Rlot (o1 m ns) := by
  unfold skipIdx Tpt
  rw [if_neg (Nat.not_lt_zero _), if_neg (by omega), if_pos rfl]

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

end

set_option maxHeartbeats 1600000 in
/-- Deleting `R(o_0)` (position `0`) leaves a ranking with a chain. -/
theorem del_R0 {m ns : ℕ} {ds : ℝ} (hA : Adm m ns ds) :
    ∃ W, IsChainFn (4 * Jn m ns + 1) (fun i => Tpt m ns ds (skipIdx 0 i)) W := by
  obtain ⟨hm, h30, hds, hns1⟩ := id hA
  have hns : 1 ≤ ns := by
    rcases Nat.eq_zero_or_pos ns with h | h
    · subst h; simp at h30
    · exact h
  obtain ⟨hg0, hg1, hJ2, -, -, -⟩ := J_spec hA
  have hGL := gadget_lines hA
  have hTN := tight_nest hA
  have hst : ∀ i, i < 4 * Jn m ns → 0 < sS m ns i ∧ sS m ns i < sU m ns i ∧ 1 < sV m ns i ∧
      0 ≤ sK m ns ds i ∧ sK m ns ds i < sS m ns i := by
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
  have hlam : ∀ i, i < 4 * Jn m ns →
      0 < (sU m ns i - sK m ns ds i) / ((1 + sK m ns ds i) * sU m ns i) ∧
      (sU m ns i - sK m ns ds i) / ((1 + sK m ns ds i) * sU m ns i) ≤ 1 ∧
      0 < (sS m ns i - sK m ns ds i) / ((1 + sK m ns ds i) * sS m ns i) ∧
      (sS m ns i - sK m ns ds i) / ((1 + sK m ns ds i) * sS m ns i) ≤ 1 := by
    intro i hi
    obtain ⟨hS0, hSU, -, hK0, hKS⟩ := hst i hi
    have hU0 : 0 < sU m ns i := by linarith
    have d1 : 0 < (1 + sK m ns ds i) * sU m ns i := by positivity
    have d2 : 0 < (1 + sK m ns ds i) * sS m ns i := by positivity
    refine ⟨div_pos (by linarith) d1, (div_le_one d1).2 (by nlinarith),
      div_pos (by linarith) d2, (div_le_one d2).2 (by nlinarith)⟩
  obtain ⟨L, hL0, hL1, hL⟩ := fin_lower (4 * Jn m ns)
    (fun i => min ((sU m ns i - sK m ns ds i) / ((1 + sK m ns ds i) * sU m ns i))
      ((sS m ns i - sK m ns ds i) / ((1 + sK m ns ds i) * sS m ns i)))
    (fun i hi => lt_min (hlam i hi).1 (hlam i hi).2.2.1)
  obtain ⟨D, hD0, hD⟩ := fin_upper (4 * Jn m ns)
    (fun i => (1 + sK m ns ds i) / sU m ns i + (1 + sK m ns ds i) / sS m ns i)
  set q : ℝ := L / 2 with hq
  set η : ℝ := q ^ (2 * Jn m ns) * L / (4 * D) with hη
  have hq0 : 0 < q := by rw [hq]; linarith
  have hη0 : 0 < η := by rw [hη]; positivity
  -- per-index facts, in a form convenient after rewriting
  have hfac : ∀ i, i < 4 * Jn m ns →
      L ≤ (sU m ns i - sK m ns ds i) / ((1 + sK m ns ds i) * sU m ns i) ∧
      L ≤ (sS m ns i - sK m ns ds i) / ((1 + sK m ns ds i) * sS m ns i) ∧
      (1 + sK m ns ds i) / sU m ns i ≤ D ∧ (1 + sK m ns ds i) / sS m ns i ≤ D ∧
      0 ≤ (1 + sK m ns ds i) / sU m ns i ∧ 0 ≤ (1 + sK m ns ds i) / sS m ns i := by
    intro i hi
    obtain ⟨hS0, hSU, -, hK0, -⟩ := hst i hi
    have h1 := hL i hi
    have h2 := hD i hi
    have p1 : 0 ≤ (1 + sK m ns ds i) / sU m ns i := div_nonneg (by linarith) (by linarith)
    have p2 : 0 ≤ (1 + sK m ns ds i) / sS m ns i := div_nonneg (by linarith) (by linarith)
    exact ⟨h1.trans (min_le_left _ _), h1.trans (min_le_right _ _), by linarith,
      by linarith, p1, p2⟩
  refine strictify (4 * Jn m ns + 1) _ (sU m ns) (sS m ns) (sV m ns)
    (fun i => aE (sU m ns i) (sK m ns ds i) (η * r0f i) (vf q i))
    (fun i => aE (sS m ns i) (sK m ns ds i) (η * r1f i) (vf q i)) (vf q) ?_ ?_ ?_
  · intro i hi
    obtain ⟨a, b, c, -, -⟩ := hst i (by omega)
    exact ⟨a, b, c⟩
  · intro i hi
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
    beta_reduce
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
  · intro i hi
    have hi0 : i < 4 * Jn m ns := by omega
    have hj : i / 4 < Jn m ns := by omega
    obtain ⟨hS0, hSU, hV1, hK0, hKS⟩ := hst i hi0
    obtain ⟨hLU, hLS, hDU, hDS, hPU, hPS⟩ := hfac i hi0
    have tb := t_bounds m ns (i / 4) hm hns
    beta_reduce
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
        rw [show i + 1 = 4 * Jn m ns by omega, pt_last]
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

end Q2CL
