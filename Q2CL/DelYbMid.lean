import Q2CL.Defs
import Q2CL.Strictify
import Q2CL.TightNest
import Q2CL.LiftedRelGadget
import Q2CL.LiftedRelTrans
import Q2CL.ReliftDval
import Q2CL.LiftOn
import Q2CL.Normalization

namespace Q2CL

open K4

noncomputable section

/-! ### Labels of the chain with `yb_j` deleted

State `i` is the vector between entries `i` and `i + 1` of the deleted list.
* `i = 0`: `A_0`, rotation `(1, 1)`;
* `1 ≤ i ≤ 4j+2`: tight label of the original entry `i`;
* `i = 4j+3` (after `xb_j`): `A_{j+1}`, rotation raise `(2, 2)`;
* `i ≥ 4j+4`: tight label of the original entry `i + 1`. -/

private def gIx (j i : ℕ) : ℕ :=
  if i ≤ 4 * j + 2 then (i - 1) / 4 else if i = 4 * j + 3 then j + 1 else i / 4
private def tIx (j i : ℕ) : ℕ :=
  if i ≤ 4 * j + 2 then (i - 1) % 4 else if i = 4 * j + 3 then 0 else i % 4

private def lU (m ns g τ : ℕ) : ℝ := if τ < 2 then UA m ns g else UB m ns g
private def lS (m ns g τ : ℕ) : ℝ := if τ < 2 then SA m ns g else SB m ns g

private def sU (m ns j i : ℕ) : ℝ := lU m ns (gIx j i) (tIx j i)
private def sS (m ns j i : ℕ) : ℝ := lS m ns (gIx j i) (tIx j i)
private def sV (m ns j i : ℕ) : ℝ := ptV m ns (gIx j i) (tIx j i)
private def sK (m ns : ℕ) (ds : ℝ) (j i : ℕ) : ℝ := cOf (sig ns ds (gIx j i)) * sV m ns j i

private def r0f (j i : ℕ) : ℝ :=
  if i = 0 then 1 else if i = 4 * j + 3 then 2 else if tIx j i = 2 then 1 else -1
private def r1f (j i : ℕ) : ℝ :=
  if i = 0 then 1 else if i = 4 * j + 3 then 2 else if tIx j i = 0 then 1 else -1

/-- `log V`-speeds: growing geometrically before the saving step, shrinking after it. -/
private def vf (q : ℝ) (N j i : ℕ) : ℝ :=
  if i ≤ 4 * j + 2 then q ^ (N - (if i = 0 then 1 else (i + 1) / 2))
  else -q ^ (if i = 4 * j + 3 then 2 * j + 2 else i / 2)

/-- re-lift log-direction of a coordinate `U` (or `S`) for rotation `r` and `log V`-move `v`. -/
private def aE (U K r v : ℝ) : ℝ := ((1 + K) * r + ((U - K) / (1 + K) + 1) * K * v) / U

private lemma ix_eval (j i g τ : ℕ)
    (h : (i ≤ 4 * j + 2 ∧ (i - 1) / 4 = g ∧ (i - 1) % 4 = τ) ∨
      (i = 4 * j + 3 ∧ g = j + 1 ∧ τ = 0) ∨ (4 * j + 4 ≤ i ∧ i / 4 = g ∧ i % 4 = τ)) :
    gIx j i = g ∧ tIx j i = τ := by
  unfold gIx tIx
  rcases h with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
  · rw [if_pos h1, if_pos h1]; exact ⟨h2, h3⟩
  · rw [if_neg (by omega), if_pos h1, if_neg (by omega), if_pos h1]; exact ⟨h2.symm, h3.symm⟩
  · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
    exact ⟨h2, h3⟩

private lemma gIx_lt {m ns j i : ℕ} (hj : j + 1 < Jn m ns) (hi : i < 4 * Jn m ns) :
    gIx j i < Jn m ns := by
  unfold gIx; split_ifs <;> omega

private lemma lblA (m ns : ℕ) (ds : ℝ) (j i g τ : ℕ) (hx : gIx j i = g ∧ tIx j i = τ)
    (hτ : τ < 2) :
    sU m ns j i = UA m ns g ∧ sS m ns j i = SA m ns g ∧ sV m ns j i = VA m ns g ∧
      sK m ns ds j i = cOf (sig ns ds g) * VA m ns g := by
  unfold sK sV sU sS lU lS ptV; rw [hx.1, hx.2]; simp [hτ]

private lemma lblB (m ns : ℕ) (ds : ℝ) (j i g τ : ℕ) (hx : gIx j i = g ∧ tIx j i = τ)
    (hτ : 2 ≤ τ) :
    sU m ns j i = UB m ns g ∧ sS m ns j i = SB m ns g ∧ sV m ns j i = VB m ns g ∧
      sK m ns ds j i = cOf (sig ns ds g) * VB m ns g := by
  have : ¬ τ < 2 := by omega
  unfold sK sV sU sS lU lS ptV; rw [hx.1, hx.2]; simp [this]

private lemma rot_eval (j i τ : ℕ) (h0 : i ≠ 0) (h3 : i ≠ 4 * j + 3) (ht : tIx j i = τ) :
    r0f j i = (if τ = 2 then 1 else -1) ∧ r1f j i = (if τ = 0 then 1 else -1) := by
  unfold r0f r1f; rw [if_neg h0, if_neg h3, if_neg h0, if_neg h3, ht]; exact ⟨rfl, rfl⟩

private lemma vf_pre (q : ℝ) (N j i e : ℕ) (h : i ≤ 4 * j + 2)
    (he : (i = 0 ∧ e = 1) ∨ (i ≠ 0 ∧ (i + 1) / 2 = e)) : vf q N j i = q ^ (N - e) := by
  unfold vf; rw [if_pos h]
  rcases he with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [if_pos h1, h2]
  · rw [if_neg h1, h2]

private lemma vf_post (q : ℝ) (N j i e : ℕ) (h : 4 * j + 3 ≤ i)
    (he : (i = 4 * j + 3 ∧ e = 2 * j + 2) ∨ (i ≠ 4 * j + 3 ∧ i / 2 = e)) :
    vf q N j i = -q ^ e := by
  unfold vf; rw [if_neg (by omega)]
  rcases he with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [if_pos h1, h2]
  · rw [if_neg h1, h2]

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

/-- Binding step after the saving step: `v = -q^f → -q^(f+1)`. -/
private lemma key_post (q L D η U K U' K' : ℝ) (f N : ℕ) (hL0 : 0 < L) (hL1 : L ≤ 1)
    (hq : q = L / 2) (hf : f ≤ N) (hD : 0 < D) (hη : η = q ^ N * L / (4 * D))
    (hU : 0 < U) (hK : 0 ≤ K) (hU' : 0 < U') (hK' : 0 ≤ K')
    (hl : L ≤ (U - K) / ((1 + K) * U)) (hl' : (U' - K') / ((1 + K') * U') ≤ 1)
    (hx : (1 + K) / U + (1 + K') / U' ≤ 2 * D) :
    aE U' K' (η * 1) (-q ^ (f + 1)) - aE U K (η * -1) (-q ^ f) ≤ -q ^ (f + 1) - -q ^ f := by
  have h1 := aE_sub U' K' (η * 1) (-q ^ (f + 1)) hU' hK'
  have h2 := aE_sub U K (η * -1) (-q ^ f) hU hK
  have hk := key_step q L D η _ _ _ f N hL0 hL1 hq hf hl hl' hx hD hη
  linear_combination h1 - h2 + hk

/-- Binding step before the saving step: `v = q^(N-e) → q^(N-(e+1))`. -/
private lemma key_pre (q L D η U K U' K' : ℝ) (e N : ℕ) (hL0 : 0 < L) (hL1 : L ≤ 1)
    (hq : q = L / 2) (he : e + 1 ≤ N) (hD : 0 < D) (hη : η = q ^ N * L / (4 * D))
    (hU : 0 < U) (hK : 0 ≤ K) (hU' : 0 < U') (hK' : 0 ≤ K')
    (hl : (U - K) / ((1 + K) * U) ≤ 1) (hl' : L ≤ (U' - K') / ((1 + K') * U'))
    (hx : (1 + K) / U + (1 + K') / U' ≤ 2 * D) :
    aE U' K' (η * 1) (q ^ (N - (e + 1))) - aE U K (η * -1) (q ^ (N - e)) ≤
      q ^ (N - (e + 1)) - q ^ (N - e) := by
  have h1 := aE_sub U' K' (η * 1) (q ^ (N - (e + 1))) hU' hK'
  have h2 := aE_sub U K (η * -1) (q ^ (N - e)) hU hK
  have hk := key_step q L D η _ _ _ (N - (e + 1)) N hL0 hL1 hq (by omega) hl' hl hx hD hη
  rw [show N - (e + 1) + 1 = N - e by omega] at hk
  linear_combination h1 - h2 + hk

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

private lemma rlot_end (U S V o a b c : ℝ) (ho : 0 < o) (hS : 0 < S) (hV : V = o * S)
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

private lemma rlot_front (U S V o a b c : ℝ) (ho : 0 < o) (hS : 0 < S) (hV : V = o * S)
    (hcb : 0 < c - b) :
    fval U S V (Rlot o) = 0 ∧ 0 < -(U * a) * Rlot o 0 - S * b * Rlot o 1 + V * c * Rlot o 3 := by
  subst hV
  have ho1 : (0 : ℝ) < 1 + o := by linarith
  simp only [fval, Rlot, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Matrix.cons_val_three]
  constructor
  · field_simp; ring
  · have e : -(U * a) * 0 - S * b * (o / (1 + o)) + o * S * c * (1 / (1 + o)) =
        S * o * (c - b) / (1 + o) := by field_simp; ring
    rw [e]
    exact div_pos (mul_pos (mul_pos hS ho) hcb) ho1

/-- Coordinates of a tight label. -/
private lemma g_pos {m ns : ℕ} {ds : ℝ} (hA : Adm m ns ds) (g τ : ℕ) (hg : g < Jn m ns) :
    0 < lS m ns g τ ∧ lS m ns g τ < lU m ns g τ ∧ 1 < ptV m ns g τ ∧
      0 ≤ cOf (sig ns ds g) * ptV m ns g τ ∧
      cOf (sig ns ds g) * ptV m ns g τ < lS m ns g τ := by
  obtain ⟨hg0, hg1, -, -, -, -⟩ := J_spec hA
  obtain ⟨hSB1, hSBA, hSAU, hSBU, -⟩ := (gadget_lines hA).1 g hg
  obtain ⟨hs0, hs1, hcA, hcB, hVA, hVB, -⟩ := cw_bound hA g hg
  have hc0 : 0 ≤ cOf (sig ns ds g) := by unfold cOf; apply div_nonneg hs0; linarith
  have hSB : 0 < SB m ns g := by linarith
  have hSA : 0 < SA m ns g := by linarith
  unfold lS lU ptV
  split_ifs
  · refine ⟨hSA, hSAU, hVA, by positivity, ?_⟩
    have : cOf (sig ns ds g) * VA m ns g = cOf (sig ns ds g) * wA m ns g * SA m ns g := by
      unfold VA; ring
    rw [this]; nlinarith
  · refine ⟨hSB, hSBU, hVB, by positivity, ?_⟩
    have : cOf (sig ns ds g) * VB m ns g = cOf (sig ns ds g) * wB m ns g * SB m ns g := by
      unfold VB; ring
    rw [this]; nlinarith

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

/-- `A_k → B_k`: equality in `(U, V)`. -/
private lemma nest_AB {m ns : ℕ} {ds : ℝ} (hA : Adm m ns ds) (k : ℕ) (hk : k < Jn m ns)
    (a a' b b' v v' : ℝ) (hd : a' - a ≤ v' - v) :
    (UB m ns k < UA m ns k ∨ (UB m ns k = UA m ns k ∧ a' ≤ a)) ∧
    (SB m ns k < SA m ns k ∨ (SB m ns k = SA m ns k ∧ b' ≤ b)) ∧
    (UB m ns k * VA m ns k < VB m ns k * UA m ns k ∨
      (UB m ns k * VA m ns k = VB m ns k * UA m ns k ∧ a' - a ≤ v' - v)) ∧
    (SB m ns k * VA m ns k < VB m ns k * SA m ns k ∨
      (SB m ns k * VA m ns k = VB m ns k * SA m ns k ∧ b' - b ≤ v' - v)) := by
  obtain ⟨hSB1, hSBA, hSAU, hSBU, hUBA⟩ := (gadget_lines hA).1 k hk
  obtain ⟨tq, tl⟩ := (tight_nest hA).1 k hk
  obtain ⟨-, -, -, -, hVA, -, -⟩ := cw_bound hA k hk
  obtain ⟨hg0, hg1, -, -, -, -⟩ := J_spec hA
  refine ⟨Or.inl hUBA, Or.inl hSBA, Or.inr ⟨by linear_combination (-1 : ℝ) * tq, hd⟩,
    Or.inl ?_⟩
  have hUA : 0 < UA m ns k := by linarith
  refine lt_of_mul_lt_mul_right ?_ hUA.le
  have := mul_lt_mul_of_pos_left tl (by linarith : (0 : ℝ) < VA m ns k)
  linear_combination this - SA m ns k * tq

/-- `B_k → A_{k+1}`: equality in `(S, V)`. -/
private lemma nest_BA {m ns : ℕ} {ds : ℝ} (hA : Adm m ns ds) (k : ℕ) (hk : k + 1 < Jn m ns)
    (a a' b b' v v' : ℝ) (hd : b' - b ≤ v' - v) :
    (UA m ns (k + 1) < UB m ns k ∨ (UA m ns (k + 1) = UB m ns k ∧ a' ≤ a)) ∧
    (SA m ns (k + 1) < SB m ns k ∨ (SA m ns (k + 1) = SB m ns k ∧ b' ≤ b)) ∧
    (UA m ns (k + 1) * VB m ns k < VA m ns (k + 1) * UB m ns k ∨
      (UA m ns (k + 1) * VB m ns k = VA m ns (k + 1) * UB m ns k ∧ a' - a ≤ v' - v)) ∧
    (SA m ns (k + 1) * VB m ns k < VA m ns (k + 1) * SB m ns k ∨
      (SA m ns (k + 1) * VB m ns k = VA m ns (k + 1) * SB m ns k ∧ b' - b ≤ v' - v)) := by
  obtain ⟨hUA', hSA'⟩ := (gadget_lines hA).2 k hk
  obtain ⟨tq, tl, -⟩ := (tight_nest hA).2 k hk
  obtain ⟨hSB1, -⟩ := (gadget_lines hA).1 (k + 1) hk
  obtain ⟨hg0, hg1, -, -, -, -⟩ := J_spec hA
  have hSA0 : 0 < SA m ns (k + 1) := by
    have := (gadget_lines hA).1 (k + 1) hk; linarith [this.2.1]
  refine ⟨Or.inl hUA', Or.inl hSA', Or.inl ?_,
    Or.inr ⟨by linear_combination (-1 : ℝ) * tq, hd⟩⟩
  refine lt_of_mul_lt_mul_right ?_ hSA0.le
  have hVA' := (cw_bound hA (k + 1) hk).2.2.2.2.1
  have := mul_lt_mul_of_pos_left tl (by linarith : (0 : ℝ) < VA m ns (k + 1))
  linear_combination this - UA m ns (k + 1) * tq

/-- Saving step `A_k → A_{k+1}`: strict in every coordinate. -/
private lemma nest_save {m ns : ℕ} {ds : ℝ} (hA : Adm m ns ds) (k : ℕ) (hk : k + 1 < Jn m ns)
    (a a' b b' v v' : ℝ) :
    (UA m ns (k + 1) < UA m ns k ∨ (UA m ns (k + 1) = UA m ns k ∧ a' ≤ a)) ∧
    (SA m ns (k + 1) < SA m ns k ∨ (SA m ns (k + 1) = SA m ns k ∧ b' ≤ b)) ∧
    (UA m ns (k + 1) * VA m ns k < VA m ns (k + 1) * UA m ns k ∨
      (UA m ns (k + 1) * VA m ns k = VA m ns (k + 1) * UA m ns k ∧ a' - a ≤ v' - v)) ∧
    (SA m ns (k + 1) * VA m ns k < VA m ns (k + 1) * SA m ns k ∨
      (SA m ns (k + 1) * VA m ns k = VA m ns (k + 1) * SA m ns k ∧ b' - b ≤ v' - v)) := by
  obtain ⟨hUA', hSA'⟩ := (gadget_lines hA).2 k hk
  obtain ⟨-, hSBA, -, -, hUBA⟩ := (gadget_lines hA).1 k (by omega)
  obtain ⟨-, -, -, -, h5, h6⟩ := (tight_nest hA).2 k hk
  exact ⟨Or.inl (hUA'.trans hUBA), Or.inl (hSA'.trans hSBA), Or.inl h5, Or.inl h6⟩

private lemma skip_lt (j i : ℕ) (h : i < 4 * j + 3) : skipIdx (4 * j + 3) i = i := by
  unfold skipIdx; rw [if_pos h]

private lemma skip_ge (j i : ℕ) (h : 4 * j + 3 ≤ i) : skipIdx (4 * j + 3) i = i + 1 := by
  unfold skipIdx; rw [if_neg (by omega)]

private lemma pt_eq {m ns : ℕ} {ds : ℝ} (j i i' g τ : ℕ) (hs : skipIdx (4 * j + 3) i = i')
    (h1 : 1 ≤ i') (h2 : i' ≤ 4 * Jn m ns) (hg : (i' - 1) / 4 = g) (hτ : (i' - 1) % 4 = τ) :
    Tpt m ns ds (skipIdx (4 * j + 3) i) = gpt m ns ds g τ := by
  rw [hs]; unfold Tpt
  rw [if_neg (by omega), if_neg (by omega), hg, hτ]

private lemma idx_cases (j i : ℕ) : i = 0 ∨ (∃ k, k ≤ j ∧ i = 4 * k + 1) ∨
    (∃ k, k ≤ j ∧ i = 4 * k + 2) ∨ (∃ k, k < j ∧ i = 4 * k + 3) ∨
    (∃ k, k < j ∧ i = 4 * k + 4) ∨ i = 4 * j + 3 ∨ (∃ k, j + 1 ≤ k ∧ i = 4 * k) ∨
    (∃ k, j + 1 ≤ k ∧ i = 4 * k + 1) ∨ (∃ k, j + 1 ≤ k ∧ i = 4 * k + 2) ∨
    (∃ k, j + 1 ≤ k ∧ i = 4 * k + 3) := by
  by_cases h0 : i = 0
  · exact Or.inl h0
  by_cases h1 : i ≤ 4 * j + 2
  · have : (i - 1) % 4 = 0 ∨ (i - 1) % 4 = 1 ∨ (i - 1) % 4 = 2 ∨ (i - 1) % 4 = 3 := by omega
    rcases this with h | h | h | h
    · exact Or.inr (Or.inl ⟨(i - 1) / 4, by omega, by omega⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨(i - 1) / 4, by omega, by omega⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨(i - 1) / 4, by omega, by omega⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨(i - 1) / 4, by omega, by omega⟩))))
  by_cases h3 : i = 4 * j + 3
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h3)))))
  have : i % 4 = 0 ∨ i % 4 = 1 ∨ i % 4 = 2 ∨ i % 4 = 3 := by omega
  refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ?_)))))
  rcases this with h | h | h | h
  · exact Or.inl ⟨i / 4, by omega, by omega⟩
  · exact Or.inr (Or.inl ⟨i / 4, by omega, by omega⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨i / 4, by omega, by omega⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨i / 4, by omega, by omega⟩))

private lemma rot0 (j i : ℕ) (h0 : i ≠ 0) (h3 : i ≠ 4 * j + 3) (ht : tIx j i = 0) :
    r0f j i = -1 ∧ r1f j i = 1 := by
  obtain ⟨a, b⟩ := rot_eval j i 0 h0 h3 ht; norm_num at a b; exact ⟨a, b⟩
private lemma rot1 (j i : ℕ) (h0 : i ≠ 0) (h3 : i ≠ 4 * j + 3) (ht : tIx j i = 1) :
    r0f j i = -1 ∧ r1f j i = -1 := by
  obtain ⟨a, b⟩ := rot_eval j i 1 h0 h3 ht; norm_num at a b; exact ⟨a, b⟩
private lemma rot2 (j i : ℕ) (h0 : i ≠ 0) (h3 : i ≠ 4 * j + 3) (ht : tIx j i = 2) :
    r0f j i = 1 ∧ r1f j i = -1 := by
  obtain ⟨a, b⟩ := rot_eval j i 2 h0 h3 ht; norm_num at a b; exact ⟨a, b⟩
private lemma rot3 (j i : ℕ) (h0 : i ≠ 0) (h3 : i ≠ 4 * j + 3) (ht : tIx j i = 3) :
    r0f j i = -1 ∧ r1f j i = -1 := by
  obtain ⟨a, b⟩ := rot_eval j i 3 h0 h3 ht; norm_num at a b; exact ⟨a, b⟩

private lemma pt_zero {m ns : ℕ} {ds : ℝ} (j : ℕ) :
    Tpt m ns ds (skipIdx (4 * j + 3) 0) = Rlot o0 := by
  rw [skip_lt j 0 (by omega)]; unfold Tpt; rw [if_pos rfl]

private lemma pt_end {m ns : ℕ} {ds : ℝ} (j i : ℕ) (h : 4 * j + 3 ≤ i)
    (he : i + 1 = 4 * Jn m ns + 1) : Tpt m ns ds (skipIdx (4 * j + 3) i) = Rlot (o1 m ns) := by
  rw [skip_ge j i h, he]; unfold Tpt; rw [if_neg (by omega), if_pos rfl]

end

set_option maxHeartbeats 4000000 in
/-- Deleting `yb_j` with `j < J-1` (position `4j+3`) leaves a ranking with a chain. -/
theorem del_yb_mid {m ns : ℕ} {ds : ℝ} (hA : Adm m ns ds) (j : ℕ) (hj : j + 1 < Jn m ns) :
    ∃ W, IsChainFn (4 * Jn m ns + 1) (fun i => Tpt m ns ds (skipIdx (4 * j + 3) i)) W := by
  obtain ⟨hm, h30, hds, hns1⟩ := id hA
  have hns : 1 ≤ ns := by
    rcases Nat.eq_zero_or_pos ns with h | h
    · subst h; simp at h30
    · exact h
  obtain ⟨hg0, hg1, hJ2, -, -, -⟩ := J_spec hA
  have hst : ∀ i, i < 4 * Jn m ns → 0 < sS m ns j i ∧ sS m ns j i < sU m ns j i ∧
      1 < sV m ns j i ∧ 0 ≤ sK m ns ds j i ∧ sK m ns ds j i < sS m ns j i := fun i hi =>
    g_pos hA (gIx j i) (tIx j i) (gIx_lt hj hi)
  have hlam : ∀ i, i < 4 * Jn m ns →
      0 < (sU m ns j i - sK m ns ds j i) / ((1 + sK m ns ds j i) * sU m ns j i) ∧
      (sU m ns j i - sK m ns ds j i) / ((1 + sK m ns ds j i) * sU m ns j i) ≤ 1 ∧
      0 < (sS m ns j i - sK m ns ds j i) / ((1 + sK m ns ds j i) * sS m ns j i) ∧
      (sS m ns j i - sK m ns ds j i) / ((1 + sK m ns ds j i) * sS m ns j i) ≤ 1 := by
    intro i hi
    obtain ⟨hS0, hSU, -, hK0, hKS⟩ := hst i hi
    have hU0 : 0 < sU m ns j i := by linarith
    have d1 : 0 < (1 + sK m ns ds j i) * sU m ns j i := by positivity
    have d2 : 0 < (1 + sK m ns ds j i) * sS m ns j i := by positivity
    refine ⟨div_pos (by linarith) d1, (div_le_one d1).2 (by nlinarith),
      div_pos (by linarith) d2, (div_le_one d2).2 (by nlinarith)⟩
  obtain ⟨L, hL0, hL1, hL⟩ := fin_lower (4 * Jn m ns)
    (fun i => min ((sU m ns j i - sK m ns ds j i) / ((1 + sK m ns ds j i) * sU m ns j i))
      ((sS m ns j i - sK m ns ds j i) / ((1 + sK m ns ds j i) * sS m ns j i)))
    (fun i hi => lt_min (hlam i hi).1 (hlam i hi).2.2.1)
  obtain ⟨D, hD0, hD⟩ := fin_upper (4 * Jn m ns)
    (fun i => (1 + sK m ns ds j i) / sU m ns j i + (1 + sK m ns ds j i) / sS m ns j i)
  obtain ⟨N, hN⟩ : ∃ N : ℕ, N = 2 * Jn m ns := ⟨_, rfl⟩
  obtain ⟨q, hq⟩ : ∃ q : ℝ, q = L / 2 := ⟨_, rfl⟩
  obtain ⟨η, hη⟩ : ∃ η : ℝ, η = q ^ N * L / (4 * D) := ⟨_, rfl⟩
  have hq0 : 0 < q := by rw [hq]; linarith
  have hη0 : 0 < η := by rw [hη]; positivity
  have hF : ∀ i, i < 4 * Jn m ns →
      0 < sS m ns j i ∧ sS m ns j i < sU m ns j i ∧ 0 ≤ sK m ns ds j i ∧
      L ≤ (sU m ns j i - sK m ns ds j i) / ((1 + sK m ns ds j i) * sU m ns j i) ∧
      (sU m ns j i - sK m ns ds j i) / ((1 + sK m ns ds j i) * sU m ns j i) ≤ 1 ∧
      L ≤ (sS m ns j i - sK m ns ds j i) / ((1 + sK m ns ds j i) * sS m ns j i) ∧
      (sS m ns j i - sK m ns ds j i) / ((1 + sK m ns ds j i) * sS m ns j i) ≤ 1 ∧
      (1 + sK m ns ds j i) / sU m ns j i ≤ D ∧ (1 + sK m ns ds j i) / sS m ns j i ≤ D ∧
      0 ≤ (1 + sK m ns ds j i) / sS m ns j i := by
    intro i hi
    obtain ⟨hS0, hSU, -, hK0, -⟩ := hst i hi
    obtain ⟨-, hl1, -, hl2⟩ := hlam i hi
    have h1 := hL i hi
    have h2 := hD i hi
    have p1 : 0 ≤ (1 + sK m ns ds j i) / sU m ns j i := div_nonneg (by linarith) (by linarith)
    have p2 : 0 ≤ (1 + sK m ns ds j i) / sS m ns j i := div_nonneg (by linarith) (by linarith)
    exact ⟨hS0, hSU, hK0, h1.trans (min_le_left _ _), hl1, h1.trans (min_le_right _ _), hl2,
      by linarith, by linarith, p2⟩
  refine strictify (4 * Jn m ns + 1) _ (sU m ns j) (sS m ns j) (sV m ns j)
    (fun i => aE (sU m ns j i) (sK m ns ds j i) (η * r0f j i) (vf q N j i))
    (fun i => aE (sS m ns j i) (sK m ns ds j i) (η * r1f j i) (vf q N j i)) (vf q N j) ?_ ?_ ?_
  · intro i hi
    obtain ⟨a, b, c, -, -⟩ := hst i (by omega)
    exact ⟨a, b, c⟩
  · -- nesting
    intro i hi
    beta_reduce
    rcases idx_cases j i with rfl | ⟨k, hk, rfl⟩ | ⟨k, hk, rfl⟩ | ⟨k, hk, rfl⟩ | ⟨k, hk, rfl⟩ |
      rfl | ⟨k, hk, rfl⟩ | ⟨k, hk, rfl⟩ | ⟨k, hk, rfl⟩ | ⟨k, hk, rfl⟩
    · -- 0 → 1: same line A_0, (1,1) → −+
      have hx0 := ix_eval j 0 0 0 (by omega)
      have hx1 := ix_eval j (0 + 1) 0 0 (by omega)
      obtain ⟨u0, s0, v0, k0⟩ := lblA m ns ds j _ _ _ hx0 (by norm_num)
      obtain ⟨u1, s1, v1, k1⟩ := lblA m ns ds j _ _ _ hx1 (by norm_num)
      have r00 : r0f j 0 = 1 := by simp [r0f]
      have r10 : r1f j 0 = 1 := by simp [r1f]
      obtain ⟨r01, r11⟩ := rot0 j (0 + 1) (by omega) (by omega) hx1.2
      have w0 := vf_pre q N j 0 1 (by omega) (by omega)
      have w1 := vf_pre q N j (0 + 1) 1 (by omega) (by omega)
      obtain ⟨hS, hSU, hK, -⟩ := hF 0 (by omega)
      simp only [u0, s0, k0] at hS hSU hK
      rw [u0, s0, v0, k0, u1, s1, v1, k1, r00, r10, r01, r11, w0, w1]
      exact nest_same (by linarith) hS hK (by linarith) (by linarith)
    · -- 4k+1 → 4k+2: same line A_k, −+ → low
      have hx0 := ix_eval j (4 * k + 1) k 0 (by omega)
      have hx1 := ix_eval j (4 * k + 1 + 1) k 1 (by omega)
      obtain ⟨u0, s0, v0, k0⟩ := lblA m ns ds j _ _ _ hx0 (by norm_num)
      obtain ⟨u1, s1, v1, k1⟩ := lblA m ns ds j _ _ _ hx1 (by norm_num)
      obtain ⟨r0a, r1a⟩ := rot0 j _ (by omega) (by omega) hx0.2
      obtain ⟨r0b, r1b⟩ := rot1 j _ (by omega) (by omega) hx1.2
      have w0 := vf_pre q N j (4 * k + 1) (2 * k + 1) (by omega) (by omega)
      have w1 := vf_pre q N j (4 * k + 1 + 1) (2 * k + 1) (by omega) (by omega)
      obtain ⟨hS, hSU, hK, -⟩ := hF (4 * k + 1) (by omega)
      simp only [u0, s0, k0] at hS hSU hK
      rw [u0, s0, v0, k0, u1, s1, v1, k1, r0a, r1a, r0b, r1b, w0, w1]
      exact nest_same (by linarith) hS hK (by linarith) (by linarith)
    · rcases Nat.lt_or_ge k j with hkj | hkj
      · -- 4k+2 → 4k+3 (k < j): A_k → B_k, pre-saving binding
        have hx0 := ix_eval j (4 * k + 2) k 1 (by omega)
        have hx1 := ix_eval j (4 * k + 2 + 1) k 2 (by omega)
        obtain ⟨u0, s0, v0, k0⟩ := lblA m ns ds j _ _ _ hx0 (by norm_num)
        obtain ⟨u1, s1, v1, k1⟩ := lblB m ns ds j _ _ _ hx1 (by norm_num)
        obtain ⟨r0a, r1a⟩ := rot1 j _ (by omega) (by omega) hx0.2
        obtain ⟨r0b, r1b⟩ := rot2 j _ (by omega) (by omega) hx1.2
        have w0 := vf_pre q N j (4 * k + 2) (2 * k + 1) (by omega) (by omega)
        have w1 := vf_pre q N j (4 * k + 2 + 1) (2 * k + 1 + 1) (by omega) (by omega)
        obtain ⟨hS, hSU, hK, -, hl, -, -, hDU, -⟩ := hF (4 * k + 2) (by omega)
        obtain ⟨hS', hSU', hK', hL', -, -, -, hDU', -⟩ := hF (4 * k + 2 + 1) (by omega)
        simp only [u0, s0, k0] at hS hSU hK hl hDU
        simp only [u1, s1, k1] at hS' hSU' hK' hL' hDU'
        rw [u0, s0, v0, k0, u1, s1, v1, k1, r0a, r1a, r0b, r1b, w0, w1]
        exact nest_AB hA k (by omega) _ _ _ _ _ _
          (key_pre q L D η _ _ _ _ (2 * k + 1) N hL0 hL1 hq (by omega) hD0 hη (by linarith) hK
            (by linarith) hK' hl hL' (by linarith))
      · -- 4j+2 → 4j+3: saving step A_j → A_{j+1}
        have hx0 := ix_eval j (4 * k + 2) j 1 (by omega)
        have hx1 := ix_eval j (4 * k + 2 + 1) (j + 1) 0 (by omega)
        obtain ⟨u0, s0, v0, k0⟩ := lblA m ns ds j _ _ _ hx0 (by norm_num)
        obtain ⟨u1, s1, v1, k1⟩ := lblA m ns ds j _ _ _ hx1 (by norm_num)
        rw [u0, s0, v0, u1, s1, v1]
        exact nest_save hA j hj _ _ _ _ _ _
    · -- 4k+3 → 4k+4 (k < j): same line B_k, +− → low
      have hx0 := ix_eval j (4 * k + 3) k 2 (by omega)
      have hx1 := ix_eval j (4 * k + 3 + 1) k 3 (by omega)
      obtain ⟨u0, s0, v0, k0⟩ := lblB m ns ds j _ _ _ hx0 (by norm_num)
      obtain ⟨u1, s1, v1, k1⟩ := lblB m ns ds j _ _ _ hx1 (by norm_num)
      obtain ⟨r0a, r1a⟩ := rot2 j _ (by omega) (by omega) hx0.2
      obtain ⟨r0b, r1b⟩ := rot3 j _ (by omega) (by omega) hx1.2
      have w0 := vf_pre q N j (4 * k + 3) (2 * k + 2) (by omega) (by omega)
      have w1 := vf_pre q N j (4 * k + 3 + 1) (2 * k + 2) (by omega) (by omega)
      obtain ⟨hS, hSU, hK, -⟩ := hF (4 * k + 3) (by omega)
      simp only [u0, s0, k0] at hS hSU hK
      rw [u0, s0, v0, k0, u1, s1, v1, k1, r0a, r1a, r0b, r1b, w0, w1]
      exact nest_same (by linarith) hS hK (by linarith) (by linarith)
    · -- 4k+4 → 4k+5 (k < j): B_k → A_{k+1}, pre-saving binding
      have hx0 := ix_eval j (4 * k + 4) k 3 (by omega)
      have hx1 := ix_eval j (4 * k + 4 + 1) (k + 1) 0 (by omega)
      obtain ⟨u0, s0, v0, k0⟩ := lblB m ns ds j _ _ _ hx0 (by norm_num)
      obtain ⟨u1, s1, v1, k1⟩ := lblA m ns ds j _ _ _ hx1 (by norm_num)
      obtain ⟨r0a, r1a⟩ := rot3 j _ (by omega) (by omega) hx0.2
      obtain ⟨r0b, r1b⟩ := rot0 j _ (by omega) (by omega) hx1.2
      have w0 := vf_pre q N j (4 * k + 4) (2 * k + 2) (by omega) (by omega)
      have w1 := vf_pre q N j (4 * k + 4 + 1) (2 * k + 2 + 1) (by omega) (by omega)
      obtain ⟨hS, hSU, hK, -, -, -, hl, -, hDS, -⟩ := hF (4 * k + 4) (by omega)
      obtain ⟨hS', hSU', hK', -, -, hL', -, -, hDS', -⟩ := hF (4 * k + 4 + 1) (by omega)
      simp only [u0, s0, k0] at hS hSU hK hl hDS
      simp only [u1, s1, k1] at hS' hSU' hK' hL' hDS'
      rw [u0, s0, v0, k0, u1, s1, v1, k1, r0a, r1a, r0b, r1b, w0, w1]
      exact nest_BA hA k (by omega) _ _ _ _ _ _
        (key_pre q L D η _ _ _ _ (2 * k + 2) N hL0 hL1 hq (by omega) hD0 hη hS hK
          hS' hK' hl hL' (by linarith))
    · -- 4j+3 → 4j+4: same line A_{j+1}, raise → −+
      have hx0 := ix_eval j (4 * j + 3) (j + 1) 0 (by omega)
      have hx1 := ix_eval j (4 * j + 3 + 1) (j + 1) 0 (by omega)
      obtain ⟨u0, s0, v0, k0⟩ := lblA m ns ds j _ _ _ hx0 (by norm_num)
      obtain ⟨u1, s1, v1, k1⟩ := lblA m ns ds j _ _ _ hx1 (by norm_num)
      have r0a : r0f j (4 * j + 3) = 2 := by unfold r0f; rw [if_neg (by omega), if_pos rfl]
      have r1a : r1f j (4 * j + 3) = 2 := by unfold r1f; rw [if_neg (by omega), if_pos rfl]
      obtain ⟨r0b, r1b⟩ := rot0 j _ (by omega) (by omega) hx1.2
      have w0 := vf_post q N j (4 * j + 3) (2 * j + 2) (by omega) (by omega)
      have w1 := vf_post q N j (4 * j + 3 + 1) (2 * j + 2) (by omega) (by omega)
      obtain ⟨hS, hSU, hK, -⟩ := hF (4 * j + 3) (by omega)
      simp only [u0, s0, k0] at hS hSU hK
      rw [u0, s0, v0, k0, u1, s1, v1, k1, r0a, r1a, r0b, r1b, w0, w1]
      exact nest_same (by linarith) hS hK (by linarith) (by linarith)
    · -- 4k → 4k+1 (k > j): same line A_k, −+ → low
      have hx0 := ix_eval j (4 * k) k 0 (by omega)
      have hx1 := ix_eval j (4 * k + 1) k 1 (by omega)
      obtain ⟨u0, s0, v0, k0⟩ := lblA m ns ds j _ _ _ hx0 (by norm_num)
      obtain ⟨u1, s1, v1, k1⟩ := lblA m ns ds j _ _ _ hx1 (by norm_num)
      obtain ⟨r0a, r1a⟩ := rot0 j _ (by omega) (by omega) hx0.2
      obtain ⟨r0b, r1b⟩ := rot1 j _ (by omega) (by omega) hx1.2
      have w0 := vf_post q N j (4 * k) (2 * k) (by omega) (by omega)
      have w1 := vf_post q N j (4 * k + 1) (2 * k) (by omega) (by omega)
      obtain ⟨hS, hSU, hK, -⟩ := hF (4 * k) (by omega)
      simp only [u0, s0, k0] at hS hSU hK
      rw [u0, s0, v0, k0, u1, s1, v1, k1, r0a, r1a, r0b, r1b, w0, w1]
      exact nest_same (by linarith) hS hK (by linarith) (by linarith)
    · -- 4k+1 → 4k+2 (k > j): A_k → B_k, post-saving binding
      have hx0 := ix_eval j (4 * k + 1) k 1 (by omega)
      have hx1 := ix_eval j (4 * k + 1 + 1) k 2 (by omega)
      obtain ⟨u0, s0, v0, k0⟩ := lblA m ns ds j _ _ _ hx0 (by norm_num)
      obtain ⟨u1, s1, v1, k1⟩ := lblB m ns ds j _ _ _ hx1 (by norm_num)
      obtain ⟨r0a, r1a⟩ := rot1 j _ (by omega) (by omega) hx0.2
      obtain ⟨r0b, r1b⟩ := rot2 j _ (by omega) (by omega) hx1.2
      have w0 := vf_post q N j (4 * k + 1) (2 * k) (by omega) (by omega)
      have w1 := vf_post q N j (4 * k + 1 + 1) (2 * k + 1) (by omega) (by omega)
      obtain ⟨hS, hSU, hK, hLU, -, -, -, hDU, -⟩ := hF (4 * k + 1) (by omega)
      obtain ⟨hS', hSU', hK', -, hl', -, -, hDU', -⟩ := hF (4 * k + 1 + 1) (by omega)
      simp only [u0, s0, k0] at hS hSU hK hLU hDU
      simp only [u1, s1, k1] at hS' hSU' hK' hl' hDU'
      rw [u0, s0, v0, k0, u1, s1, v1, k1, r0a, r1a, r0b, r1b, w0, w1]
      exact nest_AB hA k (by omega) _ _ _ _ _ _
        (key_post q L D η _ _ _ _ (2 * k) N hL0 hL1 hq (by omega) hD0 hη (by linarith) hK
          (by linarith) hK' hLU hl' (by linarith))
    · -- 4k+2 → 4k+3 (k > j): same line B_k, +− → low
      have hx0 := ix_eval j (4 * k + 2) k 2 (by omega)
      have hx1 := ix_eval j (4 * k + 2 + 1) k 3 (by omega)
      obtain ⟨u0, s0, v0, k0⟩ := lblB m ns ds j _ _ _ hx0 (by norm_num)
      obtain ⟨u1, s1, v1, k1⟩ := lblB m ns ds j _ _ _ hx1 (by norm_num)
      obtain ⟨r0a, r1a⟩ := rot2 j _ (by omega) (by omega) hx0.2
      obtain ⟨r0b, r1b⟩ := rot3 j _ (by omega) (by omega) hx1.2
      have w0 := vf_post q N j (4 * k + 2) (2 * k + 1) (by omega) (by omega)
      have w1 := vf_post q N j (4 * k + 2 + 1) (2 * k + 1) (by omega) (by omega)
      obtain ⟨hS, hSU, hK, -⟩ := hF (4 * k + 2) (by omega)
      simp only [u0, s0, k0] at hS hSU hK
      rw [u0, s0, v0, k0, u1, s1, v1, k1, r0a, r1a, r0b, r1b, w0, w1]
      exact nest_same (by linarith) hS hK (by linarith) (by linarith)
    · -- 4k+3 → 4k+4 (k > j): B_k → A_{k+1}, post-saving binding
      have hx0 := ix_eval j (4 * k + 3) k 3 (by omega)
      have hx1 := ix_eval j (4 * k + 3 + 1) (k + 1) 0 (by omega)
      obtain ⟨u0, s0, v0, k0⟩ := lblB m ns ds j _ _ _ hx0 (by norm_num)
      obtain ⟨u1, s1, v1, k1⟩ := lblA m ns ds j _ _ _ hx1 (by norm_num)
      obtain ⟨r0a, r1a⟩ := rot3 j _ (by omega) (by omega) hx0.2
      obtain ⟨r0b, r1b⟩ := rot0 j _ (by omega) (by omega) hx1.2
      have w0 := vf_post q N j (4 * k + 3) (2 * k + 1) (by omega) (by omega)
      have w1 := vf_post q N j (4 * k + 3 + 1) (2 * k + 1 + 1) (by omega) (by omega)
      obtain ⟨hS, hSU, hK, -, -, hLS, -, -, hDS, -⟩ := hF (4 * k + 3) (by omega)
      obtain ⟨hS', hSU', hK', -, -, -, hl', -, hDS', -⟩ := hF (4 * k + 3 + 1) (by omega)
      simp only [u0, s0, k0] at hS hSU hK hLS hDS
      simp only [u1, s1, k1] at hS' hSU' hK' hl' hDS'
      rw [u0, s0, v0, k0, u1, s1, v1, k1, r0a, r1a, r0b, r1b, w0, w1]
      exact nest_BA hA k (by omega) _ _ _ _ _ _
        (key_post q L D η _ _ _ _ (2 * k + 1) N hL0 hL1 hq (by omega) hD0 hη hS hK
          hS' hK' hLS hl' (by linarith))
  · -- relations
    intro i hi
    beta_reduce
    rcases idx_cases j i with rfl | ⟨k, hk, rfl⟩ | ⟨k, hk, rfl⟩ | ⟨k, hk, rfl⟩ | ⟨k, hk, rfl⟩ |
      rfl | ⟨k, hk, rfl⟩ | ⟨k, hk, rfl⟩ | ⟨k, hk, rfl⟩ | ⟨k, hk, rfl⟩
    · -- front: R(o_0) and xa_0 against A_0, rotation (1, 1)
      have hJ0 : 0 < Jn m ns := by omega
      have hx0 := ix_eval j 0 0 0 (by omega)
      obtain ⟨u0, s0, v0, k0⟩ := lblA m ns ds j _ _ _ hx0 (by norm_num)
      have r00 : r0f j 0 = 1 := by simp [r0f]
      have r10 : r1f j 0 = 1 := by simp [r1f]
      have w0 := vf_pre q N j 0 1 (by omega) (by omega)
      obtain ⟨hS, hSU, hK, -, -, hLS, -, -, hDS, hPS⟩ := hF 0 (by omega)
      simp only [u0, s0, k0] at hS hSU hK hLS hDS hPS
      rw [u0, s0, v0, k0, r00, r10, pt_zero,
        pt_eq j (0 + 1) (0 + 1) 0 0 (skip_lt j _ (by omega)) (by omega) (by omega) (by omega)
          (by omega)]
      have og := on_gadget hA 0 0 hJ0 (by norm_num) (UA m ns 0) (SA m ns 0) (VA m ns 0)
        rfl rfl rfl (η * 1) (η * 1) (vf q N j 0)
      have hVA : VA m ns 0 = o0 * SA m ns 0 := by unfold VA wA; simp
      have ho : (0 : ℝ) < o0 := by unfold o0; norm_num
      have h1 := aE_sub (SA m ns 0) (cOf (sig ns ds 0) * VA m ns 0) (η * 1) (vf q N j 0) hS hK
      have hk := last_step q L D η _ _ (N - 1) N hL0 hL1 hq (by omega) hLS hDS hPS hD0 hη
      rw [w0] at h1 og ⊢
      have hcb : 0 < q ^ (N - 1) - aE (SA m ns 0) (cOf (sig ns ds 0) * VA m ns 0) (η * 1)
          (q ^ (N - 1)) := by nlinarith
      exact ⟨Or.inr (rlot_front _ _ _ _ _ _ _ ho hS hVA hcb),
        Or.inr ⟨og.1, og.2.2 (by nlinarith)⟩⟩
    · -- 4k+1 (k ≤ j): A_k, −+, xa_k and ya_k on
      have hk' : k < Jn m ns := by omega
      have hx0 := ix_eval j (4 * k + 1) k 0 (by omega)
      obtain ⟨u0, s0, v0, k0⟩ := lblA m ns ds j _ _ _ hx0 (by norm_num)
      obtain ⟨r0a, r1a⟩ := rot0 j _ (by omega) (by omega) hx0.2
      have tb := t_bounds m ns k hm hns
      rw [u0, s0, v0, k0, r0a, r1a,
        pt_eq j (4 * k + 1) (4 * k + 1) k 0 (skip_lt j _ (by omega)) (by omega) (by omega)
          (by omega) (by omega),
        pt_eq j (4 * k + 1 + 1) (4 * k + 1 + 1) k 1 (skip_lt j _ (by omega)) (by omega)
          (by omega) (by omega) (by omega)]
      have o0 := on_gadget hA k 0 hk' (by norm_num) (UA m ns k) (SA m ns k) (VA m ns k)
        rfl rfl rfl (η * -1) (η * 1) (vf q N j (4 * k + 1))
      have o1 := on_gadget hA k 1 hk' (by norm_num) (UA m ns k) (SA m ns k) (VA m ns k)
        rfl rfl rfl (η * -1) (η * 1) (vf q N j (4 * k + 1))
      exact ⟨Or.inr ⟨o0.1, o0.2.1 (by nlinarith [tb.1])⟩,
        Or.inr ⟨o1.1, o1.2.2 (by nlinarith [tb.2.1])⟩⟩
    · -- 4k+2 (k ≤ j): A_k, low, ya_k on; next yb_k (G2a) or, for k = j, xb_j (G2b)
      have hk' : k < Jn m ns := by omega
      have hx0 := ix_eval j (4 * k + 2) k 1 (by omega)
      obtain ⟨u0, s0, v0, k0⟩ := lblA m ns ds j _ _ _ hx0 (by norm_num)
      obtain ⟨r0a, r1a⟩ := rot1 j _ (by omega) (by omega) hx0.2
      rw [u0, s0, v0, k0, r0a, r1a,
        pt_eq j (4 * k + 2) (4 * k + 2) k 1 (skip_lt j _ (by omega)) (by omega) (by omega)
          (by omega) (by omega)]
      have o1 := on_gadget hA k 1 hk' (by norm_num) (UA m ns k) (SA m ns k) (VA m ns k)
        rfl rfl rfl (η * -1) (η * -1) (vf q N j (4 * k + 2))
      refine ⟨Or.inr ⟨o1.1, o1.2.1 (by nlinarith)⟩, ?_⟩
      rcases Nat.lt_or_ge k j with hkj | hkj
      · rw [pt_eq j (4 * k + 2 + 1) (4 * k + 2 + 1) k 2 (skip_lt j _ (by omega)) (by omega)
          (by omega) (by omega) (by omega)]
        exact Or.inl (lifted_rel_gadget hA k hk').1
      · rw [pt_eq j (4 * k + 2 + 1) (4 * k + 2 + 1 + 1) k 3 (skip_ge j _ (by omega))
          (by omega) (by omega) (by omega) (by omega)]
        exact Or.inl (lifted_rel_gadget hA k hk').2.1
    · -- 4k+3 (k < j): B_k, +−, yb_k and xb_k on
      have hk' : k < Jn m ns := by omega
      have hx0 := ix_eval j (4 * k + 3) k 2 (by omega)
      obtain ⟨u0, s0, v0, k0⟩ := lblB m ns ds j _ _ _ hx0 (by norm_num)
      obtain ⟨r0a, r1a⟩ := rot2 j _ (by omega) (by omega) hx0.2
      have tb := t_bounds m ns k hm hns
      rw [u0, s0, v0, k0, r0a, r1a,
        pt_eq j (4 * k + 3) (4 * k + 3) k 2 (skip_lt j _ (by omega)) (by omega) (by omega)
          (by omega) (by omega),
        pt_eq j (4 * k + 3 + 1) (4 * k + 3 + 1) k 3 (skip_lt j _ (by omega)) (by omega)
          (by omega) (by omega) (by omega)]
      have o2 := on_gadget hA k 2 hk' (by norm_num) (UB m ns k) (SB m ns k) (VB m ns k)
        rfl rfl rfl (η * 1) (η * -1) (vf q N j (4 * k + 3))
      have o3 := on_gadget hA k 3 hk' (by norm_num) (UB m ns k) (SB m ns k) (VB m ns k)
        rfl rfl rfl (η * 1) (η * -1) (vf q N j (4 * k + 3))
      exact ⟨Or.inr ⟨o2.1, o2.2.1 (by nlinarith [tb.2.2.1])⟩,
        Or.inr ⟨o3.1, o3.2.2 (by nlinarith [tb.2.2.2])⟩⟩
    · -- 4k+4 (k < j): B_k, low, xb_k on; next xa_{k+1} (G4)
      have hk' : k + 1 < Jn m ns := by omega
      have hx0 := ix_eval j (4 * k + 4) k 3 (by omega)
      obtain ⟨u0, s0, v0, k0⟩ := lblB m ns ds j _ _ _ hx0 (by norm_num)
      obtain ⟨r0a, r1a⟩ := rot3 j _ (by omega) (by omega) hx0.2
      rw [u0, s0, v0, k0, r0a, r1a,
        pt_eq j (4 * k + 4) (4 * k + 4) k 3 (skip_lt j _ (by omega)) (by omega) (by omega)
          (by omega) (by omega),
        pt_eq j (4 * k + 4 + 1) (4 * k + 4 + 1) (k + 1) 0 (skip_lt j _ (by omega)) (by omega)
          (by omega) (by omega) (by omega)]
      have o3 := on_gadget hA k 3 (by omega) (by norm_num) (UB m ns k) (SB m ns k) (VB m ns k)
        rfl rfl rfl (η * -1) (η * -1) (vf q N j (4 * k + 4))
      exact ⟨Or.inr ⟨o3.1, o3.2.1 (by nlinarith)⟩, Or.inl (lifted_rel_trans hA k hk').1⟩
    · -- 4j+3: A_{j+1}, raise; xb_j strictly above (G5b), xa_{j+1} on
      have hx0 := ix_eval j (4 * j + 3) (j + 1) 0 (by omega)
      obtain ⟨u0, s0, v0, k0⟩ := lblA m ns ds j _ _ _ hx0 (by norm_num)
      have r0a : r0f j (4 * j + 3) = 2 := by unfold r0f; rw [if_neg (by omega), if_pos rfl]
      have r1a : r1f j (4 * j + 3) = 2 := by unfold r1f; rw [if_neg (by omega), if_pos rfl]
      rw [u0, s0, v0, k0, r0a, r1a,
        pt_eq j (4 * j + 3) (4 * j + 3 + 1) j 3 (skip_ge j _ (by omega)) (by omega) (by omega)
          (by omega) (by omega),
        pt_eq j (4 * j + 3 + 1) (4 * j + 3 + 1 + 1) (j + 1) 0 (skip_ge j _ (by omega))
          (by omega) (by omega) (by omega) (by omega)]
      have o0 := on_gadget hA (j + 1) 0 hj (by norm_num) (UA m ns (j + 1)) (SA m ns (j + 1))
        (VA m ns (j + 1)) rfl rfl rfl (η * 2) (η * 2) (vf q N j (4 * j + 3))
      exact ⟨Or.inl (lifted_rel_trans hA j hj).2.2.2, Or.inr ⟨o0.1, o0.2.2 (by nlinarith)⟩⟩
    · -- 4k (k > j): A_k, −+, xa_k and ya_k on
      have hk' : k < Jn m ns := by omega
      have hx0 := ix_eval j (4 * k) k 0 (by omega)
      obtain ⟨u0, s0, v0, k0⟩ := lblA m ns ds j _ _ _ hx0 (by norm_num)
      obtain ⟨r0a, r1a⟩ := rot0 j _ (by omega) (by omega) hx0.2
      have tb := t_bounds m ns k hm hns
      rw [u0, s0, v0, k0, r0a, r1a,
        pt_eq j (4 * k) (4 * k + 1) k 0 (skip_ge j _ (by omega)) (by omega) (by omega)
          (by omega) (by omega),
        pt_eq j (4 * k + 1) (4 * k + 1 + 1) k 1 (skip_ge j _ (by omega)) (by omega)
          (by omega) (by omega) (by omega)]
      have o0 := on_gadget hA k 0 hk' (by norm_num) (UA m ns k) (SA m ns k) (VA m ns k)
        rfl rfl rfl (η * -1) (η * 1) (vf q N j (4 * k))
      have o1 := on_gadget hA k 1 hk' (by norm_num) (UA m ns k) (SA m ns k) (VA m ns k)
        rfl rfl rfl (η * -1) (η * 1) (vf q N j (4 * k))
      exact ⟨Or.inr ⟨o0.1, o0.2.1 (by nlinarith [tb.1])⟩,
        Or.inr ⟨o1.1, o1.2.2 (by nlinarith [tb.2.1])⟩⟩
    · -- 4k+1 (k > j): A_k, low, ya_k on; next yb_k (G2a)
      have hk' : k < Jn m ns := by omega
      have hx0 := ix_eval j (4 * k + 1) k 1 (by omega)
      obtain ⟨u0, s0, v0, k0⟩ := lblA m ns ds j _ _ _ hx0 (by norm_num)
      obtain ⟨r0a, r1a⟩ := rot1 j _ (by omega) (by omega) hx0.2
      rw [u0, s0, v0, k0, r0a, r1a,
        pt_eq j (4 * k + 1) (4 * k + 1 + 1) k 1 (skip_ge j _ (by omega)) (by omega) (by omega)
          (by omega) (by omega),
        pt_eq j (4 * k + 1 + 1) (4 * k + 1 + 1 + 1) k 2 (skip_ge j _ (by omega)) (by omega)
          (by omega) (by omega) (by omega)]
      have o1 := on_gadget hA k 1 hk' (by norm_num) (UA m ns k) (SA m ns k) (VA m ns k)
        rfl rfl rfl (η * -1) (η * -1) (vf q N j (4 * k + 1))
      exact ⟨Or.inr ⟨o1.1, o1.2.1 (by nlinarith)⟩, Or.inl (lifted_rel_gadget hA k hk').1⟩
    · -- 4k+2 (k > j): B_k, +−, yb_k and xb_k on
      have hk' : k < Jn m ns := by omega
      have hx0 := ix_eval j (4 * k + 2) k 2 (by omega)
      obtain ⟨u0, s0, v0, k0⟩ := lblB m ns ds j _ _ _ hx0 (by norm_num)
      obtain ⟨r0a, r1a⟩ := rot2 j _ (by omega) (by omega) hx0.2
      have tb := t_bounds m ns k hm hns
      rw [u0, s0, v0, k0, r0a, r1a,
        pt_eq j (4 * k + 2) (4 * k + 2 + 1) k 2 (skip_ge j _ (by omega)) (by omega) (by omega)
          (by omega) (by omega),
        pt_eq j (4 * k + 2 + 1) (4 * k + 2 + 1 + 1) k 3 (skip_ge j _ (by omega)) (by omega)
          (by omega) (by omega) (by omega)]
      have o2 := on_gadget hA k 2 hk' (by norm_num) (UB m ns k) (SB m ns k) (VB m ns k)
        rfl rfl rfl (η * 1) (η * -1) (vf q N j (4 * k + 2))
      have o3 := on_gadget hA k 3 hk' (by norm_num) (UB m ns k) (SB m ns k) (VB m ns k)
        rfl rfl rfl (η * 1) (η * -1) (vf q N j (4 * k + 2))
      exact ⟨Or.inr ⟨o2.1, o2.2.1 (by nlinarith [tb.2.2.1])⟩,
        Or.inr ⟨o3.1, o3.2.2 (by nlinarith [tb.2.2.2])⟩⟩
    · -- 4k+3 (k > j): B_k, low, xb_k on; next xa_{k+1} (G4) or R(o_1)
      have hk' : k < Jn m ns := by omega
      have hx0 := ix_eval j (4 * k + 3) k 3 (by omega)
      obtain ⟨u0, s0, v0, k0⟩ := lblB m ns ds j _ _ _ hx0 (by norm_num)
      obtain ⟨r0a, r1a⟩ := rot3 j _ (by omega) (by omega) hx0.2
      obtain ⟨hS, hSU, hK, -, -, hLS, -, -, hDS, hPS⟩ := hF (4 * k + 3) (by omega)
      simp only [u0, s0, k0] at hS hSU hK hLS hDS hPS
      rw [u0, s0, v0, k0, r0a, r1a,
        pt_eq j (4 * k + 3) (4 * k + 3 + 1) k 3 (skip_ge j _ (by omega)) (by omega) (by omega)
          (by omega) (by omega)]
      have o3 := on_gadget hA k 3 hk' (by norm_num) (UB m ns k) (SB m ns k) (VB m ns k)
        rfl rfl rfl (η * -1) (η * -1) (vf q N j (4 * k + 3))
      refine ⟨Or.inr ⟨o3.1, o3.2.1 (by nlinarith)⟩, ?_⟩
      by_cases hl : k + 1 < Jn m ns
      · rw [pt_eq j (4 * k + 3 + 1) (4 * k + 3 + 1 + 1) (k + 1) 0 (skip_ge j _ (by omega))
          (by omega) (by omega) (by omega) (by omega)]
        exact Or.inl (lifted_rel_trans hA k hl).1
      · have hJe : Jn m ns = k + 1 := by omega
        rw [pt_end j (4 * k + 3 + 1) (by omega) (by omega)]
        have hwB : wB m ns k = o1 m ns := by
          unfold wB o1 wA; rw [hJe, Finset.prod_range_succ]; ring
        have ho1 : 0 < o1 m ns := by
          have := ((w_envelope hA).1 (Jn m ns) le_rfl).1
          unfold o1; unfold o0 at this; linarith
        have hVB : VB m ns k = o1 m ns * SB m ns k := by unfold VB; rw [hwB]
        have hv := vf_post q N j (4 * k + 3) (2 * k + 1) (by omega) (by omega)
        have h1 := aE_sub _ _ (η * -1) (vf q N j (4 * k + 3)) hS hK
        have hk2 := last_step q L D η _ _ (2 * k + 1) N hL0 hL1 hq (by omega) hLS hDS
          hPS hD0 hη
        rw [hv] at h1
        have hcb : vf q N j (4 * k + 3) - aE (SB m ns k) (cOf (sig ns ds k) * VB m ns k)
            (η * -1) (vf q N j (4 * k + 3)) < 0 := by
          rw [hv]; nlinarith
        exact Or.inr (rlot_end _ _ _ _ _ _ _ ho1 hS hVB hcb)

end Q2CL
