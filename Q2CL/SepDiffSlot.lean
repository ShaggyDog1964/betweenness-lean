import Q2CL.Defs
import Q2CL.CwBound
import Q2CL.Normalization

namespace Q2CL

open K4

/-- Every slot position is `1/50 + (7/25) k δ_m` (left) or `31/50 + (9/25) k δ_m` (right),
with `k ≤ 2m+1`. -/
private lemma ptT_form (m ns j τ : ℕ) :
    ∃ k : ℕ, k ≤ 2 * m + 1 ∧
      (ptT m ns j τ = 1 / 50 + 7 / 25 * (k : ℝ) * dlt m ∨
        ptT m ns j τ = 31 / 50 + 9 / 25 * (k : ℝ) * dlt m) := by
  have hc : cls m ns j ≤ m := by
    unfold cls
    have := Nat.mod_lt (j / ns) (by omega : 0 < m + 1)
    omega
  have hu : uOf m ns j = 2 * (cls m ns j : ℝ) * dlt m := rfl
  unfold ptT
  split_ifs
  · refine ⟨2 * cls m ns j + 1, by omega, Or.inl ?_⟩
    unfold fa' fa; rw [hu]; push_cast; ring
  · refine ⟨2 * cls m ns j, by omega, Or.inr ?_⟩
    unfold fb; rw [hu]; push_cast; ring
  · refine ⟨2 * cls m ns j + 1, by omega, Or.inr ?_⟩
    unfold fb' fb; rw [hu]; push_cast; ring
  · refine ⟨2 * cls m ns j, by omega, Or.inl ?_⟩
    unfold fa; rw [hu]; push_cast; ring

private lemma nat_gap {k k' : ℕ} (h : (k : ℝ) ≠ (k' : ℝ)) : 1 ≤ |(k : ℝ) - (k' : ℝ)| := by
  have hne : k ≠ k' := fun e => h (by rw [e])
  rcases Nat.lt_or_gt_of_ne hne with h1 | h1
  · have : (k : ℝ) + 1 ≤ (k' : ℝ) := by exact_mod_cast h1
    rw [abs_of_neg (by linarith)]; linarith
  · have : (k' : ℝ) + 1 ≤ (k : ℝ) := by exact_mod_cast h1
    rw [abs_of_pos (by linarith)]; linarith

/-- Distinct slot positions differ by at least `(7/25) δ_m`; all lie in `[0, 1]`. -/
private lemma ptT_sep (m ns j j' τ τ' : ℕ) (hm : 2 ≤ m) :
    0 ≤ ptT m ns j' τ' ∧ ptT m ns j' τ' ≤ 1 ∧
    (ptT m ns j τ ≠ ptT m ns j' τ' → 7 / 25 * dlt m ≤ |ptT m ns j τ - ptT m ns j' τ'|) := by
  have hmR : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hd : dlt m * (2 * (m : ℝ) + 1) = 1 := by unfold dlt; field_simp
  have hd0 : 0 < dlt m := by unfold dlt; positivity
  have hd5 : dlt m ≤ 1 / 5 := by nlinarith
  obtain ⟨k, hk, hk'⟩ := ptT_form m ns j τ
  obtain ⟨l, hl, hl'⟩ := ptT_form m ns j' τ'
  have hkR : (k : ℝ) ≤ 2 * (m : ℝ) + 1 := by exact_mod_cast hk
  have hlR : (l : ℝ) ≤ 2 * (m : ℝ) + 1 := by exact_mod_cast hl
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hl0 : (0 : ℝ) ≤ l := Nat.cast_nonneg l
  have hkd : (k : ℝ) * dlt m ≤ 1 := by nlinarith
  have hld : (l : ℝ) * dlt m ≤ 1 := by nlinarith
  have hkd0 : 0 ≤ (k : ℝ) * dlt m := by positivity
  have hld0 : 0 ≤ (l : ℝ) * dlt m := by positivity
  refine ⟨?_, ?_, ?_⟩
  · rcases hl' with e | e <;> rw [e] <;> nlinarith
  · rcases hl' with e | e <;> rw [e] <;> nlinarith
  intro hne
  rcases hk' with e1 | e1 <;> rcases hl' with e2 | e2 <;> rw [e1, e2] at hne ⊢
  · have hkl : (k : ℝ) ≠ l := by intro h; apply hne; rw [h]
    have h1 := nat_gap hkl
    have : 1 / 50 + 7 / 25 * (k : ℝ) * dlt m - (1 / 50 + 7 / 25 * (l : ℝ) * dlt m) =
        7 / 25 * dlt m * ((k : ℝ) - l) := by ring
    rw [this, abs_mul, abs_of_pos (by positivity)]
    nlinarith
  · rw [abs_of_neg (by nlinarith)]; nlinarith
  · rw [abs_of_pos (by nlinarith)]; nlinarith
  · have hkl : (k : ℝ) ≠ l := by intro h; apply hne; rw [h]
    have h1 := nat_gap hkl
    have : 31 / 50 + 9 / 25 * (k : ℝ) * dlt m - (31 / 50 + 9 / 25 * (l : ℝ) * dlt m) =
        9 / 25 * dlt m * ((k : ℝ) - l) := by ring
    rw [this, abs_mul, abs_of_pos (by positivity)]
    nlinarith

/-- The common factor `(1-s)(1-h)` of coordinates 0 and 1 is at least `80/401`. -/
private lemma kfac_lower {m ns : ℕ} {ds : ℝ} (hA : Adm m ns ds) (h32 : 32 ≤ m ^ 2 * ns)
    (j τ : ℕ) (hj : j < Jn m ns) (hτ : τ < 4) :
    80 / 401 ≤ (1 - sig ns ds j) *
      (1 - hLift (sig ns ds j) (ptL m ns j τ) (ptV m ns j τ) /
        (1 + hLift (sig ns ds j) (ptL m ns j τ) (ptV m ns j τ))) := by
  obtain ⟨hs0, hs1, -, -, hVA, hVB, hpos⟩ := cw_bound hA j hj
  have hh := hpos τ hτ
  obtain ⟨hg0, -, -, hJ, -, -⟩ := J_spec hA
  obtain ⟨-, hH4⟩ := hJ j hj
  have hm : 2 ≤ m := hA.1
  have hns : 1 ≤ ns := by
    rcases Nat.eq_zero_or_pos ns with h | h
    · subst h; simp at h32
    · exact h
  have hF := face_basic _ _ (class_trans m ns j hm hns).1
  have he0 : 0 < epsJ m ns j := hF.1
  have he1 : epsJ m ns j < 1 := hF.2.1
  have h32R : (32 : ℝ) ≤ (m : ℝ) ^ 2 * ns := by exact_mod_cast h32
  have hg80 : gP m ns ≤ 1 / 80 := by
    unfold gP; rw [div_le_iff₀ (by positivity)]; nlinarith
  -- bound on L
  have hL : ptL m ns j τ ≤ 4 + 1 / 80 := by
    unfold ptL
    have := mul_pos hg0 he0
    have : gP m ns * epsJ m ns j ≤ gP m ns := by nlinarith
    split_ifs <;> linarith
  have hV : 1 < ptV m ns j τ := by unfold ptV; split_ifs <;> assumption
  set s := sig ns ds j
  set L := ptL m ns j τ
  set V := ptV m ns j τ
  have hs : 0 < 1 - s := by linarith
  have hc : cOf s = s / (1 - s) := rfl
  have hc0 : 0 ≤ cOf s := by rw [hc]; positivity
  set κ := cOf s * V with hκ
  have hκ0 : 0 ≤ κ := by positivity
  have hhdef : hLift s L V = (L - κ) / (1 + κ) := rfl
  set h := hLift s L V
  have hLκ : κ < L := by
    rw [hhdef] at hh
    have := (div_pos_iff.mp hh)
    rcases this with ⟨a, _⟩ | ⟨_, b⟩
    · linarith
    · linarith
  have h1L : 0 < 1 + L := by linarith
  have e1 : 1 - h / (1 + h) = (1 + κ) / (1 + L) := by
    rw [hhdef]; field_simp; ring
  have e2 : (1 - s) * (1 + κ) = 1 - s + s * V := by
    rw [hκ, hc]; field_simp
  rw [e1, ← mul_div_assoc, e2, div_le_div_iff₀ (by norm_num) h1L]
  nlinarith

private lemma gpt_zero (m ns : ℕ) (ds : ℝ) (j τ : ℕ) :
    gpt m ns ds j τ 0 = (1 - sig ns ds j) *
      (1 - hLift (sig ns ds j) (ptL m ns j τ) (ptV m ns j τ) /
        (1 + hLift (sig ns ds j) (ptL m ns j τ) (ptV m ns j τ))) * (1 - ptT m ns j τ) := by
  simp [gpt, liftPt]

private lemma gpt_one (m ns : ℕ) (ds : ℝ) (j τ : ℕ) :
    gpt m ns ds j τ 1 = (1 - sig ns ds j) *
      (1 - hLift (sig ns ds j) (ptL m ns j τ) (ptV m ns j τ) /
        (1 + hLift (sig ns ds j) (ptL m ns j τ) (ptV m ns j τ))) * ptT m ns j τ := by
  simp [gpt, liftPt]

/-- Separation, same slice and different `t`: `‖p - q‖_∞ ≥ |t - t'|/(1 + L_p)`, and distinct
slot positions differ by `≥ 0.28 δ_m`, so the distance is `≥ (7/25)/((2m+1)(401/80))`. -/
theorem sep_diff_slot {m ns : ℕ} {ds : ℝ} (hA : Adm m ns ds) (h32 : 32 ≤ m ^ 2 * ns) :
    ∀ j j' τ τ', j < Jn m ns → j' < Jn m ns → τ < 4 → τ' < 4 →
      sig ns ds j = sig ns ds j' → ptT m ns j τ ≠ ptT m ns j' τ' →
      ∃ k : Fin 4, (7 / 25) / ((2 * (m : ℝ) + 1) * (401 / 80)) ≤
        |gpt m ns ds j τ k - gpt m ns ds j' τ' k| := by
  intro j j' τ τ' hj hj' hτ _ hs hne
  have hm : 2 ≤ m := hA.1
  obtain ⟨ht0, ht1, hsep⟩ := ptT_sep m ns j j' τ τ' hm
  have hD := hsep hne
  have hkp := kfac_lower hA h32 j τ hj hτ
  have hmR : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hd0 : 0 < dlt m := by unfold dlt; positivity
  have htarget : (7 / 25) / ((2 * (m : ℝ) + 1) * (401 / 80)) = 80 / 401 * (7 / 25 * dlt m) := by
    unfold dlt; field_simp
  rw [htarget]
  have e0 := gpt_zero m ns ds j τ
  have e0' := gpt_zero m ns ds j' τ'
  have e1 := gpt_one m ns ds j τ
  have e1' := gpt_one m ns ds j' τ'
  rw [← hs] at e0' e1'
  set kp := (1 - sig ns ds j) *
      (1 - hLift (sig ns ds j) (ptL m ns j τ) (ptV m ns j τ) /
        (1 + hLift (sig ns ds j) (ptL m ns j τ) (ptV m ns j τ)))
  set kq := (1 - sig ns ds j) *
      (1 - hLift (sig ns ds j) (ptL m ns j' τ') (ptV m ns j' τ') /
        (1 + hLift (sig ns ds j) (ptL m ns j' τ') (ptV m ns j' τ')))
  set t := ptT m ns j τ
  set t' := ptT m ns j' τ'
  have hlow : 80 / 401 * (7 / 25 * dlt m) ≤ kp * |t - t'| := by
    have : 0 ≤ 7 / 25 * dlt m := by positivity
    have : 80 / 401 * (7 / 25 * dlt m) ≤ kp * (7 / 25 * dlt m) :=
      mul_le_mul_of_nonneg_right hkp this
    have : kp * (7 / 25 * dlt m) ≤ kp * |t - t'| :=
      mul_le_mul_of_nonneg_left hD (by linarith)
    linarith
  have hkp0 : 0 ≤ kp := by linarith
  rcases le_total 0 (t - t') with hT | hT <;> rcases le_total 0 (kp - kq) with hK | hK
  · refine ⟨1, ?_⟩
    rw [e1, e1']
    rw [abs_of_nonneg hT] at hlow
    have : kp * (t - t') ≤ kp * t - kq * t' := by nlinarith
    exact le_trans hlow (le_trans this (le_abs_self _))
  · refine ⟨0, ?_⟩
    rw [e0, e0']
    rw [abs_of_nonneg hT] at hlow
    have : kp * (t - t') ≤ -(kp * (1 - t) - kq * (1 - t')) := by nlinarith
    exact le_trans hlow (le_trans this (neg_le_abs _))
  · refine ⟨0, ?_⟩
    rw [e0, e0']
    rw [abs_of_nonpos hT] at hlow
    have : kp * -(t - t') ≤ kp * (1 - t) - kq * (1 - t') := by nlinarith
    exact le_trans hlow (le_trans this (le_abs_self _))
  · refine ⟨1, ?_⟩
    rw [e1, e1']
    rw [abs_of_nonpos hT] at hlow
    have : kp * -(t - t') ≤ -(kp * t - kq * t') := by nlinarith
    exact le_trans hlow (le_trans this (neg_le_abs _))

end Q2CL
