import Q2CL.Defs
import Q2CL.CwBound
import Q2CL.TLength
import Q2CL.RhoBounds
import Q2CL.WCons

namespace Q2CL

open K4

private lemma gpt_three (m ns : ℕ) (ds : ℝ) (j τ : ℕ) :
    gpt m ns ds j τ 3 = sig ns ds j := by
  simp [gpt, liftPt]

private lemma Rlot_three (o : ℝ) : Rlot o 3 = 1 / (1 + o) := by
  simp [Rlot]

/-- `wA j ≥ o0 (1 + j g / 8)` for `j ≤ J`. -/
private lemma wA_lower {m ns : ℕ} {ds : ℝ} (hA : Adm m ns ds) :
    ∀ j, j ≤ Jn m ns → o0 * (1 + (j : ℝ) * gP m ns / 8) ≤ wA m ns j := by
  obtain ⟨hg0, -, -, hJ, -, -⟩ := J_spec hA
  have hR := (rho_bounds hA).1
  intro j
  induction j with
  | zero => intro _; simp [wA]
  | succ j ih =>
    intro hj
    have hj' : j < Jn m ns := by omega
    have h1 := ih hj'.le
    obtain ⟨hH1, hH4⟩ := hJ j hj'
    have heps : 0 < epsJ m ns j := by
      have hm : 2 ≤ m := hA.1
      have hns : 1 ≤ ns := by
        rcases Nat.eq_zero_or_pos ns with h | h
        · have := hA.2.1; subst h; simp at this
        · exact h
      exact (face_basic _ _ (class_trans m ns j hm hns).1).1
    have hHpos : 0 < Hh m ns j := by nlinarith
    have hr := (hR j hj').1
    have hr8 : 1 + gP m ns / 8 ≤ rho m ns j := by
      have : gP m ns / 8 ≤ gP m ns / (2 * Hh m ns j) := by
        apply div_le_div_of_nonneg_left hg0.le (by linarith) (by linarith)
      linarith
    have hw : wA m ns (j + 1) = wA m ns j * rho m ns j := by
      unfold wA; rw [Finset.prod_range_succ]; ring
    rw [hw]
    have ho0 : (0 : ℝ) < o0 := by unfold o0; norm_num
    have hpos : 0 ≤ o0 * (1 + (j : ℝ) * gP m ns / 8) := by positivity
    have hstep : o0 * (1 + (j : ℝ) * gP m ns / 8) * (1 + gP m ns / 8) ≤
        wA m ns j * rho m ns j := by
      apply mul_le_mul h1 hr8 (by positivity) (le_trans hpos h1)
    push_cast
    have : o0 * (1 + ((j : ℝ) + 1) * gP m ns / 8) ≤
        o0 * (1 + (j : ℝ) * gP m ns / 8) * (1 + gP m ns / 8) := by
      have : 0 ≤ o0 * ((j : ℝ) * gP m ns / 8) * (gP m ns / 8) := by positivity
      nlinarith
    linarith

private lemma o1_lower {m ns : ℕ} {ds : ℝ} (hA : Adm m ns ds) :
    1766 / 1000 ≤ o1 m ns := by
  obtain ⟨hg0, hg1, -, -, -, hstop⟩ := J_spec hA
  have hm : 2 ≤ m := hA.1
  have hns : 1 ≤ ns := by
    rcases Nat.eq_zero_or_pos ns with h | h
    · have := hA.2.1; subst h; simp at this
    · exact h
  have hfb : ∀ k, dJ m ns k < 21 / 10 ∧ 0 < epsJ m ns k ∧ epsJ m ns k < 1 := by
    intro k
    have hF := face_basic _ _ (class_trans m ns k hm hns).1
    exact ⟨hF.2.2.2.2.2.2.2.2.2.2.1, hF.1, hF.2.1⟩
  set J := Jn m ns
  have hsum : ∑ k ∈ Finset.range J, dJ m ns k ≤ 21 / 10 * (J : ℝ) := by
    have := Finset.sum_le_sum (s := Finset.range J) (fun k _ => (hfb k).1.le)
    simpa [mul_comm] using this
  have hH : Hh m ns J = 4 - gP m ns * ∑ k ∈ Finset.range J, dJ m ns k := rfl
  have hgs : gP m ns * ∑ k ∈ Finset.range J, dJ m ns k ≤ gP m ns * (21 / 10 * (J : ℝ)) :=
    mul_le_mul_of_nonneg_left hsum hg0.le
  have hge1 : gP m ns * epsJ m ns J < gP m ns := by
    have := (hfb J).2.2
    nlinarith
  have key : 3 - gP m ns < 21 / 10 * (gP m ns * J) := by
    have : gP m ns * (21 / 10 * (J : ℝ)) = 21 / 10 * (gP m ns * J) := by ring
    linarith
  have hw := wA_lower hA J le_rfl
  have : o1 m ns = wA m ns J := rfl
  rw [this]
  unfold o0 at hw
  nlinarith

private lemma Tpt_slice {m ns : ℕ} {ds : ℝ} (i : ℕ) (h0 : i ≠ 0) (h1 : i ≠ 4 * Jn m ns + 1) :
    Tpt m ns ds i 3 = sig ns ds ((i - 1) / 4) := by
  unfold Tpt; rw [if_neg h0, if_neg h1, gpt_three]

theorem sep_basic {m ns : ℕ} {ds : ℝ} (hA : Adm m ns ds) :
    (∀ j j' τ τ', j < Jn m ns → j' < Jn m ns → sig ns ds j ≠ sig ns ds j' →
      ds ≤ |gpt m ns ds j τ 3 - gpt m ns ds j' τ' 3|) ∧
    (∀ i i', i < 4 * Jn m ns + 2 → i' < 4 * Jn m ns + 2 → i ≠ i' →
      (i = 0 ∨ i = 4 * Jn m ns + 1) →
      ∃ k : Fin 4, 11 / 1000 ≤ |Tpt m ns ds i k - Tpt m ns ds i' k|) := by
  have hds : 0 < ds := hA.2.2.1
  refine ⟨?_, ?_⟩
  · intro j j' τ τ' _ _ hne
    rw [gpt_three, gpt_three]
    unfold sig at hne ⊢
    have hab : j % ns ≠ j' % ns := by
      intro h; apply hne; rw [h]
    have hd : ((j % ns : ℕ) : ℝ) * ds - ((j' % ns : ℕ) : ℝ) * ds =
        (((j % ns : ℕ) : ℝ) - ((j' % ns : ℕ) : ℝ)) * ds := by ring
    rw [hd, abs_mul, abs_of_pos hds]
    have h1 : 1 ≤ |((j % ns : ℕ) : ℝ) - ((j' % ns : ℕ) : ℝ)| := by
      rcases Nat.lt_or_gt_of_ne hab with h | h
      · have : ((j % ns : ℕ) : ℝ) + 1 ≤ ((j' % ns : ℕ) : ℝ) := by exact_mod_cast h
        rw [abs_of_neg (by linarith)]; linarith
      · have : ((j' % ns : ℕ) : ℝ) + 1 ≤ ((j % ns : ℕ) : ℝ) := by exact_mod_cast h
        rw [abs_of_pos (by linarith)]; linarith
    nlinarith
  · intro i i' hi hi' hne hcase
    refine ⟨3, ?_⟩
    have hlo := o1_lower hA
    have hhi := (w_cons hA).1
    have hT0 : Tpt m ns ds 0 3 = 2 / 5 := by
      unfold Tpt; rw [if_pos rfl, Rlot_three]; unfold o0; norm_num
    have hT1 : Tpt m ns ds (4 * Jn m ns + 1) 3 = 1 / (1 + o1 m ns) := by
      unfold Tpt; rw [if_neg (by omega), if_pos rfl, Rlot_three]
    have hpos : 0 < 1 + o1 m ns := by linarith
    have hR1lo : 4 / 29 ≤ 1 / (1 + o1 m ns) := by
      rw [div_le_div_iff₀ (by norm_num) hpos]; linarith
    have hR1hi : 1 / (1 + o1 m ns) ≤ 1000 / 2766 := by
      rw [div_le_div_iff₀ hpos (by norm_num)]; linarith
    -- the other point
    have hother : i' = 0 ∨ i' = 4 * Jn m ns + 1 ∨
        (0 ≤ Tpt m ns ds i' 3 ∧ Tpt m ns ds i' 3 ≤ 1 / 12) := by
      by_cases h0 : i' = 0
      · exact Or.inl h0
      by_cases h1 : i' = 4 * Jn m ns + 1
      · exact Or.inr (Or.inl h1)
      right; right
      rw [Tpt_slice i' h0 h1]
      have hj : (i' - 1) / 4 < Jn m ns := by omega
      have := cw_bound hA _ hj
      exact ⟨this.1, this.2.1⟩
    rcases hcase with rfl | rfl
    · rw [hT0]
      rcases hother with rfl | rfl | ⟨h0, h1⟩
      · exact absurd rfl hne
      · rw [hT1, abs_of_pos (by linarith)]; linarith
      · rw [abs_of_pos (by linarith)]; linarith
    · rw [hT1]
      rcases hother with rfl | rfl | ⟨h0, h1⟩
      · rw [hT0, abs_of_neg (by linarith)]; linarith
      · exact absurd rfl hne
      · rw [abs_of_pos (by linarith)]; linarith

end Q2CL
