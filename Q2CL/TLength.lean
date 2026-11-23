import Q2CL.Defs
import Q2CL.JSpec
import Q2CL.FaceBasic
import Q2CL.ClassTrans

namespace Q2CL

open K4

/-- Size (a cruder uniform version of Lemma 81): `n(T) > (100/7) m² ns`, from
`d < 21/10`, `ε < 1`. -/
theorem T_length {m ns : ℕ} {ds : ℝ} (hA : Adm m ns ds) :
    (100 / 7 : ℝ) * (m : ℝ) ^ 2 * ns < ((Tlist m ns ds).length : ℝ) := by
  obtain ⟨hg0, -, -, -, -, hstop⟩ := J_spec hA
  obtain ⟨hm, h30, -, -⟩ := hA
  have hns : 1 ≤ ns := by
    rcases Nat.eq_zero_or_pos ns with h | h
    · subst h; simp at h30
    · exact h
  have hfb : ∀ k, dJ m ns k < 21 / 10 ∧ 0 < epsJ m ns k ∧ epsJ m ns k < 1 := by
    intro k
    have hF := face_basic _ _ (class_trans m ns k hm hns).1
    exact ⟨hF.2.2.2.2.2.2.2.2.2.2.1, hF.1, hF.2.1⟩
  have hlen : ((Tlist m ns ds).length : ℝ) = 4 * (Jn m ns : ℝ) + 2 := by
    unfold Tlist; simp
  rw [hlen]
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
  have hN : (0 : ℝ) < (m : ℝ) ^ 2 * ns := by
    have : (30 : ℝ) ≤ (m : ℝ) ^ 2 * ns := by exact_mod_cast h30
    linarith
  have hgN : gP m ns * ((m : ℝ) ^ 2 * ns) = 2 / 5 := by
    unfold gP; field_simp
  have key2 := mul_lt_mul_of_pos_right key hN
  have e1 : 21 / 10 * (gP m ns * J) * ((m : ℝ) ^ 2 * ns) = 21 / 10 * (J : ℝ) * (2 / 5) := by
    rw [← hgN]; ring
  have e2 : (3 - gP m ns) * ((m : ℝ) ^ 2 * ns) = 3 * ((m : ℝ) ^ 2 * ns) - 2 / 5 := by
    rw [sub_mul, hgN]
  rw [e1, e2] at key2
  have : (100 / 7 : ℝ) * (m : ℝ) ^ 2 * ns = 100 / 7 * ((m : ℝ) ^ 2 * ns) := by ring
  rw [this]
  linarith

end Q2CL
