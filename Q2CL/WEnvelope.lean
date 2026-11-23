import Q2CL.Defs
import Q2CL.RhoBounds

namespace Q2CL

open K4

private lemma wA_succ (m ns k : ℕ) : wA m ns (k + 1) = wA m ns k * rho m ns k := by
  unfold wA; rw [Finset.prod_range_succ]; ring

private lemma epsJ_nonneg (m ns j : ℕ) : 0 ≤ epsJ m ns j := by
  unfold epsJ feps fa' fa fb uOf dlt; positivity

private lemma Hh_pos {m ns : ℕ} {ds : ℝ} (hA : Adm m ns ds) :
    ∀ k, k ≤ Jn m ns → 0 < Hh m ns k := by
  obtain ⟨hg0, -, -, hJ, hHJ, -⟩ := J_spec hA
  intro k hk
  rcases lt_or_eq_of_le hk with h | h
  · have h1 := (hJ k h).1
    have h2 := epsJ_nonneg m ns k
    nlinarith [mul_nonneg hg0.le h2]
  · subst h; linarith

/-- Lemma 74: `w_A` is increasing from `o_0` and obeys the height envelope
`w_A(k) ≤ o_0 (4/H_k)^{17/20}` for `k ≤ J`. -/
theorem w_envelope {m ns : ℕ} {ds : ℝ} (hA : Adm m ns ds) :
    (∀ k, k ≤ Jn m ns → o0 ≤ wA m ns k ∧ wA m ns k ≤ o0 * (4 / Hh m ns k) ^ (17 / 20 : ℝ)) ∧
    (∀ k, k < Jn m ns → wA m ns k < wA m ns (k + 1)) := by
  obtain ⟨hg0, -, -, -, -, -⟩ := J_spec hA
  have hR := (rho_bounds hA).1
  have hHp := Hh_pos hA
  have ho0 : (0 : ℝ) < o0 := by unfold o0; norm_num
  -- ρ_k > 1
  have hrho1 : ∀ k, k < Jn m ns → 1 < rho m ns k := by
    intro k hk
    have hH := hHp k hk.le
    have := (hR k hk).1
    have : 0 < gP m ns / (2 * Hh m ns k) := by positivity
    linarith
  -- log ρ_k ≤ β (log H_k - log H_{k+1})
  have hlog : ∀ k, k < Jn m ns →
      Real.log (rho m ns k) ≤ 17 / 20 * (Real.log (Hh m ns k) - Real.log (Hh m ns (k + 1))) := by
    intro k hk
    have hH := hHp k hk.le
    have hH1 := hHp (k + 1) hk
    have hr := hrho1 k hk
    have h1 : Real.log (rho m ns k) ≤ rho m ns k - 1 :=
      Real.log_le_sub_one_of_pos (by linarith)
    have h2 := (hR k hk).2
    have h3 : Real.log (Hh m ns (k + 1) / Hh m ns k) ≤ Hh m ns (k + 1) / Hh m ns k - 1 :=
      Real.log_le_sub_one_of_pos (by positivity)
    rw [Real.log_div hH1.ne' hH.ne'] at h3
    have h4 : (Hh m ns k - Hh m ns (k + 1)) / Hh m ns k = 1 - Hh m ns (k + 1) / Hh m ns k := by
      field_simp
    have h5 : 17 / 20 * (Hh m ns k - Hh m ns (k + 1)) / Hh m ns k
        = 17 / 20 * ((Hh m ns k - Hh m ns (k + 1)) / Hh m ns k) := by ring
    rw [h5, h4] at h2
    linarith
  have hmono : ∀ k, k < Jn m ns → wA m ns k < wA m ns (k + 1) := by
    intro k hk
    have hpos : 0 < wA m ns k := by
      unfold wA
      apply mul_pos ho0
      apply Finset.prod_pos
      intro i hi
      have := hrho1 i (lt_of_lt_of_le (Finset.mem_range.mp hi) hk.le)
      linarith
    rw [wA_succ]
    have := hrho1 k hk
    nlinarith
  have hind : ∀ k, k ≤ Jn m ns → o0 ≤ wA m ns k ∧
      Real.log (wA m ns k) ≤ Real.log o0 + 17 / 20 * (Real.log 4 - Real.log (Hh m ns k)) := by
    intro k
    induction k with
    | zero =>
      intro _
      have : Hh m ns 0 = 4 := by simp [Hh]
      simp [wA, this]
    | succ k ih =>
      intro hk
      have hk' : k < Jn m ns := hk
      obtain ⟨ih1, ih2⟩ := ih hk'.le
      have hr := hrho1 k hk'
      have hwpos : 0 < wA m ns k := lt_of_lt_of_le ho0 ih1
      refine ⟨le_trans ih1 (hmono k hk').le, ?_⟩
      rw [wA_succ, Real.log_mul hwpos.ne' (by linarith)]
      have := hlog k hk'
      linarith
  refine ⟨?_, hmono⟩
  intro k hk
  obtain ⟨h1, h2⟩ := hind k hk
  refine ⟨h1, ?_⟩
  have hH := hHp k hk
  have hwpos : 0 < wA m ns k := lt_of_lt_of_le ho0 h1
  have hq : 0 < 4 / Hh m ns k := by positivity
  rw [Real.rpow_def_of_pos hq, Real.log_div (by norm_num) hH.ne']
  calc wA m ns k = Real.exp (Real.log (wA m ns k)) := (Real.exp_log hwpos).symm
    _ ≤ Real.exp (Real.log o0 + 17 / 20 * (Real.log 4 - Real.log (Hh m ns k))) :=
        Real.exp_le_exp.mpr h2
    _ = o0 * Real.exp ((Real.log 4 - Real.log (Hh m ns k)) * (17 / 20)) := by
        rw [Real.exp_add, Real.exp_log ho0]; ring_nf

end Q2CL
