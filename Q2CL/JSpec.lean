import Q2CL.Defs
import Q2CL.FaceBasic
import Q2CL.ClassTrans
import Q2CL.Normalization

namespace Q2CL

open K4

/-- Lemma 74 and the recursion stop: `g ≤ 1/75`, `J ≥ 2`, placed gadgets have
`H_j - g ε_j ≥ 1` and `H_j ≤ 4`, `H_J ≥ 24/25`, and `J` really is a stopping index. -/
theorem J_spec {m ns : ℕ} {ds : ℝ} (hA : Adm m ns ds) :
    0 < gP m ns ∧ gP m ns ≤ 1 / 75 ∧ 2 ≤ Jn m ns ∧
    (∀ j, j < Jn m ns → 1 ≤ Hh m ns j - gP m ns * epsJ m ns j ∧ Hh m ns j ≤ 4) ∧
    24 / 25 ≤ Hh m ns (Jn m ns) ∧
    Hh m ns (Jn m ns) - gP m ns * epsJ m ns (Jn m ns) < 1 := by
  obtain ⟨hm, h30, -, -⟩ := hA
  have hns : 1 ≤ ns := by
    rcases Nat.eq_zero_or_pos ns with h | h
    · subst h; simp at h30
    · exact h
  have h30R : (30 : ℝ) ≤ (m : ℝ) ^ 2 * ns := by exact_mod_cast h30
  have hg0 : 0 < gP m ns := by
    have : (0 : ℝ) < (m : ℝ) ^ 2 * ns := by linarith
    unfold gP; apply div_pos (by norm_num); linarith
  have hg1 : gP m ns ≤ 1 / 75 := by
    have : (0 : ℝ) < 5 * (m : ℝ) ^ 2 * ns := by linarith
    unfold gP
    rw [div_le_iff₀ this]; nlinarith
  have hfb : ∀ k, 3 / 2 < dJ m ns k ∧ dJ m ns k < 21 / 10 ∧
      0 < epsJ m ns k ∧ epsJ m ns k < 1 := by
    intro k
    have hF := face_basic _ _ (class_trans m ns k hm hns).1
    exact ⟨hF.2.2.2.2.2.2.2.2.2.1, hF.2.2.2.2.2.2.2.2.2.2.1, hF.1, hF.2.1⟩
  have hstep : ∀ j, Hh m ns (j + 1) = Hh m ns j - gP m ns * dJ m ns j :=
    fun j => (normalization m ns j hm).1
  have hH0 : Hh m ns 0 = 4 := by unfold Hh; simp
  have hHub : ∀ j : ℕ, Hh m ns j ≤ 4 - 3 / 2 * gP m ns * j := by
    intro j
    induction j with
    | zero => rw [hH0]; simp
    | succ n ih =>
      rw [hstep]; push_cast
      have := (hfb n).1
      nlinarith
  have hH4 : ∀ j, Hh m ns j ≤ 4 := by
    intro j; have := hHub j
    have : 0 ≤ 3 / 2 * gP m ns * (j : ℝ) := by positivity
    linarith
  set S := {j : ℕ | Hh m ns j - gP m ns * epsJ m ns j < 1} with hS
  have hne : S.Nonempty := by
    obtain ⟨N, hN⟩ := exists_nat_gt (2 / gP m ns)
    refine ⟨N, ?_⟩
    show Hh m ns N - gP m ns * epsJ m ns N < 1
    have h1 := hHub N
    have h2 : 2 < gP m ns * N := by
      rw [div_lt_iff₀ hg0] at hN; linarith
    have h3 := (hfb N).2.2.1
    have : 0 < gP m ns * epsJ m ns N := mul_pos hg0 h3
    nlinarith
  have hJS : Jn m ns = sInf S := rfl
  have hmem : Jn m ns ∈ S := by rw [hJS]; exact Nat.sInf_mem hne
  have hnot : ∀ j, j < Jn m ns → 1 ≤ Hh m ns j - gP m ns * epsJ m ns j := by
    intro j hj
    rw [hJS] at hj
    have := Nat.notMem_of_lt_sInf hj
    simp only [hS, Set.mem_setOf_eq, not_lt] at this
    exact this
  have hmem' : Hh m ns (Jn m ns) - gP m ns * epsJ m ns (Jn m ns) < 1 := hmem
  have hJ2 : 2 ≤ Jn m ns := by
    by_contra hc
    rw [not_le] at hc
    rcases (show Jn m ns = 0 ∨ Jn m ns = 1 by omega) with h | h
    · rw [h, hH0] at hmem'
      have := (hfb 0).2.2.2
      nlinarith
    · rw [h, hstep, hH0] at hmem'
      have := (hfb 1).2.2.2
      have := (hfb 0).2.1
      nlinarith
  refine ⟨hg0, hg1, hJ2, fun j hj => ⟨hnot j hj, hH4 j⟩, ?_, hmem'⟩
  obtain ⟨k, hk⟩ : ∃ k, Jn m ns = k + 1 := ⟨Jn m ns - 1, by omega⟩
  have hlt : k < Jn m ns := by omega
  have h1 := hnot k hlt
  rw [hk, hstep]
  have := (hfb k).2.1
  have := (hfb k).2.2.1
  nlinarith

end Q2CL
