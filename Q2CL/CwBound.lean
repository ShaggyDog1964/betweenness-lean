import Q2CL.Defs
import Q2CL.WCons
import Q2CL.GadgetLines
import Q2CL.Normalization
import Q2CL.ClassTrans

namespace Q2CL

open K4

private lemma wA_le_of_le {m ns : ℕ} {ds : ℝ} (hA : Adm m ns ds) :
    ∀ j, j ≤ Jn m ns → wA m ns j ≤ wA m ns (Jn m ns) := by
  have hmono := (w_envelope hA).2
  intro j hj
  have key : ∀ d, j + d ≤ Jn m ns → wA m ns j ≤ wA m ns (j + d) := by
    intro d
    induction d with
    | zero => intro _; simp
    | succ d ih =>
      intro hd
      have h1 := ih (by omega)
      have h2 := hmono (j + d) (by omega)
      rw [← add_assoc]; linarith
  have := key (Jn m ns - j) (by omega)
  rwa [show j + (Jn m ns - j) = Jn m ns by omega] at this

private lemma ptT_le_one (m ns j τ : ℕ) (hm : 2 ≤ m) (hns : 1 ≤ ns) : ptT m ns j τ ≤ 1 := by
  obtain ⟨hd0, hd5, hu0, hu1⟩ := (class_trans m ns j hm hns).1
  unfold ptT
  split_ifs
  · unfold fa' fa; linarith
  · unfold fb; linarith
  · unfold fb' fb; linarith
  · unfold fa; linarith

/-- Positivity of the lifted height from a line point. -/
private lemma hLift_pos_core {s U S t w : ℝ} (hc0 : 0 ≤ cOf s) (hS : 0 < S) (hUS : S < U)
    (ht : t ≤ 1) (hw : 0 < w) (hcw : cOf s * w ≤ 25 / 44) :
    0 < hLift s (U * (1 - t) + S * t) (w * S) := by
  unfold hLift
  have hL : S ≤ U * (1 - t) + S * t := by nlinarith
  have hk : cOf s * (w * S) ≤ 25 / 44 * S := by
    rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right hcw hS.le
  have hk0 : 0 ≤ cOf s * (w * S) := by positivity
  apply div_pos <;> linarith

/-- Lemma 74: slices are `≤ 1/12`, `c_j w ≤ 25/44`, tight `V > 1`, lifted heights
are positive. -/
theorem cw_bound {m ns : ℕ} {ds : ℝ} (hA : Adm m ns ds) :
    ∀ j, j < Jn m ns →
      0 ≤ sig ns ds j ∧ sig ns ds j ≤ 1 / 12 ∧
      cOf (sig ns ds j) * wA m ns j ≤ 25 / 44 ∧ cOf (sig ns ds j) * wB m ns j ≤ 25 / 44 ∧
      1 < VA m ns j ∧ 1 < VB m ns j ∧
      ∀ τ, τ < 4 → 0 < hLift (sig ns ds j) (ptL m ns j τ) (ptV m ns j τ) := by
  intro j hj
  obtain ⟨hm, h30, hds, hns1⟩ := id hA
  have hns : 1 ≤ ns := by
    rcases Nat.eq_zero_or_pos ns with h | h
    · subst h; simp at h30
    · exact h
  obtain ⟨-, hg1, -, -, -, -⟩ := J_spec hA
  have ho1 := (w_cons hA).1
  have hE := (w_envelope hA).1
  have hGL := (gadget_lines hA).1 j hj
  obtain ⟨hSB, hSBA, hSAU, hSBU, -⟩ := hGL
  -- slice
  have hmod : j % ns < ns := Nat.mod_lt _ (by omega)
  have hmodR : ((j % ns : ℕ) : ℝ) ≤ (ns : ℝ) - 1 := by
    have : j % ns + 1 ≤ ns := hmod
    have : ((j % ns : ℕ) : ℝ) + 1 ≤ (ns : ℝ) := by exact_mod_cast this
    linarith
  have hs0 : 0 ≤ sig ns ds j := by unfold sig; positivity
  have hs1 : sig ns ds j ≤ 1 / 12 := by
    unfold sig
    have := mul_le_mul_of_nonneg_right hmodR hds.le
    linarith
  -- c
  have hc0 : 0 ≤ cOf (sig ns ds j) := by
    unfold cOf; apply div_nonneg hs0; linarith
  have hc1 : cOf (sig ns ds j) ≤ 1 / 11 := by
    unfold cOf; rw [div_le_iff₀ (by linarith)]; linarith
  -- states
  have hwA0 : 3 / 2 ≤ wA m ns j := by have := (hE j hj.le).1; unfold o0 at this; exact this
  have hwB_eq : wB m ns j = wA m ns (j + 1) := by
    unfold wB wA; rw [Finset.prod_range_succ]; ring
  have hwB0 : 3 / 2 ≤ wB m ns j := by
    have := (hE (j + 1) hj).1; unfold o0 at this; rw [hwB_eq]; exact this
  have hwA1 : wA m ns j ≤ 25 / 4 := by
    have := wA_le_of_le hA j hj.le; unfold o1 at ho1; linarith
  have hwB1 : wB m ns j ≤ 25 / 4 := by
    have := wA_le_of_le hA (j + 1) hj; unfold o1 at ho1; rw [hwB_eq]; linarith
  have hcwA : cOf (sig ns ds j) * wA m ns j ≤ 25 / 44 := by
    have := mul_le_mul hc1 hwA1 (by linarith) (by norm_num); linarith
  have hcwB : cOf (sig ns ds j) * wB m ns j ≤ 25 / 44 := by
    have := mul_le_mul hc1 hwB1 (by linarith) (by norm_num); linarith
  have hSB' : 73 / 75 ≤ SB m ns j := by linarith
  refine ⟨hs0, hs1, hcwA, hcwB, ?_, ?_, ?_⟩
  · unfold VA; nlinarith
  · unfold VB; nlinarith
  · intro τ hτ
    have hN := normalization m ns j hm
    have ht := ptT_le_one m ns j τ hm hns
    rcases lt_or_ge τ 2 with h2 | h2
    · rw [hN.2.2.1 τ h2]
      simp only [ptV, h2, if_true]
      unfold VA
      exact hLift_pos_core hc0 (by linarith) hSAU ht (by linarith) hcwA
    · rw [hN.2.2.2 τ h2 hτ]
      simp only [ptV, show ¬ τ < 2 by omega, if_false]
      unfold VB
      exact hLift_pos_core hc0 (by linarith) hSBU ht (by linarith) hcwB

end Q2CL
