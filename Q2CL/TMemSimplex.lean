import Q2CL.Defs
import Q2CL.CwBound
import Q2CL.JSpec

namespace Q2CL

open K4

private lemma Rlot_mem {o : ℝ} (ho : 0 < o) : Rlot o ∈ Simplex 4 := by
  refine ⟨?_, ?_⟩
  · intro i
    fin_cases i <;> simp [Rlot] <;> positivity
  · simp only [Rlot, Fin.sum_univ_four]
    simp
    field_simp
    ring

private lemma liftPt_mem {s t L V : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hH : 0 < hLift s L V) : liftPt s t L V ∈ Simplex 4 := by
  set H := hLift s L V with hHdef
  have hh0 : 0 ≤ H / (1 + H) := by positivity
  have hh1 : H / (1 + H) ≤ 1 := by
    rw [div_le_one (by linarith)]; linarith
  refine ⟨?_, ?_⟩
  · intro i
    fin_cases i <;> simp only [liftPt, ← hHdef] <;> simp
    · exact mul_nonneg (mul_nonneg (by linarith) (by linarith)) (by linarith)
    · exact mul_nonneg (mul_nonneg (by linarith) (by linarith)) ht0
    · exact mul_nonneg (by linarith) hh0
    · exact hs0
  · simp only [liftPt, ← hHdef, Fin.sum_univ_four]
    simp
    ring

private lemma ptT_mem (m ns j τ : ℕ) (hm : 2 ≤ m) (hns : 1 ≤ ns) :
    0 ≤ ptT m ns j τ ∧ ptT m ns j τ ≤ 1 := by
  obtain ⟨hd0, hd5, hu0, hu1⟩ := (class_trans m ns j hm hns).1
  unfold ptT
  split_ifs
  · unfold fa' fa; constructor <;> nlinarith
  · unfold fb; constructor <;> linarith
  · unfold fb' fb; constructor <;> linarith
  · unfold fa; constructor <;> linarith

/-- Every entry of `T(m, ns, ds)` is a lottery. -/
theorem T_mem_simplex {m ns : ℕ} {ds : ℝ} (hA : Adm m ns ds) :
    ∀ i, i < 4 * Jn m ns + 2 → Tpt m ns ds i ∈ Simplex 4 := by
  intro i hi
  have hm : 2 ≤ m := hA.1
  have hns : 1 ≤ ns := by
    rcases Nat.eq_zero_or_pos ns with h | h
    · subst h; have := hA.2.1; simp at this
    · exact h
  have ho0 : (0 : ℝ) < o0 := by unfold o0; norm_num
  unfold Tpt
  split_ifs with h0 h1
  · exact Rlot_mem ho0
  · have := ((w_envelope hA).1 (Jn m ns) le_rfl).1
    exact Rlot_mem (by unfold o1; linarith)
  · have hj : (i - 1) / 4 < Jn m ns := by omega
    have hτ : (i - 1) % 4 < 4 := Nat.mod_lt _ (by norm_num)
    obtain ⟨hs0, hs1, -, -, -, -, hH⟩ := cw_bound hA _ hj
    have ht := ptT_mem m ns ((i - 1) / 4) ((i - 1) % 4) hm hns
    exact liftPt_mem hs0 (by linarith) ht.1 ht.2 (hH _ hτ)

end Q2CL
