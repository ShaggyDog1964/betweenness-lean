import Q2CL.Defs

namespace Q2CL

open K4

private lemma cls_le (m ns j : ℕ) : cls m ns j ≤ m := by
  unfold cls
  have := Nat.mod_lt (j / ns) (by omega : 0 < m + 1)
  omega

private lemma cls_step (m ns j : ℕ) :
    cls m ns (j + 1) = cls m ns j ∨ (cls m ns j < m ∧ cls m ns (j + 1) = cls m ns j + 1) ∨
      (cls m ns j = m ∧ cls m ns (j + 1) = 0) := by
  unfold cls
  rw [Nat.succ_div]
  split_ifs with h
  · set q := j / ns
    have hq : q + 1 = (q % (m + 1) + 1) + (m + 1) * (q / (m + 1)) := by
      have := Nat.mod_add_div q (m + 1); omega
    have hr := Nat.mod_lt q (by omega : 0 < m + 1)
    rw [hq, Nat.add_mul_mod_self_left]
    rcases Nat.lt_or_ge (q % (m + 1)) m with h1 | h1
    · right; left
      exact ⟨h1, Nat.mod_eq_of_lt (by omega)⟩
    · right; right
      have he : q % (m + 1) = m := by omega
      refine ⟨he, ?_⟩
      rw [he]; exact Nat.mod_self _
  · left; simp

/-- Lemma 73 (types): every gadget lies in the gadget domain and every transition
`j → j+1` is a stay, a step or a wrap. -/
theorem class_trans (m ns j : ℕ) (hm : 2 ≤ m) (hns : 1 ≤ ns) :
    GadDom (uOf m ns j) (dlt m) ∧ TransDom (uOf m ns j) (uOf m ns (j + 1)) (dlt m) := by
  have hmR : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hpos : (0 : ℝ) < 2 * (m : ℝ) + 1 := by linarith
  have hd : dlt m * (2 * (m : ℝ) + 1) = 1 := by
    unfold dlt; field_simp
  have hd0 : 0 < dlt m := by unfold dlt; positivity
  have hd5 : dlt m ≤ 1 / 5 := by nlinarith
  have hi := cls_le m ns j
  have hiR : (cls m ns j : ℝ) ≤ m := by exact_mod_cast hi
  have hi0 : (0 : ℝ) ≤ cls m ns j := Nat.cast_nonneg _
  have hu0 : 0 ≤ uOf m ns j := by unfold uOf; positivity
  have hu1 : uOf m ns j ≤ 1 - dlt m := by
    unfold uOf; nlinarith [mul_nonneg (sub_nonneg.mpr hiR) hd0.le]
  refine ⟨⟨hd0.le, hd5, hu0, hu1⟩, hd0.le, hd5, ?_⟩
  rcases cls_step m ns j with h | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · left; refine ⟨hu0, hu1, ?_⟩; unfold uOf; rw [h]
  · right; left
    have h1' : (cls m ns j : ℝ) + 1 ≤ m := by exact_mod_cast h1
    refine ⟨hu0, ?_, ?_⟩
    · unfold uOf; nlinarith [mul_nonneg (sub_nonneg.mpr h1') hd0.le]
    · unfold uOf; rw [h2]; push_cast; ring
  · right; right
    refine ⟨?_, ?_⟩
    · unfold uOf; rw [h1]; linarith
    · unfold uOf; rw [h2]; simp

end Q2CL
