import Q1.Defs

namespace Q1

private lemma hs_bounds (k : ℕ) :
    0 ≤ (halfStep k).1 ∧ 0 ≤ (halfStep k).2 ∧
      (halfStep k).1 ≤ (k : ℤ) ∧ (halfStep k).2 ≤ (k : ℤ) := by
  unfold halfStep
  split_ifs <;> simp

private lemma mid_mono {k m : ℕ} (h : k ≤ m) :
    (midPt k).1 + k ≤ (midPt m).1 + m ∧ (midPt k).2 + k ≤ (midPt m).2 + m := by
  induction m, h using Nat.le_induction with
  | base => exact ⟨le_rfl, le_rfl⟩
  | succ m _ ih =>
    obtain ⟨h1, h2, _, _⟩ := hs_bounds (m + 1)
    simp only [midPt, Prod.fst_add, Prod.snd_add]
    push_cast
    constructor <;> linarith [ih.1, ih.2]

private lemma end_le (k : ℕ) :
    (endPt k).1 ≤ (midPt k).1 + k ∧ (endPt k).2 ≤ (midPt k).2 + k := by
  cases k with
  | zero => simp [endPt, midPt]
  | succ k =>
    obtain ⟨_, _, h3, h4⟩ := hs_bounds (k + 1)
    simp only [endPt, midPt, Prod.fst_add, Prod.snd_add]
    push_cast at h3 h4 ⊢
    constructor <;> linarith

/-- `a_k ∈ orth t` for `k < t`.
Sketch: `t = m + 1`, `k ≤ m`. In each coordinate `i`, `(endPt k).i ≤ (midPt k).i + k`
(`endPt 0 = midPt 0`; `endPt (k+1) = midPt (k+1) + halfStep (k+1)`, whose entries are `0`
or `k + 1`), and `(midPt k).i + k ≤ (midPt m).i + m` because `midPt` coordinates are
nondecreasing. Cast to `ℝ` (`Int.cast_le`). -/
theorem endPt_mem_orth {k t : ℕ} (h : k < t) : toPt (endPt k) ∈ orth t := by
  obtain ⟨m, rfl⟩ : ∃ m, t = m + 1 := ⟨t - 1, by omega⟩
  have hkm : k ≤ m := by omega
  obtain ⟨a1, a2⟩ := end_le k
  obtain ⟨b1, b2⟩ := mid_mono hkm
  have c1 : (endPt k).1 ≤ (midPt m).1 + (m : ℤ) := by linarith
  have c2 : (endPt k).2 ≤ (midPt m).2 + (m : ℤ) := by linarith
  simp only [orth, toPt, Set.mem_ofPred_eq]
  constructor
  · exact_mod_cast c1
  · exact_mod_cast c2

end Q1
