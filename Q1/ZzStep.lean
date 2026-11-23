import Q1.Defs

namespace Q1

/-- One step of the alternating fill: `p_{k+1}` lies between `p_k` and `a_{k+1}` on an
axis-parallel line, so an upper contour set of an HVQC preference containing `p_k` and
`a_{k+1}` contains `p_{k+1}`.
Sketch: `midPt (k+1) = midPt k + h`, `endPt (k+1) = midPt k + 2h`, `h = halfStep (k+1)`.
If `(k+1) % 2 = 0`, `h = (0, k+1)`: first coordinates agree, and the second coordinate of
`p_{k+1}` is `p_k.2 + (k+1) ∈ uIcc p_k.2 (p_k.2 + 2(k+1))`; apply `hR.2` (VQC) with
`y = p_k`, `z = a_{k+1}`, `w = p_{k+1}`. Otherwise `h = (k+1, 0)`: apply `hR.1` (HQC). -/
theorem zz_step {R : Rel} (hR : HVQC R) (x : Pt) (k : ℕ)
    (h1 : R (toPt (midPt k)) x) (h2 : R (toPt (endPt (k + 1))) x) :
    R (toPt (midPt (k + 1))) x := by
  have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  simp only [midPt, endPt] at h2 ⊢
  unfold halfStep at h2 ⊢
  split_ifs at h2 ⊢ with hpar
  · refine hR.2 x _ _ _ ?_ ?_ ?_ h1 h2
    · simp [toPt]
    · simp [toPt]
    · simp only [toPt, Prod.snd_add, Prod.fst_add]
      push_cast
      rw [Set.mem_uIcc]
      left; constructor <;> linarith
  · refine hR.1 x _ _ _ ?_ ?_ ?_ h1 h2
    · simp [toPt]
    · simp [toPt]
    · simp only [toPt, Prod.snd_add, Prod.fst_add]
      push_cast
      rw [Set.mem_uIcc]
      left; constructor <;> linarith

end Q1
