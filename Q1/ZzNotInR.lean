import Q1.ZzStep

namespace Q1

/-- The zigzag ranking is not in R(HVQC).
Sketch: let `R` be an HVQC weak order with `zigzagList n` pairwise strict, `x := a_n`.
From `List.pairwise_append` and `List.pairwise_map` (plus `List.pairwise_iff_getElem` or
`List.Pairwise.rel_of_mem` style lemmas on `List.range (n+1)`): `R a_k a_n` for all
`k ≤ n` (`k < n` from strictness, `k = n` from completeness), and `a_n ≻ p_n`. By
induction on `k ≤ n`, `R p_k a_n`: `p_0 = a_0` (`midPt 0 = endPt 0`), and `zz_step` with
`R a_{k+1} a_n`. So `R p_n a_n`, contradicting `a_n ≻ p_n`. -/
theorem zz_not_inR (n : ℕ) : ¬ InR HVQC (zigzagList n) := by
  rintro ⟨R, hW, hR, hP⟩
  unfold zigzagList at hP
  rw [List.pairwise_append, List.pairwise_map] at hP
  obtain ⟨hA, -, hX⟩ := hP
  have hlast : SPref R (toPt (endPt n)) (toPt (midPt n)) :=
    hX _ (List.mem_map.2 ⟨n, List.mem_range.2 (Nat.lt_succ_self n), rfl⟩) _
      (List.mem_singleton.2 rfl)
  have hA' : ∀ k, k ≤ n → R (toPt (endPt k)) (toPt (endPt n)) := by
    intro k hk
    rcases Nat.lt_or_ge k n with h | h
    · rw [List.pairwise_iff_getElem] at hA
      have := hA k n (by simp; omega) (by simp) h
      simp only [List.getElem_range] at this
      exact this.1
    · have : k = n := by omega
      subst this
      rcases hW.complete (toPt (endPt k)) (toPt (endPt k)) with h' | h' <;> exact h'
  have key : ∀ k, k ≤ n → R (toPt (midPt k)) (toPt (endPt n)) := by
    intro k
    induction k with
    | zero =>
      intro _
      have := hA' 0 (Nat.zero_le _)
      simpa [midPt, endPt] using this
    | succ k ih =>
      intro hk
      exact zz_step hR _ k (ih (by omega)) (hA' (k + 1) hk)
  exact hlast.2 (key n le_rfl)

end Q1
