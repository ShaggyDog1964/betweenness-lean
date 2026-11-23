import Q1.EndMemOrth
import Q1.EndNotMemOrth
import Q1.MidNotMemOrth
import Q1.MidNeEnd

namespace Q1

/-- The zigzag list has no repeats for `n ≥ 1`. (For `n = 0` it is `[a_0, a_0]`.)
Sketch: `List.nodup_append`. Mapped part: `List.Nodup.map_on` with `List.nodup_range`; for
`k < k'`, `a_k ∈ orth k'` (`endPt_mem_orth`) and `a_{k'} ∉ orth k'`
(`endPt_not_mem_orth`), so `a_k ≠ a_{k'}`. Disjointness from `[p_n]`: for `k < n`,
`a_k ∈ orth n ∌ p_n` (`midPt_not_mem_orth`); for `k = n`, `midPt_ne_endPt hn`. -/
theorem zigzagList_nodup {n : ℕ} (hn : 1 ≤ n) : (zigzagList n).Nodup := by
  unfold zigzagList
  rw [List.nodup_append]
  refine ⟨?_, List.nodup_singleton _, ?_⟩
  · refine List.Nodup.map_on ?_ List.nodup_range
    intro k _ k' _ hkk'
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · have h1 := endPt_mem_orth h
      rw [hkk'] at h1
      exact endPt_not_mem_orth _ h1
    · have h1 := endPt_mem_orth h
      rw [← hkk'] at h1
      exact endPt_not_mem_orth _ h1
  · intro a ha b hb
    simp only [List.mem_singleton] at hb
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp ha
    rw [List.mem_range] at hk
    subst hb
    intro heq
    rcases Nat.lt_or_ge k n with h | h
    · have h1 := endPt_mem_orth h
      rw [heq] at h1
      exact midPt_not_mem_orth _ h1
    · have : k = n := by omega
      subst this
      exact midPt_ne_endPt hn heq.symm

end Q1
