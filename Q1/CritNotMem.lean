import Q1.ZzLength
import Q1.ZzGetElem
import Q1.EndMemOrth
import Q1.EndNotMemOrth
import Q1.MidNotMemOrth
import Q1.OrthLtEnd
import Q1.OrthLtMid
import Q1.MidNeEnd

namespace Q1

/-- No entry of the reduced ranking lies in the chain set built from the entries above it.
Sketch: length `n + 1`, so `t ≤ n`; entries as in `crit_mem`.
* `t < i`: entry `a_t`; `min t i = t`, `a_t ∉ orth t` (`endPt_not_mem_orth`); the endpoint
  part needs `i < j ≤ t`, impossible.
* `i ≤ t < n`: entry `a_{t+1}`; `min t i = i < t + 1`, so `orth_lt_endPt` excludes it from
  `orth i` (a member would satisfy `a.1 < a.1`). It is no `a_j` with `j ≤ t`, because
  `a_j ∈ orth (t+1)` (`endPt_mem_orth`) and `a_{t+1} ∉ orth (t+1)` (`endPt_not_mem_orth`).
* `t = n` (forces `i ≤ n`): entry `p_n`. Not in `orth i`: if `i < n` by `orth_lt_midPt`,
  if `i = n` by `midPt_not_mem_orth`. Not `a_j` with `i < j ≤ n`: for `j < n`, `a_j ∈ orth n`
  but `p_n ∉ orth n`; for `j = n`, `n > i ≥ 0`, so `n ≥ 1` and `midPt_ne_endPt`. -/
theorem crit_not_mem {n i : ℕ} (hi : i ≤ n + 1) (t : ℕ)
    (h : t < ((zigzagList n).eraseIdx i).length) :
    ((zigzagList n).eraseIdx i)[t] ∉ critU i t := by
  have hL : (zigzagList n).length = n + 2 := zigzagList_length n
  have hlen : ((zigzagList n).eraseIdx i).length = n + 1 := by
    rw [List.length_eraseIdx]; split_ifs <;> omega
  have ht : t ≤ n := by omega
  rw [List.getElem_eraseIdx]
  intro hmem
  rcases hmem with hmem | ⟨j, hij, hjt, hx⟩
  · split_ifs at hmem with hti
    · rw [zigzagList_getElem, if_pos (by omega)] at hmem
      rw [min_eq_left (by omega)] at hmem
      exact endPt_not_mem_orth t hmem
    · rw [min_eq_right (by omega)] at hmem
      rw [zigzagList_getElem] at hmem
      split_ifs at hmem with htn
      · have := orth_lt_endPt (t := i) (j := t + 1) (by omega) _ hmem
        exact lt_irrefl _ this.1
      · rcases Nat.lt_or_ge i n with hin | hin
        · have := orth_lt_midPt (t := i) (j := n) hin _ hmem
          exact lt_irrefl _ this.1
        · have : i = n := by omega
          subst this
          exact midPt_not_mem_orth _ hmem
  · split_ifs at hx with hti
    · omega
    · rw [zigzagList_getElem] at hx
      split_ifs at hx with htn
      · have h1 : toPt (endPt j) ∈ orth (t + 1) := endPt_mem_orth (by omega)
        rw [← hx] at h1
        exact endPt_not_mem_orth _ h1
      · have htn' : t = n := by omega
        subst htn'
        rcases Nat.lt_or_ge j t with hjn | hjn
        · have h1 : toPt (endPt j) ∈ orth t := endPt_mem_orth hjn
          rw [← hx] at h1
          exact midPt_not_mem_orth _ h1
        · have : j = t := by omega
          subst this
          exact midPt_ne_endPt (by omega) hx

end Q1
