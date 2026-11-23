import Q1.ZzLength
import Q1.ZzGetElem
import Q1.EndMemOrth

namespace Q1

/-- Every non-final entry of the reduced ranking lies in the next chain set. -/
theorem crit_mem {n i : ℕ} (hi : i ≤ n + 1) (t : ℕ)
    (h : t + 1 < ((zigzagList n).eraseIdx i).length) :
    ((zigzagList n).eraseIdx i)[t] ∈ critU i (t + 1) := by
  have hlen0 := zigzagList_length n
  have hlen : ((zigzagList n).eraseIdx i).length = n + 1 := by
    rw [List.length_eraseIdx]; simp [hlen0]; omega
  have htn : t < n := by omega
  rw [List.getElem_eraseIdx]
  split_ifs with hti
  · rw [zigzagList_getElem, if_pos (by omega)]
    left
    rw [Nat.min_eq_left (by omega)]
    exact endPt_mem_orth (Nat.lt_succ_self t)
  · rw [zigzagList_getElem, if_pos (by omega)]
    right
    exact ⟨t + 1, by omega, le_refl _, rfl⟩

end Q1
