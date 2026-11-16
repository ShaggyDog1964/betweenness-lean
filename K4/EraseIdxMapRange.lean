import K4.Defs

namespace K4

/-- Deleting position `k` from a mapped range reindexes by `skipIdx k`.
Sketch: `List.range n = List.range k ++ k :: (List.range (n - k - 1)).map (· + k + 1)`
(`List.range_eq_range'`, `List.range'_append`); `List.eraseIdx_append_of_length_le` /
`List.eraseIdx_cons_zero`; or compare by `List.ext_getElem`: lengths `n - 1`
(`List.length_eraseIdx`), and `List.getElem_eraseIdx` gives index `i` for `i < k`, `i + 1`
otherwise, which is `skipIdx k i`. -/
theorem eraseIdx_map_range {α : Type*} (f : ℕ → α) (n k : ℕ) (hk : k < n) :
    ((List.range n).map f).eraseIdx k =
      (List.range (n - 1)).map (fun i => f (skipIdx k i)) := by
  apply List.ext_getElem
  · simp [List.length_eraseIdx, hk]
  · intro i h1 h2
    rw [List.getElem_eraseIdx]
    simp only [List.getElem_map, List.getElem_range, skipIdx]
    split_ifs <;> rfl

end K4
