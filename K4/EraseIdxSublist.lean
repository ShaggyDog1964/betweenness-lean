import K4.Defs

namespace K4

/-- A strictly shorter sublist misses some position, so it is a sublist of a one-point
deletion.
Sketch: induction on `h : L' <+ L`. `slnil`: impossible (`0 < 0`). `cons a h'` (L' <+ l,
`L = a :: l`): take `k = 0`, `(a :: l).eraseIdx 0 = l`. `cons₂ a h'` (`L' = a :: l'`,
`L = a :: l`, `l'.length < l.length`): by IH `l' <+ l.eraseIdx k` with `k < l.length`;
take `k + 1`, `(a :: l).eraseIdx (k+1) = a :: l.eraseIdx k`, `Sublist.cons₂`. -/
theorem exists_eraseIdx_of_sublist {α : Type*} {L L' : List α} (h : L'.Sublist L)
    (hlt : L'.length < L.length) : ∃ k < L.length, L'.Sublist (L.eraseIdx k) := by
  induction h with
  | slnil => exact absurd hlt (Nat.lt_irrefl 0)
  | cons a h' _ =>
    exact ⟨0, by simp, by simpa using h'⟩
  | cons_cons a h' ih =>
    simp only [List.length_cons] at hlt
    obtain ⟨k, hk, hs⟩ := ih (by omega)
    exact ⟨k + 1, by simp; omega, by simpa using hs.cons_cons a⟩

end K4
