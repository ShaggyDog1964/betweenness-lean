import K4.Defs
import K4.NodupOfRepresentable

namespace K4

/-- If every one-point deletion of a list of length `≥ 3` is representable, the list has
no repeats.
Sketch: every `L.eraseIdx k` is `Nodup` (`nodup_of_representable`). If `L` had a repeat at
positions `p < q` (`List.nodup_iff_getElem?_ne_getElem?` or `List.nodup_iff_sublist`:
`[a, a] <+ L`), pick `k < L.length` with `k ≠ p`, `k ≠ q` (possible as `3 ≤ L.length`);
then `[a, a] <+ L.eraseIdx k`, contradicting `Nodup`. A concrete alternative: duplicates
avoiding index `0` survive in `L.eraseIdx 0 = L.tail`; those avoiding the last index
survive in `L.eraseIdx (L.length - 1)`; the remaining case `L[0] = L[last]` survives in
`L.eraseIdx 1`. -/
theorem nodup_of_eraseIdx_representable {K : ℕ} (L : List (Lot K)) (hlen : 3 ≤ L.length)
    (h : ∀ k < L.length, Representable (L.eraseIdx k)) : L.Nodup := by
  match L, hlen, h with
  | x :: y :: z :: rest, _, h =>
    have h0 := nodup_of_representable (h 0 (by simp))
    have h1 := nodup_of_representable (h 1 (by simp))
    have h2 := nodup_of_representable (h 2 (by simp))
    simp only [List.eraseIdx_cons_zero, List.eraseIdx_cons_succ] at h0 h1 h2
    simp only [List.nodup_cons, List.mem_cons, not_or] at h0 h1 h2 ⊢
    tauto

end K4
