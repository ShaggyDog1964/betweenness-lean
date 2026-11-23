import Q1.InRSwap

namespace Q1

/-- V-QC and H-QC have the same locality.
Sketch: (←) let `L` be nodup with `LocallyInR VQC n L`, and `M = L.map Prod.swap` (nodup:
`List.Nodup.map Prod.swap_injective`). For `L' <+ M` with `L'.length ≤ n`:
`L'.map swap <+ M.map swap = L` (`List.Sublist.map`, `List.map_map`,
`Prod.swap_swap_eq`, `List.map_id`), same length, so it is in R(VQC), hence by
`inR_vqc_iff_swap` `(L'.map swap).map swap = L'` is in R(HQC). So `M` is in R(HQC) by
the H-QC locality, i.e. `L` is in R(VQC) by `inR_vqc_iff_swap`. (→) symmetric, using
`inR_vqc_iff_swap` on `L.map swap` and `Prod.swap_swap_eq`. -/
theorem isLocal_vqc_iff (n : ℕ) : IsLocal VQC n ↔ IsLocal HQC n := by
  have hss : ∀ L : List Pt, (L.map Prod.swap).map Prod.swap = L := by
    intro L; simp [List.map_map]
  constructor
  · intro hV L hL hloc
    have hM : InR VQC (L.map Prod.swap) := by
      apply hV _ (hL.map Prod.swap_injective)
      intro L' hsub hlen
      rw [inR_vqc_iff_swap]
      apply hloc
      · have := hsub.map Prod.swap
        rwa [hss] at this
      · simpa using hlen
    rw [inR_vqc_iff_swap, hss] at hM
    exact hM
  · intro hH L hL hloc
    rw [inR_vqc_iff_swap]
    apply hH _ (hL.map Prod.swap_injective)
    intro L' hsub hlen
    have h1 : InR VQC (L'.map Prod.swap) := by
      apply hloc
      · have := hsub.map Prod.swap
        rwa [hss] at this
      · simpa using hlen
    rw [inR_vqc_iff_swap, hss] at h1
    exact h1

end Q1
