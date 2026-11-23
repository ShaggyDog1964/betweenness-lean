import Q1.ChainWeakOrder
import Q1.ChainPairwise
import Q1.ChainHQC
import Q1.HHullSubset
import Q1.HHullSelf
import Q1.HHullConv
import Q1.HHullAvoid

namespace Q1

/-- (a) for H-QC: R(HQC) is 3-local.
Sketch: given `L` nodup with every sub-ranking of size `≤ 3` in R(HQC), set
`U k := hHull (L.take k)`. Monotone: `hHull_subset` with
`(List.take_sublist_take_left h).subset`. `HConv (U k)`: `hHull_hconv`. Membership
`L[j] ∈ U (j+1)`: `mem_hHull_self`, as `L[j] ∈ L.take (j+1)` (`List.take_concat_get'`,
`List.mem_append`). Non-membership `L[j] ∉ U j`: `hHull_avoid`. Then
`⟨chainRel U, chainRel_weakOrder _, chainRel_hqc _, chainRel_pairwise _ L _ _⟩`. -/
theorem hqc_local_three : IsLocal HQC 3 := by
  intro L hnd hloc
  have hU : Monotone (fun k => hHull (L.take k)) := by
    intro k k' hkk'
    exact hHull_subset (fun x hx => (List.take_sublist_take_left hkk').subset hx)
  refine ⟨chainRel (fun k => hHull (L.take k)), chainRel_weakOrder hU,
    chainRel_hqc (fun k => hHull_hconv _), chainRel_pairwise hU L ?_ ?_⟩
  · intro j h
    apply mem_hHull_self
    rw [← List.take_concat_get' L j (by omega)]
    exact List.mem_append_right _ (List.mem_singleton_self _)
  · intro j h
    exact hHull_avoid hnd hloc j h

end Q1
