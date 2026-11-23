import Q1.TripleHQC
import Q1.PairSublist

namespace Q1

/-- Under 3-local data, no entry lies in the horizontal hull of the entries above it.
Sketch: suppose `L[j] ∈ hHull (L.take j)` with witnesses `y, z ∈ L.take j`. If `y = z`,
then `L[j] = y` (`Set.uIcc_self`, `Prod.ext`), so `L[j] ∈ L.take j`; but
`L.take j ++ [L[j]] = L.take (j+1)` (`List.take_concat_get'`) is nodup (sublist of `L`),
contradiction (`List.nodup_append`). If `y ≠ z`, `pair_sublist_of_mem` gives `[y, z]` or
`[z, y]` as a sublist of `L.take j`, so `[y, z, L[j]]` (or `[z, y, L[j]]`) is a sublist of
`L.take j ++ [L[j]] = L.take (j+1) <+ L` (`List.Sublist.append`, `List.take_sublist`) of
length `3`; `hloc` puts it in R(HQC), contradicting `triple_not_inR_hqc` (for the second
order use `Set.uIcc_comm` and `y.2 = z.2` reversed). -/
theorem hHull_avoid {L : List Pt} (hnd : L.Nodup) (hloc : LocallyInR HQC 3 L) :
    ∀ j (h : j < L.length), L[j] ∉ hHull (L.take j) := by
  intro j h ⟨y, hy, z, hz, hyz, hwy, hw1⟩
  have htk : L.take j ++ [L[j]] = L.take (j + 1) := List.take_concat_get' L j h
  have hsub : (L.take j ++ [L[j]]).Sublist L := htk ▸ List.take_sublist _ _
  by_cases hne : y = z
  · subst hne
    rw [Set.uIcc_self, Set.mem_singleton_iff] at hw1
    have heq : L[j] = y := Prod.ext hw1 hwy
    have hnd' : (L.take j ++ [L[j]]).Nodup := hsub.nodup hnd
    rw [List.nodup_append] at hnd'
    exact hnd'.2.2 y hy y (by simp [heq]) rfl
  · rcases pair_sublist_of_mem hy hz hne with hs | hs
    · have h3 : [y, z, L[j]].Sublist L :=
        (hs.append (List.Sublist.refl [L[j]])).trans hsub
      exact triple_not_inR_hqc hyz hwy hw1 (hloc _ h3 (by simp))
    · have h3 : [z, y, L[j]].Sublist L :=
        (hs.append (List.Sublist.refl [L[j]])).trans hsub
      exact triple_not_inR_hqc hyz.symm (hwy.trans hyz) (Set.uIcc_comm y.1 z.1 ▸ hw1)
        (hloc _ h3 (by simp))

end Q1
