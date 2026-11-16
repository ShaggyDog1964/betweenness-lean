import K4.Defs
import K4.RacetrackLength
import K4.RepresentableSublist
import K4.EraseIdxSublist

namespace K4

/-- (A) implies (B): critical obstructions of unbounded size kill every `LocalComplete K n`.
Sketch: given `K ≥ 4`, `n`, and `hLC : LocalComplete K n`, take `J = n + 1` and
`hc := hA K hK J (by omega)`, `L := racetrackList K J`. `hLC L hc.1 hc.2.1 hloc` would give
`Representable L`, contradicting `hc.2.2.1`. Locality `hloc`: for `L' <+ L` with
`L'.length ≤ n < 4J + 2 = L.length` (`racetrack_length`), `exists_eraseIdx_of_sublist`
gives `k < L.length` with `L' <+ L.eraseIdx k`; `hc.2.2.2 k hk` and `representable_sublist`
finish. -/
theorem sharp_of_racetrack (hA : racetrack_stmt) : sharp_impossibility_stmt := by
  intro K hK n hLC
  have hc := hA K hK (n + 1) (by omega)
  apply hc.2.2.1
  apply hLC _ hc.1 hc.2.1
  intro L' hsub hlen
  have hlt : L'.length < (racetrackList K (n + 1)).length := by
    rw [racetrack_length]; omega
  obtain ⟨k, hk, hs⟩ := exists_eraseIdx_of_sublist hsub hlt
  exact representable_sublist hs (hc.2.2.2 k hk)

end K4
