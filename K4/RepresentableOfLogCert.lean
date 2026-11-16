import K4.Defs
import K4.RacetrackEqMap
import K4.EraseIdxMapRange
import K4.RepresentableOfLogChain

namespace K4

/-- A log certificate for deletion `k` makes `(racetrackList K J).eraseIdx k`
representable.
Sketch: `rw [racetrack_eq_map, eraseIdx_map_range _ _ _ hk]`; `4 * J + 2 - 1 = 4 * J + 1`;
the mapped function is `fun i => ekLot K (rtKind J (skipIdx k i)) (rtExp J (skipIdx k i))`
(unfold `racePt`); `LogCert` unfolds to the matching `LogChain`; apply
`representable_of_logChain hK`. -/
theorem representable_of_logCert {K : ℕ} (hK : 4 ≤ K) (J k : ℕ) (hk : k < 4 * J + 2)
    (u s v w : ℕ → ℤ) (h : LogCert J k u s v w) :
    Representable ((racetrackList K J).eraseIdx k) := by
  rw [racetrack_eq_map, eraseIdx_map_range _ _ _ hk,
    show 4 * J + 2 - 1 = 4 * J + 1 by omega]
  exact representable_of_logChain hK (4 * J + 1) (fun i => rtKind J (skipIdx k i))
    (fun i => rtExp J (skipIdx k i)) u s v w h

end K4
