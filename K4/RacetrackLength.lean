import K4.Defs
import K4.RacetrackEqMap

namespace K4

/-- The racetrack list has `4J + 2` entries.
Sketch: `rw [racetrack_eq_map]; simp` (`List.length_map`, `List.length_range`). -/
theorem racetrack_length (K J : ℕ) : (racetrackList K J).length = 4 * J + 2 := by
  rw [racetrack_eq_map, List.length_map, List.length_range]

end K4
