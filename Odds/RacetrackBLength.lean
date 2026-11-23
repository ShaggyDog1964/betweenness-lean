import Odds.Defs
import Odds.RacetrackBEqMap

namespace Odds

open K4

/-- The base-`b` racetrack has `4J + 2` entries.
Sketch: `rw [racetrackB_eq_map, List.length_map, List.length_range]`. -/
theorem racetrackB_length (b : ℝ) (K J : ℕ) : (racetrackListB b K J).length = 4 * J + 2 := by
  rw [racetrackB_eq_map, List.length_map, List.length_range]

end Odds
