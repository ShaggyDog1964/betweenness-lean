import Odds.Defs
import Odds.RacetrackBEqMap
import Odds.EkLotBMem

namespace Odds

open K4

/-- Every entry of the base-`b` racetrack is a lottery.
Sketch: `rw [racetrackB_eq_map, List.mem_map]` gives `x = racePtB b K J i`, which unfolds to
`ekLotB b K _ _`; apply `ekLotB_mem_simplex hK hb`. -/
theorem racetrackB_mem_simplex {K : ℕ} (hK : 4 ≤ K) {b : ℝ} (hb : 0 < b) (J : ℕ) :
    ∀ x ∈ racetrackListB b K J, x ∈ Simplex K := by
  intro x hx
  rw [racetrackB_eq_map, List.mem_map] at hx
  obtain ⟨i, -, rfl⟩ := hx
  exact ekLotB_mem_simplex hK hb _ _

end Odds
