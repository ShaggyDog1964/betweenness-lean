import K4.Defs
import K4.RacetrackEqMap
import K4.EkLotMem

namespace K4

/-- Every racetrack entry is a lottery.
Sketch: `rw [racetrack_eq_map]`, `List.mem_map` gives `x = racePt K J i = ekLot K _ _`;
apply `ekLot_mem_simplex hK`. -/
theorem racetrack_mem_simplex {K : ℕ} (hK : 4 ≤ K) (J : ℕ) :
    ∀ x ∈ racetrackList K J, x ∈ Simplex K := by
  intro x hx
  rw [racetrack_eq_map, List.mem_map] at hx
  obtain ⟨i, -, rfl⟩ := hx
  exact ekLot_mem_simplex hK _ _

end K4
