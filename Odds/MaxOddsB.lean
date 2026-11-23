import Odds.Defs
import Odds.EdgeLotsBEq
import Odds.RacetrackBEqMap
import Odds.OddsLeRLot
import Odds.RtExpLe

namespace Odds

open K4

/-- (B) The largest odds in `X_J^b` are `b^(v0 + Jβ)`.
Sketch. Fix `b > 1`, `K ≥ 4`, `J ≥ 1`; write `N = parV0 J + J * parBeta J`.
Every entry: `rw [racetrackB_eq_map, List.mem_map]` gives `x = racePtB b K J i` with
`i < 4J+2`; unfold `racePtB`, case on `rtKind J i`, rewrite `ekLotB` with
`edge_lotsB_eq_rLot` to `rLot K i' j' (b ^ c)` (`c = rtExp J i`, pair `(0,2)`, `(1,2)` or
`(1,3)`). `1 ≤ b ^ c` (`one_le_pow₀ hb.le`), so by `oddsLe_rLot` the goal is
`b ^ c ≤ b ^ N`, which is `pow_le_pow_right₀ hb.le (rtExp_le J i hi)`. This shows
membership of `b ^ N` in the set.
Lower bound: let `M` be in the set. The last entry `lotRB b K N` belongs to the list
(`racetrackListB` is `[_] ++ _ ++ [lotRB b K N]`, `List.mem_append`, `List.mem_singleton`),
so `OddsLe M (lotRB b K N)`; rewrite to `rLot K 1 3 (b ^ N)` and apply `oddsLe_rLot`
(`1 ≤ b ^ N`) to get `b ^ N ≤ M`. -/
theorem racetrackB_maxOdds : maxOddsB_stmt := by
  intro b hb K hK J _hJ
  have hN1 : (1 : ℝ) ≤ b ^ (parV0 J + J * parBeta J) := one_le_pow₀ hb.le
  constructor
  · intro x hx
    rw [racetrackB_eq_map, List.mem_map] at hx
    obtain ⟨i, hi, rfl⟩ := hx
    rw [List.mem_range] at hi
    have hc1 : (1 : ℝ) ≤ b ^ rtExp J i := one_le_pow₀ hb.le
    have hle : b ^ rtExp J i ≤ b ^ (parV0 J + J * parBeta J) :=
      pow_le_pow_right₀ hb.le (rtExp_le J i hi)
    obtain ⟨eP, eQ, eR⟩ := edge_lotsB_eq_rLot b K (rtExp J i)
    unfold racePtB
    cases rtKind J i with
    | P => rw [ekLotB, eP, oddsLe_rLot (by decide) (by omega) (by omega) hc1]; exact hle
    | Q => rw [ekLotB, eQ, oddsLe_rLot (by decide) (by omega) (by omega) hc1]; exact hle
    | R => rw [ekLotB, eR, oddsLe_rLot (by decide) (by omega) (by omega) hc1]; exact hle
  · intro M hM
    have hmem : lotRB b K (parV0 J + J * parBeta J) ∈ racetrackListB b K J := by
      rw [racetrackListB]
      exact List.mem_append_right _ (List.mem_singleton_self _)
    have h := hM _ hmem
    rw [(edge_lotsB_eq_rLot b K _).2.2, oddsLe_rLot (by decide) (by omega) (by omega) hN1] at h
    exact h

end Odds
