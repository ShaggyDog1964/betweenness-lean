import Odds.Defs
import Odds.RacetrackBLength
import Odds.ExistsBasePow
import K4.RepresentableSublist
import K4.EraseIdxSublist

namespace Odds

open K4

/-- (A) and (B) imply (C): bounded odds do not bound tests.
Sketch. Given `K ≥ 4`, `M > 1`, `n`, put `J = n + 1` and
`N = parV0 J + J * parBeta J`; `1 ≤ N` (unfold `parV0`, `omega`). `exists_base_pow M hM N`
gives `b > 1` with `b ^ N = M`. Take `L = racetrackListB b K J` and
`hc := hA b hb K hK J (by omega)`.
* `Nodup`, simplex, `¬ Representable`: `hc.1`, `hc.2.1`, `hc.2.2.1`.
* Odds: `(hB b hb K hK J (by omega)).1 x hx : OddsLe (b ^ N) x`; rewrite `b ^ N = M`.
* Locality: for `L' <+ L` with `L'.length ≤ n < 4J + 2 = L.length` (`racetrackB_length`),
  `K4.exists_eraseIdx_of_sublist` gives `k < L.length` with `L' <+ L.eraseIdx k`; finish
  with `K4.representable_sublist` and `hc.2.2.2 k hk`. (Same as `K4.sharp_of_racetrack`.) -/
theorem boundedOdds_of_AB (hA : racetrackB_stmt) (hB : maxOddsB_stmt) :
    boundedOdds_impossibility_stmt := by
  intro K hK M hM n
  have hN : 1 ≤ parV0 (n + 1) + (n + 1) * parBeta (n + 1) := by
    unfold parV0; omega
  obtain ⟨b, hb, hbM⟩ := exists_base_pow M hM _ hN
  have hc := hA b hb K hK (n + 1) (by omega)
  have hO := (hB b hb K hK (n + 1) (by omega)).1
  refine ⟨racetrackListB b K (n + 1), hc.1, hc.2.1, ?_, ?_, hc.2.2.1⟩
  · intro x hx
    have := hO x hx
    rw [hbM] at this
    exact this
  · intro L' hsub hlen
    have hlt : L'.length < (racetrackListB b K (n + 1)).length := by
      rw [racetrackB_length]; omega
    obtain ⟨k, hk, hs⟩ := exists_eraseIdx_of_sublist hsub hlt
    exact representable_sublist hs (hc.2.2.2 k hk)

end Odds
