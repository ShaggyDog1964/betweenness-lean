import Odds.Defs
import Odds.RacetrackBEqMap
import Odds.RepresentableOfLogChainB
import K4.EraseIdxMapRange

namespace Odds

open K4

/-- A (base-free) log certificate for deletion `k` makes `(racetrackListB b K J).eraseIdx k`
representable, for every `b > 1`.
Sketch: `rw [racetrackB_eq_map, K4.eraseIdx_map_range _ _ _ hk,
show 4 * J + 2 - 1 = 4 * J + 1 by omega]`; the mapped function is
`fun i => racePtB b K J (skipIdx k i) = ekLotB b K (rtKind J (skipIdx k i))
(rtExp J (skipIdx k i))` (definitional); `LogCert J k u s v w` is by definition the matching
`LogChain`; apply `representable_of_logChainB hK hb`. Same as
`K4.representable_of_logCert`. -/
theorem representable_of_logCertB {K : ℕ} (hK : 4 ≤ K) {b : ℝ} (hb : 1 < b) (J k : ℕ)
    (hk : k < 4 * J + 2) (u s v w : ℕ → ℤ) (h : LogCert J k u s v w) :
    Representable ((racetrackListB b K J).eraseIdx k) := by
  rw [racetrackB_eq_map, eraseIdx_map_range _ _ _ hk,
    show 4 * J + 2 - 1 = 4 * J + 1 by omega]
  exact representable_of_logChainB hK hb (4 * J + 1) (fun i => rtKind J (skipIdx k i))
    (fun i => rtExp J (skipIdx k i)) u s v w h

end Odds
