/-
# Shared definitions for the base-`b` racetrack (no theorems, no proof holes)

Base-`b` analogues of `K4.ekLot`, `K4.racePt`, `K4.logW`. Everything base-free
(`K4.EK`, `K4.ekSel`, `K4.rtKind`, `K4.rtExp`, `K4.skipIdx`, `K4.LogChain`, `K4.LogCert`,
`K4.rLot`, `K4.vtx`, `K4.dot`) is reused from `K4.Defs` unchanged.
-/
import K4.Defs
import Odds.Statement

namespace Odds

open K4

/-- `ekLotB b K e c` is `lotPB b K c`, `lotQB b K c` or `lotRB b K c`. -/
noncomputable def ekLotB (b : ℝ) (K : ℕ) : EK → ℕ → Lot K
  | EK.P, c => lotPB b K c
  | EK.Q, c => lotQB b K c
  | EK.R, c => lotRB b K c

/-- The `i`-th entry of `racetrackListB b K J` as an explicit function of `i`
(same kinds and exponents as `K4.racePt`). -/
noncomputable def racePtB (b : ℝ) (K J i : ℕ) : Lot K := ekLotB b K (rtKind J i) (rtExp J i)

/-- Base-`b` log tilt vector `(-b^L1, -b^L2, b^L3, b^L4, b^L4 + 1, b^L4 + 2, …)`. -/
noncomputable def logWB (b : ℝ) (K : ℕ) (L1 L2 L3 L4 : ℤ) : Lot K := fun k =>
  if k.val = 0 then -(b ^ L1)
  else if k.val = 1 then -(b ^ L2)
  else if k.val = 2 then b ^ L3
  else b ^ L4 + ((k.val : ℝ) - 3)

end Odds
