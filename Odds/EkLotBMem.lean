import Odds.Defs
import Odds.EdgeLotsBEq
import K4.RLotMem

namespace Odds

open K4

/-- Every base-`b` family lottery lies in `Simplex K` when `K ≥ 4` and `b > 0`.
Sketch: `b ^ c ≥ 0` (`pow_nonneg hb.le`). Case on `e`; rewrite with `edge_lotsB_eq_rLot`
and apply `K4.rLot_mem_simplex` (index pairs `(0,2)`, `(1,2)`, `(1,3)` distinct, `< 4 ≤ K`).
Same as `K4.ekLot_mem_simplex`. -/
theorem ekLotB_mem_simplex {K : ℕ} (hK : 4 ≤ K) {b : ℝ} (hb : 0 < b) (e : EK) (c : ℕ) :
    ekLotB b K e c ∈ Simplex K := by
  have hx : (0 : ℝ) ≤ b ^ c := pow_nonneg hb.le c
  cases e with
  | P =>
    show lotPB b K c ∈ Simplex K
    rw [(edge_lotsB_eq_rLot b K c).1]
    exact rLot_mem_simplex (by decide) (by omega) (by omega) hx
  | Q =>
    show lotQB b K c ∈ Simplex K
    rw [(edge_lotsB_eq_rLot b K c).2.1]
    exact rLot_mem_simplex (by decide) (by omega) (by omega) hx
  | R =>
    show lotRB b K c ∈ Simplex K
    rw [(edge_lotsB_eq_rLot b K c).2.2]
    exact rLot_mem_simplex (by decide) (by omega) (by omega) hx

end Odds
