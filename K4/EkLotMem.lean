import K4.Defs
import K4.EdgeLotsEq
import K4.RLotMem

namespace K4

/-- Every family lottery lies in `Simplex K` when `K ≥ 4`.
Sketch: case on `e`; rewrite with `edge_lots_eq_rLot` and apply `rLot_mem_simplex`
(indices `(0,2)`, `(1,2)`, `(1,3)` are distinct and `< 4 ≤ K`; `2^c ≥ 0`). -/
theorem ekLot_mem_simplex {K : ℕ} (hK : 4 ≤ K) (e : EK) (c : ℕ) :
    ekLot K e c ∈ Simplex K := by
  have hx : (0 : ℝ) ≤ (2 : ℝ) ^ c := pow_nonneg (by norm_num) c
  cases e with
  | P =>
    show lotP K c ∈ Simplex K
    rw [(edge_lots_eq_rLot K c).1]
    exact rLot_mem_simplex (by decide) (by omega) (by omega) hx
  | Q =>
    show lotQ K c ∈ Simplex K
    rw [(edge_lots_eq_rLot K c).2.1]
    exact rLot_mem_simplex (by decide) (by omega) (by omega) hx
  | R =>
    show lotR K c ∈ Simplex K
    rw [(edge_lots_eq_rLot K c).2.2]
    exact rLot_mem_simplex (by decide) (by omega) (by omega) hx

end K4
