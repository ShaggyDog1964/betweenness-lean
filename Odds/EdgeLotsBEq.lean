import Odds.Defs

namespace Odds

open K4

/-- The base-`b` family lotteries are ratio edge lotteries with ratio `b^c`.
Sketch: each conjunct is `rfl` (unfold `lotPB`/`lotQB`/`lotRB`, `edgeLotB`, `K4.rLot`;
`edgeLotB b K i j c` is literally `rLot K i j (b ^ c)`). -/
theorem edge_lotsB_eq_rLot (b : ℝ) (K c : ℕ) :
    lotPB b K c = rLot K 0 2 (b ^ c) ∧ lotQB b K c = rLot K 1 2 (b ^ c) ∧
      lotRB b K c = rLot K 1 3 (b ^ c) := by
  exact ⟨rfl, rfl, rfl⟩

end Odds
