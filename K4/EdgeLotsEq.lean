import K4.Defs

namespace K4

/-- The family lotteries are ratio edge lotteries with ratio `2^c`.
Sketch: each is `rfl` after unfolding `lotP`/`lotQ`/`lotR`, `edgeLot`, `rLot`. -/
theorem edge_lots_eq_rLot (K c : ℕ) :
    lotP K c = rLot K 0 2 ((2 : ℝ) ^ c) ∧ lotQ K c = rLot K 1 2 ((2 : ℝ) ^ c) ∧
      lotR K c = rLot K 1 3 ((2 : ℝ) ^ c) := by
  exact ⟨rfl, rfl, rfl⟩

end K4
