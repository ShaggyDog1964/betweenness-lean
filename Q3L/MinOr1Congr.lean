/-
`minOr1_congr`.
-/
import Q3L.Statement

namespace Q3L

open K4 (Lot)

/-- `minOr1 S f` only depends on `f` on `S`.
Sketch. Unfold `minOr1`; `split_ifs`; `Finset.inf'_congr` (or `Finset.inf'_congr rfl h`). -/
theorem minOr1_congr {K : ℕ} {S : Finset (Lot K)} {f f' : Lot K → ℝ}
    (h : ∀ y ∈ S, f y = f' y) : minOr1 S f = minOr1 S f' := by
  unfold minOr1
  split_ifs with hS
  · exact Finset.inf'_congr hS rfl h
  · rfl

end Q3L
