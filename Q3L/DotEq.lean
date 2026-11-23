/-
`dot_eq_dotProduct`: the pairing `dot` is Mathlib's `dotProduct`.
-/
import Q3L.Statement

namespace Q3L

open K4 (Lot)

/-- `dot u p` is Mathlib's `dotProduct u p` (both are `∑ k, u k * p k`).
Sketch: `rfl` (unfold `dot`, `dotProduct`). Use it to get linearity for free:
`dotProduct_add`, `dotProduct_sub`, `dotProduct_smul`, `dotProduct_neg`, `add_dotProduct`,
`neg_dotProduct`, `smul_dotProduct`, `dotProduct_zero`. Note also `K4.dot u p = dot u p`
definitionally (same body), so `K4.dot_lt_of_strictFOSD` applies after `show`/`unfold`. -/
theorem dot_eq_dotProduct {K : ℕ} (u p : Lot K) : dot u p = dotProduct u p := by
  rfl

end Q3L
