/-
`isMaxIn_euRel_iff`.
-/
import Q3L.Statement

namespace Q3L

open K4 (Lot)

/-- `x` is the `euRel u`-best element of `A` iff `x ∈ A` and `x` has strictly the largest
`u`-value in `A`.
Sketch. Unfold `IsMaxIn`, `SPref`, `euRel`: `dot u y ≤ dot u x ∧ ¬ dot u x ≤ dot u y ↔
dot u y < dot u x` (`lt_iff_le_not_le` / `not_le`). -/
theorem isMaxIn_euRel_iff {K : ℕ} {u x : Lot K} {A : Finset (Lot K)} :
    IsMaxIn (euRel u) x A ↔ x ∈ A ∧ ∀ y ∈ A, y ≠ x → dot u y < dot u x := by
  unfold IsMaxIn K4.SPref euRel
  constructor
  · rintro ⟨hx, h⟩
    exact ⟨hx, fun y hy hne => lt_of_not_ge (h y hy hne).2⟩
  · rintro ⟨hx, h⟩
    exact ⟨hx, fun y hy hne => ⟨(h y hy hne).le, not_le.mpr (h y hy hne)⟩⟩

end Q3L
