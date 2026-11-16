import K4.Defs

namespace K4

/-- A representable list has no repeats. Sketch: `List.Nodup` is `Pairwise (· ≠ ·)`;
`Pairwise.imp`: `SPref R x y → x ≠ y` since `SPref R x x` would need `R x x ∧ ¬ R x x`. -/
theorem nodup_of_representable {K : ℕ} {L : List (Lot K)} (h : Representable L) :
    L.Nodup := by
  obtain ⟨R, _, hp⟩ := h
  refine hp.imp ?_
  rintro x y ⟨h1, h2⟩ rfl
  exact h2 h1

end K4
