import K4.Defs

namespace K4

/-- Representability passes to sub-orders. Sketch: same `R`; `List.Pairwise.sublist`. -/
theorem representable_sublist {K : ℕ} {L L' : List (Lot K)} (h : L'.Sublist L)
    (hL : Representable L) : Representable L' := by
  obtain ⟨R, hR, hp⟩ := hL
  exact ⟨R, hR, hp.sublist h⟩

end K4
