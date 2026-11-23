import Q1.Defs

namespace Q1

/-- Members lie in the hull. Sketch: witnesses `y = z = x`; `Set.left_mem_uIcc`. -/
theorem mem_hHull_self {S : List Pt} {x : Pt} (h : x ∈ S) : x ∈ hHull S :=
  ⟨x, h, x, h, rfl, rfl, Set.left_mem_uIcc⟩

end Q1
