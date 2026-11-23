import Q1.Defs

namespace Q1

/-- R(P) is closed under sub-rankings. Sketch: same preference; `List.Pairwise.sublist`. -/
theorem inR_sublist {P : Rel → Prop} {L L' : List Pt} (h : InR P L) (hs : L'.Sublist L) :
    InR P L' := by
  obtain ⟨R, hR, hP, hL⟩ := h
  exact ⟨R, hR, hP, hL.sublist hs⟩

end Q1
