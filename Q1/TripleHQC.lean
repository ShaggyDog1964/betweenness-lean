import Q1.Defs

namespace Q1

/-- A point between two better points on a horizontal line cannot be ranked last.
Sketch: from `InR HQC [y, z, w]` get `R` with `y ≻ z`, `y ≻ w`, `z ≻ w`. Apply `HQC` with
`x := z`: `R y z`, `R z z` (completeness), so `R w z`, contradicting `z ≻ w`. -/
theorem triple_not_inR_hqc {y z w : Pt} (h1 : y.2 = z.2) (h2 : w.2 = y.2)
    (h3 : w.1 ∈ Set.uIcc y.1 z.1) : ¬ InR HQC [y, z, w] := by
  rintro ⟨R, hW, hH, hP⟩
  have hyz : SPref R y z := List.rel_of_pairwise_cons hP (by simp)
  have hzw : SPref R z w := List.rel_of_pairwise_cons (List.Pairwise.of_cons hP) (by simp)
  have hzz : R z z := (hW.complete z z).elim id id
  exact hzw.2 (hH z y z w h1 h2 h3 hyz.1 hzz)

end Q1
