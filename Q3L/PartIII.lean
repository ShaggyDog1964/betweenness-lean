/-
`part_iii`: Theorem 36(3), the collinear case.
-/
import Q3L.Statement
import Q3L.LineParam
import Q3L.AtMostTwo
import Q3L.CollinearBinRed

namespace Q3L

/-- Theorem 36(3).
Sketch. Intro `K _ X hXs hdim`. `line_param hdim` gives `x0, d, φ, hrep`. Then
`⟨atMostTwo_of_line hXs hrep, collinear_binaryReduction hXs hrep⟩`. -/
theorem part_iii : part_iii_stmt := by
  intro K _ X hXs hdim
  obtain ⟨x0, d, φ, hrep⟩ := line_param hdim
  exact ⟨atMostTwo_of_line hXs hrep, collinear_binaryReduction hXs hrep⟩

end Q3L
