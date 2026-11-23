import Q1.Defs

namespace Q1

/-- If every set of the chain is horizontally convex, the chain preference is H-QC.
Sketch: given `chainRel U y x`, `chainRel U z x` and `w` between `y`, `z` on a horizontal
line, for each `k` with `x ∈ U k` both `y, z ∈ U k`, so `w ∈ U k` by `HConv (U k)`. -/
theorem chainRel_hqc {U : ℕ → Set Pt} (hU : ∀ k, HConv (U k)) : HQC (chainRel U) := by
  intro x y z w hyz hwy hw hy hz k hx
  exact hU k y z w (hy k hx) (hz k hx) hyz hwy hw

end Q1
