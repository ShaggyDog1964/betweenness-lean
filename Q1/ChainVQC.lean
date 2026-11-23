import Q1.Defs

namespace Q1

/-- If every set of the chain is vertically convex, the chain preference is V-QC.
Sketch: as `chainRel_hqc`, with `VConv`. -/
theorem chainRel_vqc {U : ℕ → Set Pt} (hU : ∀ k, VConv (U k)) : VQC (chainRel U) := by
  intro x y z w h1 h2 h3 hy hz k hx
  exact hU k y z w (hy k hx) (hz k hx) h1 h2 h3

end Q1
