/-
`meets_iff_hyperplane` (first claim of Theorem 36(2); Lemma 85, both directions).
-/
import Q3L.Statement
import Q3L.DotPosCone
import Q3L.PerpStrictMono
import Q3L.PerpIffConst

namespace Q3L

open K4 (Lot)

/-- `V ∩ D = {0}` iff `aff(X)` lies in an EU indifference hyperplane with strictly increasing
`w`.
Sketch. (⇒) `exists_perp_strictMono (dirSpace X) h` gives `w` strictly increasing with
`w ⊥ dirSpace X`; `perp_iff_const` turns orthogonality into a constant `γ` on `affHull X`.
(⇐) From `⟨hw, γ, hγ⟩`, `perp_iff_const` (backwards) gives `dot w d = 0` for `d ∈ dirSpace X`.
If `d ∈ dirSpace X ∩ FOSDCone K` and `d ≠ 0`, `dot_pos_of_cone hK hw` gives `0 < dot w d`,
contradiction; so `d = 0`. -/
theorem meets_iff_hyperplane {K : ℕ} (hK : 0 < K) (X : Finset (Lot K)) :
    MeetsConeTrivially X ↔ ∃ w : Lot K, InIndiffHyperplane X w := by
  constructor
  · intro h
    obtain ⟨w, hw, hperp⟩ := exists_perp_strictMono (dirSpace X) h
    exact ⟨w, hw, (perp_iff_const X w).mp hperp⟩
  · rintro ⟨w, hw, hγ⟩ d hdV hdD
    have hperp := (perp_iff_const X w).mpr hγ
    by_contra hd0
    have hpos := dot_pos_of_cone hK hw hdD hd0
    rw [hperp d hdV] at hpos
    exact lt_irrefl _ hpos

end Q3L
