import Q1.ConvCaraV
import Q1.ConvCaraHV

/-!
# Q1 via Conv: assembly

`Q1.target_stmt` re-derived through the generic convexity library: locality of H-QC and
V-QC from `Conv.locality` with the Carathéodory numbers of `CH` and `CV`, and
non-locality of HVQC from `Conv.conj_local` with the unbounded Carathéodory number of
`CH ∩ CV`.
-/

namespace Q1

/-- The whole bridge claim. -/
theorem conv_target : conv_target_stmt :=
  ⟨convexity, bridge, cara_H, cara_V, cara_HV⟩

/-- `Q1.target_stmt`, derived through `Conv`. -/
theorem target_via_conv : target_stmt := by
  have hH : HQC = Conv.UCC CH := funext fun R => propext (bridge.1 R)
  have hV : VQC = Conv.UCC CV := funext fun R => propext (bridge.2.1 R)
  have hHV : HVQC = fun R => Conv.UCC CH R ∧ Conv.UCC CV R :=
    funext fun R => propext (bridge.2.2 R)
  have locH := Conv.locality Pt CH convexity.1
  have locV := Conv.locality Pt CV convexity.2
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩
  · rw [isLocal_iff_conv, hH]; exact (locH 3 (by norm_num)).2 cara_H.1
  · rw [isLocal_iff_conv, hH]; exact fun h => cara_H.2 ((locH 2 le_rfl).1 h)
  · rw [isLocal_iff_conv, hV]; exact (locV 3 (by norm_num)).2 cara_V.1
  · rw [isLocal_iff_conv, hV]; exact fun h => cara_V.2 ((locV 2 le_rfl).1 h)
  · intro n h
    rw [isLocal_iff_conv, hHV] at h
    exact cara_HV (max n 2 - 1)
      ((Conv.conj_local Pt CH CV convexity.1 convexity.2 (max n 2) (le_max_right _ _)).1
        (Conv.isLocal_mono h (le_max_left _ _)))

end Q1
