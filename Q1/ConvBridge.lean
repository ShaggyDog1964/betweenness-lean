import Q1.ConvStatement
import Q1.Defs
import Conv.Main

/-!
# Q1 via Conv: the bridge

`CH` and `CV` are convexities; H-QC, V-QC and their conjunction are the `UCC` conditions;
the Q1 and Conv notions of `InR` and `IsLocal` agree on the plane.
-/

namespace Q1

/-- Membership in `CH` is horizontal convexity. -/
theorem mem_CH_iff (U : Set Pt) : U ∈ CH ↔ HConv U := Iff.rfl

/-- Membership in `CV` is vertical convexity. -/
theorem mem_CV_iff (U : Set Pt) : U ∈ CV ↔ VConv U := Iff.rfl

/-- `CH` and `CV` are convexities. -/
theorem convexity : convexity_stmt := by
  refine ⟨fun S hS => ?_, fun S hS => ?_⟩
  · intro y z w hy hz hyz hwy hw U hU
    exact hS hU y z w (hy U hU) (hz U hU) hyz hwy hw
  · intro y z w hy hz hyz hwy hw U hU
    exact hS hU y z w (hy U hU) (hz U hU) hyz hwy hw

/-- H-QC, V-QC and their conjunction are the `UCC` conditions. -/
theorem bridge : bridge_stmt := by
  have hH : ∀ R : Rel, HQC R ↔ Conv.UCC CH R := fun R =>
    ⟨fun h x y z w hy hz hyz hwy hw => h x y z w hyz hwy hw hy hz,
     fun h x y z w hyz hwy hw hy hz => h x y z w hy hz hyz hwy hw⟩
  have hV : ∀ R : Rel, VQC R ↔ Conv.UCC CV R := fun R =>
    ⟨fun h x y z w hy hz hyz hwy hw => h x y z w hyz hwy hw hy hz,
     fun h x y z w hyz hwy hw hy hz => h x y z w hy hz hyz hwy hw⟩
  exact ⟨hH, hV, fun R => and_congr (hH R) (hV R)⟩

/-- The Q1 and Conv notions of `InR` agree (the weak-order structures are converted field
by field). -/
theorem inR_iff_conv (P : Rel → Prop) (L : List Pt) : Q1.InR P L ↔ Conv.InR P L := by
  constructor
  · rintro ⟨R, hW, hP, hL⟩
    exact ⟨R, ⟨hW.complete, hW.trans⟩, hP, hL⟩
  · rintro ⟨R, hW, hP, hL⟩
    exact ⟨R, ⟨hW.complete, hW.trans⟩, hP, hL⟩

/-- The Q1 and Conv notions of `IsLocal` agree. -/
theorem isLocal_iff_conv (P : Rel → Prop) (n : ℕ) : Q1.IsLocal P n ↔ Conv.IsLocal P n := by
  constructor
  · intro h L hL hloc
    exact (inR_iff_conv P L).1 (h L hL fun L' hs hlen => (inR_iff_conv P L').2 (hloc L' hs hlen))
  · intro h L hL hloc
    exact (inR_iff_conv P L).2 (h L hL fun L' hs hlen => (inR_iff_conv P L').1 (hloc L' hs hlen))

/-- R(HVQC) in Q1 is R(UCC (CH ∩ CV)) in Conv. -/
theorem inR_HVQC_iff (L : List Pt) : Q1.InR HVQC L ↔ Conv.InR (Conv.UCC (CH ∩ CV)) L := by
  have hP : HVQC = Conv.UCC (CH ∩ CV) := funext fun R => propext
    ((bridge.2.2 R).trans ((Conv.join Pt CH CV convexity.1 convexity.2).2.1 R))
  rw [inR_iff_conv, hP]

end Q1
