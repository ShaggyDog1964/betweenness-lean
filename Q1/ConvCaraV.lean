import Q1.ConvCaraH

/-!
# Carathéodory number of vertical convexity

Transported from the horizontal case along `Prod.swap`: `U ∈ CV` iff its swap is in `CH`,
so the hulls correspond and so do Carathéodory bounds.
-/

namespace Q1

/-- The swap of a set is horizontally convex iff the set is vertically convex. -/
theorem swap_mem_CV_iff (U : Set Pt) : Prod.swap ⁻¹' U ∈ CH ↔ U ∈ CV := by
  constructor
  · intro h y z w hy hz hyz hwy hw
    have := h y.swap z.swap w.swap (by simpa using hy) (by simpa using hz) hyz hwy hw
    simpa using this
  · intro h y z w hy hz hyz hwy hw
    exact h y.swap z.swap w.swap hy hz hyz hwy hw

/-- The `CV`-hull is the swap of the `CH`-hull of the swapped set. -/
theorem hull_CV_swap (S : Set Pt) :
    Conv.hull CV S = Prod.swap ⁻¹' Conv.hull CH (Prod.swap ⁻¹' S) := by
  ext x
  simp only [Conv.hull, Set.mem_preimage, Set.mem_sInter, Set.mem_ofPred_eq]
  constructor
  · rintro h V ⟨hV, hSV⟩
    have hV' : Prod.swap ⁻¹' V ∈ CV := by
      rw [← swap_mem_CV_iff, ← Set.preimage_comp, Prod.swap_swap_eq, Set.preimage_id]
      exact hV
    exact h _ ⟨hV', fun s hs => by simpa using hSV (show s.swap ∈ Prod.swap ⁻¹' S by simpa using hs)⟩
  · rintro h U ⟨hU, hSU⟩
    have := h _ ⟨(swap_mem_CV_iff U).2 hU, fun s hs => hSU hs⟩
    simpa using this

/-- The `CH`-hull is the swap of the `CV`-hull of the swapped set. -/
theorem hull_CH_swap (S : Set Pt) :
    Conv.hull CH S = Prod.swap ⁻¹' Conv.hull CV (Prod.swap ⁻¹' S) := by
  rw [hull_CV_swap, ← Set.preimage_comp, ← Set.preimage_comp, Prod.swap_swap_eq,
    Set.preimage_id, Set.preimage_id]

/-- Carathéodory bounds transfer along `Prod.swap` between convexities whose hulls
correspond. -/
theorem caraBound_swap {C₁ C₂ : Set (Set Pt)}
    (hh : ∀ S, Conv.hull C₂ S = Prod.swap ⁻¹' Conv.hull C₁ (Prod.swap ⁻¹' S)) {c : ℕ}
    (h : Conv.CaraBound C₁ c) : Conv.CaraBound C₂ c := by
  classical
  have hcoe : ∀ A : Finset Pt,
      Prod.swap ⁻¹' (↑A : Set Pt) = ↑(A.map (Equiv.prodComm ℝ ℝ).toEmbedding) := by
    intro A; ext x
    simp only [Set.mem_preimage, Finset.coe_map, Set.mem_image, Finset.mem_coe]
    exact ⟨fun hx => ⟨x.swap, hx, by simp⟩, fun ⟨a, ha, hax⟩ => by subst hax; simpa using ha⟩
  intro A p hp
  rw [hh, Set.mem_preimage, hcoe] at hp
  obtain ⟨B', hB'A, hB'c, hpB'⟩ := h _ _ hp
  refine ⟨B'.map (Equiv.prodComm ℝ ℝ).toEmbedding, ?_, by simpa using hB'c, ?_⟩
  · intro x hx
    rw [Finset.mem_map] at hx
    obtain ⟨b, hb, rfl⟩ := hx
    have := hB'A hb
    rw [Finset.mem_map] at this
    obtain ⟨a, ha, rfl⟩ := this
    simpa using ha
  · rw [hh, Set.mem_preimage, hcoe]
    have : (B'.map (Equiv.prodComm ℝ ℝ).toEmbedding).map (Equiv.prodComm ℝ ℝ).toEmbedding
        = B' := by
      ext x; simp
    rw [this]; exact hpB'

/-- `CV` has Carathéodory bound 2 and not 1, transported from `cara_H`. -/
theorem cara_V : cara_V_stmt :=
  ⟨caraBound_swap hull_CV_swap cara_H.1,
   fun h => cara_H.2 (caraBound_swap hull_CH_swap h)⟩

end Q1
