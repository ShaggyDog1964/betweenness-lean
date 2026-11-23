import Conv.Locality

/-!
# Joins of convexities

The intersection of two convexities is a convexity whose quasi-concave preferences are
those quasi-concave for both and whose hull is the closure under both hull operators
(`join_stmt`). The locality criterion transfers to the conjunction (`conj_local_stmt`).
-/

namespace Conv

universe u

/-- Joins of convexities. -/
theorem join : join_stmt.{u} := by
  intro α C₁ C₂ hC₁ hC₂
  refine ⟨fun S hS => ⟨hC₁ S (hS.trans Set.inter_subset_left),
    hC₂ S (hS.trans Set.inter_subset_right)⟩, fun R => ?_, fun S => ?_⟩
  · exact ⟨fun h x => ⟨h.1 x, h.2 x⟩, fun h => ⟨fun x => (h x).1, fun x => (h x).2⟩⟩
  · unfold hull
    congr 1
    ext T
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff]
    constructor
    · rintro ⟨⟨h₁, h₂⟩, hST⟩
      exact ⟨hST, hull_eq_self hC₁ h₁, hull_eq_self hC₂ h₂⟩
    · rintro ⟨hST, h₁, h₂⟩
      exact ⟨⟨h₁ ▸ hull_mem hC₁ T, h₂ ▸ hull_mem hC₂ T⟩, hST⟩

/-- The locality criterion for the conjunction of two quasi-concavity properties. -/
theorem conj_local : conj_local_stmt.{u} := by
  intro α C₁ C₂ hC₁ hC₂ n hn
  have hP : (fun R => UCC C₁ R ∧ UCC C₂ R) = UCC (C₁ ∩ C₂) :=
    funext fun R => propext ((join α C₁ C₂ hC₁ hC₂).2.1 R)
  rw [hP]
  exact locality α _ (join α C₁ C₂ hC₁ hC₂).1 n hn

/-- The conjunction of two quasi-concavity properties has a bounded test iff the join
convexity `C₁ ∩ C₂` has a finite Carathéodory bound. -/
theorem conj_local_iff_finite {α : Type u} {C₁ C₂ : Set (Set α)} (hC₁ : IsConvexity C₁)
    (hC₂ : IsConvexity C₂) :
    (∃ n, IsLocal (fun R => UCC C₁ R ∧ UCC C₂ R) n) ↔ ∃ c, CaraBound (C₁ ∩ C₂) c := by
  have hP : (fun R => UCC C₁ R ∧ UCC C₂ R) = UCC (C₁ ∩ C₂) :=
    funext fun R => propext ((join α C₁ C₂ hC₁ hC₂).2.1 R)
  rw [hP]
  exact local_iff_finite α _ (join α C₁ C₂ hC₁ hC₂).1

end Conv
