/-
`strict_contour_relOpen` (part of the proof of Lemma 34: strict contour sets are relatively
open in the simplex).
-/
import Q3L.Statement

namespace Q3L

open K4 (Lot Simplex Rel SPref IsBetweennessPref)

/-- The strict upper and strict lower contour sets of `r` are traces on the simplex of open
subsets of `Lot K`.
Sketch (upper). `hR.closed_lower r hr : IsClosed {q : Simplex K | R r q.1}`. Its complement
`{q : Simplex K | ¬ R r q.1}` is open in the subtype (`IsClosed.isOpen_compl`), so by
`isOpen_induced_iff` (the subtype topology is induced by `Subtype.val`) there is an open
`G : Set (Lot K)` with `Subtype.val ⁻¹' G = {q | ¬ R r q.1}`. For `p ∈ Simplex K`:
`p ∈ G ↔ ¬ R r p ↔ SPref R p r`, the last step by completeness (`¬ R r p → R p r`).
Lower: the same with `hR.closed_upper r hr` and `¬ R p r ↔ SPref R r p`. -/
theorem strict_contour_relOpen {K : ℕ} {R : Rel K} (hR : IsBetweennessPref R) {r : Lot K}
    (hr : r ∈ Simplex K) :
    (∃ G : Set (Lot K), IsOpen G ∧ ∀ p ∈ Simplex K, (p ∈ G ↔ SPref R p r)) ∧
      (∃ G : Set (Lot K), IsOpen G ∧ ∀ p ∈ Simplex K, (p ∈ G ↔ SPref R r p)) := by
  constructor
  · obtain ⟨G, hG, hpre⟩ := isOpen_induced_iff.mp (hR.closed_lower r hr).isOpen_compl
    refine ⟨G, hG, fun p hp => ?_⟩
    have h : (⟨p, hp⟩ : Simplex K) ∈ Subtype.val ⁻¹' G ↔
        (⟨p, hp⟩ : Simplex K) ∈ {q : Simplex K | R r q.1}ᶜ := by rw [hpre]
    simp only [Set.mem_preimage, Set.mem_compl_iff, Set.mem_ofPred_eq] at h
    rw [h]
    unfold SPref
    constructor
    · intro hn
      exact ⟨(hR.complete p hp r hr).resolve_right hn, hn⟩
    · exact fun h' => h'.2
  · obtain ⟨G, hG, hpre⟩ := isOpen_induced_iff.mp (hR.closed_upper r hr).isOpen_compl
    refine ⟨G, hG, fun p hp => ?_⟩
    have h : (⟨p, hp⟩ : Simplex K) ∈ Subtype.val ⁻¹' G ↔
        (⟨p, hp⟩ : Simplex K) ∈ {q : Simplex K | R q.1 r}ᶜ := by rw [hpre]
    simp only [Set.mem_preimage, Set.mem_compl_iff, Set.mem_ofPred_eq] at h
    rw [h]
    unfold SPref
    constructor
    · intro hn
      exact ⟨(hR.complete p hp r hr).resolve_left hn, hn⟩
    · exact fun h' => h'.2

end Q3L
