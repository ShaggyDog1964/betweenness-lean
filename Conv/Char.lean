import Conv.ChainOrder
import Conv.Basic

/-!
# Characterisation of R(UCC C)

A ranking is in R(UCC C) iff it has no obstruction (`char_stmt`).
-/

namespace Conv

universe u

variable {α : Type u} {C : Set (Set α)}

/-- Taking a longer prefix gives more elements. -/
theorem mem_take_mono {L : List α} {m n : ℕ} (hmn : m ≤ n) {x : α} (h : x ∈ L.take m) :
    x ∈ L.take n :=
  (List.take_prefix_take_left (l := L) hmn).subset h

/-- Sufficiency: a ranking without obstruction is in R(UCC C).
Sketch: `U k = hull C {x | x ∈ L.take (k+1)}` is a monotone chain in `C`. Its chain
preference is a quasi-concave weak order; `L[i] ∈ U i`, and for `j > 0`,
`U (j - 1) = hull (take j) ∌ L[j]` by `NoObstruction`. -/
theorem inR_of_noObstruction (hC : IsConvexity C) {L : List α} (h : NoObstruction C L) :
    InR (UCC C) L := by
  set U : ℕ → Set α := fun k => hull C {x | x ∈ L.take (k + 1)} with hUdef
  have hU : Monotone U := fun a b hab =>
    hull_mono fun x hx => mem_take_mono (by omega) hx
  refine ⟨chainRel U, chainRel_weakOrder hU, chainRel_ucc hC fun k => hull_mem hC _, ?_⟩
  refine chainRel_pairwise hU L (fun i hi => ?_) (fun j hj hj0 => ?_)
  · apply subset_hull
    show L[i] ∈ L.take (i + 1)
    exact List.mem_take_iff_getElem.2 ⟨i, by omega, rfl⟩
  · have := h j hj hj0
    simpa [hUdef, Nat.sub_add_cancel (show 1 ≤ j by omega)] using this

/-- Necessity: a ranking in R(UCC C) has no obstruction.
Sketch: if `L[j] ∈ hull (take j)` with `j > 0`, the upper set of `L[j-1]` is convex and
contains `take j`, so `L[j] ≽ L[j-1]`, contradicting `L[j-1] ≻ L[j]`. -/
theorem noObstruction_of_inR {L : List α} (h : InR (UCC C) L) : NoObstruction C L := by
  obtain ⟨R, hR, hP, hL⟩ := h
  intro j hj hj0 hmem
  rw [List.pairwise_iff_getElem] at hL
  have hj1 : j - 1 < L.length := by omega
  have hsub : {x | x ∈ L.take j} ⊆ {y | R y L[j - 1]} := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := List.mem_take_iff_getElem.1 hx
    show R L[i] L[j - 1]
    rcases Nat.lt_or_ge i (j - 1) with hlt | hge
    · exact (hL i (j - 1) (by omega) hj1 hlt).1
    · have : i = j - 1 := by omega
      subst this
      exact (hR.complete _ _).elim id id
  have := hull_min (hP L[j - 1]) hsub hmem
  exact (hL (j - 1) j hj1 hj (by omega)).2 this

/-- Characterisation: a list is in R(UCC C) iff it has no obstruction. -/
theorem char : char_stmt.{u} := fun _ _ hC _ =>
  ⟨noObstruction_of_inR, inR_of_noObstruction hC⟩

/-- The empty ranking is in R(UCC C). -/
example (hC : IsConvexity C) : InR (UCC C) ([] : List α) :=
  (char _ C hC _).2 fun _ hj => absurd hj (by simp)

/-- A one-entry ranking is in R(UCC C), even for the trivial convexity `{Set.univ}`. -/
example (hC : IsConvexity C) (x : α) : InR (UCC C) [x] :=
  (char _ C hC _).2 fun j hj hj0 => absurd hj (by simp; omega)

/-- A ranking with a repeat is never in R(UCC C). -/
example (hC : IsConvexity C) (x : α) : ¬ InR (UCC C) [x, x] := by
  intro h
  exact (char _ C hC _).1 h 1 (by simp) one_pos (subset_hull C _ (by simp))

end Conv
