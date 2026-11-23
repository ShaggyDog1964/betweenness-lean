import Q1.ConvBridge
import Q1.HHullConv
import Q1.HHullSelf
import Q1.HHullSubset

/-!
# Carathéodory number of horizontal convexity

The `CH`-hull of a finite set is its horizontal hull `hHull`; every point of it lies on a
horizontal segment between two of the points, so `CH` has Carathéodory bound 2. The
witness for "not 1" is `A = {(0,0), (2,0)}`, `p = (1,0)`.
-/

namespace Q1

/-- The `CH`-hull of a finite set is its horizontal hull. -/
theorem hull_CH_eq_hHull (A : Finset Pt) : Conv.hull CH ↑A = hHull A.toList := by
  apply Set.Subset.antisymm
  · exact Conv.hull_min (hHull_hconv _) fun x hx =>
      mem_hHull_self (Finset.mem_toList.2 (Finset.mem_coe.1 hx))
  · rintro w ⟨y, hy, z, hz, h1, h2, h3⟩
    have hy' := Conv.subset_hull CH (↑A : Set Pt) (Finset.mem_coe.2 (Finset.mem_toList.1 hy))
    have hz' := Conv.subset_hull CH (↑A : Set Pt) (Finset.mem_coe.2 (Finset.mem_toList.1 hz))
    exact Conv.hull_mem convexity.1 _ y z w hy' hz' h1 h2 h3

/-- A set with at most one element is horizontally convex. -/
theorem subsingleton_mem_CH {U : Set Pt} (hU : U.Subsingleton) : U ∈ CH := by
  intro y z w hy hz _ hwy hw
  have hyz : y = z := hU hy hz
  subst hyz
  rw [Set.uIcc_self, Set.mem_singleton_iff] at hw
  have : w = y := Prod.ext hw hwy
  exact this ▸ hy

/-- `CH` has Carathéodory bound 2 and not 1. -/
theorem cara_H : cara_H_stmt := by
  classical
  refine ⟨fun A p hp => ?_, fun h => ?_⟩
  · rw [hull_CH_eq_hHull] at hp
    obtain ⟨y, hy, z, hz, h1, h2, h3⟩ := hp
    refine ⟨{y, z}, ?_, Finset.card_le_two, ?_⟩
    · intro x hx
      rw [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact Finset.mem_toList.1 hy
      · exact Finset.mem_toList.1 hz
    · rw [hull_CH_eq_hHull]
      exact ⟨y, by simp, z, by simp, h1, h2, h3⟩
  · have hp : ((1 : ℝ), (0 : ℝ)) ∈ Conv.hull CH
        (↑({((0 : ℝ), (0 : ℝ)), ((2 : ℝ), (0 : ℝ))} : Finset Pt) : Set Pt) := by
      intro U ⟨hU, hAU⟩
      refine hU ((0 : ℝ), (0 : ℝ)) ((2 : ℝ), (0 : ℝ)) ((1 : ℝ), (0 : ℝ))
        (hAU (by simp)) (hAU (by simp)) rfl rfl ?_
      rw [Set.mem_uIcc]; left; norm_num
    obtain ⟨B, hBA, hBc, hpB⟩ := h _ _ hp
    have hsub : (↑B : Set Pt).Subsingleton := fun a ha b hb =>
      Finset.card_le_one.1 hBc a ha b hb
    rw [Conv.hull_eq_self convexity.1 (subsingleton_mem_CH hsub)] at hpB
    have := hBA (Finset.mem_coe.1 hpB)
    simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at this
    norm_num at this

end Q1
