/-
`lemma_H`: Lemma 34 in general dimension `K`.
-/
import Q3L.Statement
import Q3L.HConvex
import Q3L.HRelOpen
import Q3L.HSeparate
import Q3L.HClosure
import Q3L.PosPoint
import Q3L.ZeroPoint
import Q3L.HTrichotomy
import Q3L.HStrictMono

namespace Q3L

open K4 (Lot Simplex Rel SPref IsBetweennessPref)

/-- Lemma 34, for any `K`. If `x ≻ r ≻ y` in the simplex, some strictly increasing `W`
satisfies `p ≻ r ↔ W·p > 0` and `r ≻ p ↔ W·p < 0` on the simplex (so `p ∼ r ↔ W·p = 0`).
`r` need not be interior.
Sketch (assembly). `0 < K` (the simplex of `Fin 0 → ℝ` is empty since its sum is `0 ≠ 1`).
`strict_contour_relOpen` gives open `G` (upper) and `G'` (lower). Then
`Simplex ∩ G = {p | p ∈ Simplex ∧ SPref R p r}` and likewise for `G'` (`Set.ext`), so both are
convex by `strict_contour_convex`, and disjoint (`SPref R p r` and `SPref R r p` are
incompatible). `sep_relOpen` gives `W₀` strictly positive / negative at positive points of
the two sets. `nonneg_of_relOpen` gives `hU`; applied to `-W₀` and `G'` it gives `hL`.
`exists_pos_mem_open` at `x ∈ Simplex ∩ G` gives a positive upper point `z'`, so
`0 < dot W₀ z'`; at `y ∈ Simplex ∩ G'` a positive lower point `z` with `dot W₀ z < 0`.
`sign_iff_of_sep` gives the sign characterization `hsign`. `exists_pos_zero` (with `z, z'`)
gives a positive zero of `dot W₀`, and `strictMono_of_sign` gives `StrictMono W₀`. -/
theorem lemma_H {K : ℕ} {R : Rel K} (hR : IsBetweennessPref R) {r x y : Lot K}
    (hr : r ∈ Simplex K) (hx : x ∈ Simplex K) (hy : y ∈ Simplex K)
    (hxr : SPref R x r) (hry : SPref R r y) :
    ∃ W : Lot K, StrictMono W ∧
      ∀ p ∈ Simplex K, (SPref R p r ↔ 0 < dot W p) ∧ (SPref R r p ↔ dot W p < 0) := by
  have hK : 0 < K := by
    rcases Nat.eq_zero_or_pos K with h | h
    · subst h
      have := hr.2
      simp at this
    · exact h
  obtain ⟨⟨G, hG, hGU⟩, ⟨G', hG', hGL⟩⟩ := strict_contour_relOpen hR hr
  have eU : Simplex K ∩ G = {p | p ∈ Simplex K ∧ SPref R p r} := by
    ext p
    exact ⟨fun h => ⟨h.1, (hGU p h.1).mp h.2⟩, fun h => ⟨h.1, (hGU p h.1).mpr h.2⟩⟩
  have eL : Simplex K ∩ G' = {p | p ∈ Simplex K ∧ SPref R r p} := by
    ext p
    exact ⟨fun h => ⟨h.1, (hGL p h.1).mp h.2⟩, fun h => ⟨h.1, (hGL p h.1).mpr h.2⟩⟩
  have hconv := strict_contour_convex hR hr
  have hS : Convex ℝ (Simplex K ∩ G) := by rw [eU]; exact hconv.1
  have hT : Convex ℝ (Simplex K ∩ G') := by rw [eL]; exact hconv.2
  have hdisj : Disjoint (Simplex K ∩ G) (Simplex K ∩ G') := by
    rw [eU, eL, Set.disjoint_left]
    rintro p ⟨_, h1⟩ ⟨_, h2⟩
    exact h1.2 h2.1
  obtain ⟨W, hWU, hWL⟩ := sep_relOpen hK hG hG' hS hT hdisj
  have hneg : ∀ p : Lot K, dot (-W) p = - dot W p := by
    intro p
    simp [dot, Finset.sum_neg_distrib]
  have hU0 := nonneg_of_relOpen hK hG hWU
  have hL0 := nonneg_of_relOpen hK hG' (W := -W) (fun p hp hpos => by
    rw [hneg]; have := hWL p hp hpos; linarith)
  have hU : ∀ p ∈ Simplex K, SPref R p r → 0 ≤ dot W p :=
    fun p hp h => hU0 p ⟨hp, (hGU p hp).mpr h⟩
  have hL : ∀ p ∈ Simplex K, SPref R r p → dot W p ≤ 0 := by
    intro p hp h
    have := hL0 p ⟨hp, (hGL p hp).mpr h⟩
    rw [hneg] at this; linarith
  obtain ⟨z', hz'S, hz'G, hz'p⟩ := exists_pos_mem_open hK hG hx ((hGU x hx).mpr hxr)
  obtain ⟨z, hzS, hzG, hzp⟩ := exists_pos_mem_open hK hG' hy ((hGL y hy).mpr hry)
  have h2 : 0 < dot W z' := hWU z' ⟨hz'S, hz'G⟩ hz'p
  have h1 : dot W z < 0 := hWL z ⟨hzS, hzG⟩ hzp
  have hsign := sign_iff_of_sep hR hr hG hG' hGU hGL hU hL
    ⟨z, hzS, (hGL z hzS).mp hzG, h1⟩ ⟨z', hz'S, (hGU z' hz'S).mp hz'G, h2⟩
  exact ⟨W, strictMono_of_sign hR hr hsign (exists_pos_zero hzS hzp hz'S hz'p h1 h2), hsign⟩

end Q3L
