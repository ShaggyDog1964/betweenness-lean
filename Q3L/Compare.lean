/-
`comparison_frame` (Lemma 87, extended to the two extreme vertices so
the main proof needs no case split).
-/
import Q3L.Statement
import Q3L.DotEq
import Q3L.LemmaH
import Q3L.VtxDom
import K4.DotFosd
import K4.VtxMem

namespace Q3L

open K4 (Lot Simplex Rel SPref IsBetweennessPref)

/-- For a betweenness preference and ANY `x` in the simplex there is a strictly increasing `W`
with `x ≻ y ↔ W·(x - y) > 0` for all `y` in the simplex.
Sketch. Write `top := K4.vtx K (K-1)`, `bot := K4.vtx K 0` (both in the simplex,
`K4.vtx_mem_simplex`). Note `SPref R p p` is always false.
* `x = top`: take `W k := (k : ℝ)` (strictly increasing). For `y = x` both sides are false
  (`dot W 0 = 0`). For `y ≠ x`, `StrictFOSD x y` (`vtx_fosd`), so `SPref R x y`
  (`hR.strictMono`) and `dot W y < dot W x` (`K4.dot_lt_of_strictFOSD`), i.e.
  `0 < dot W (x - y)`.
* `x = bot`: same `W`. For `y ≠ x`, `StrictFOSD y x`, so `SPref R y x` and hence
  `¬ SPref R x y`; and `dot W x < dot W y`, so `¬ 0 < dot W (x - y)`.
* otherwise: `StrictFOSD top x` and `StrictFOSD x bot` (`vtx_fosd`, `x ≠ top`, `x ≠ bot`),
  so `SPref R top x` and `SPref R x bot`. `lemma_H` with `r := x` gives `W`. At `p = x`,
  neither `SPref R x x` side holds, so `dot W x = 0`. Then
  `SPref R x y ↔ dot W y < 0 ↔ 0 < dot W x - dot W y = dot W (x - y)`. -/
theorem comparison_frame {K : ℕ} (hK : 0 < K) {R : Rel K} (hR : IsBetweennessPref R)
    {x : Lot K} (hx : x ∈ Simplex K) :
    ∃ W : Lot K, StrictMono W ∧ ∀ y ∈ Simplex K, (SPref R x y ↔ 0 < dot W (x - y)) := by
  have hsub : ∀ W y : Lot K, dot W (x - y) = dot W x - dot W y := by
    intro W y
    rw [dot_eq_dotProduct, dot_eq_dotProduct, dot_eq_dotProduct, dotProduct_sub]
  have hirr : ∀ p : Lot K, ¬ SPref R p p := fun p h => h.2 h.1
  have hK4 : ∀ W p : Lot K, K4.dot W p = dot W p := fun _ _ => rfl
  have htop : K4.vtx K (K - 1) ∈ Simplex K := K4.vtx_mem_simplex (by omega)
  have hbot : K4.vtx K 0 ∈ Simplex K := K4.vtx_mem_simplex hK
  have hW0 : StrictMono (fun k : Fin K => (k.val : ℝ)) := by
    intro a b h
    simp only
    exact_mod_cast h
  by_cases hxt : x = K4.vtx K (K - 1)
  · refine ⟨fun k => (k.val : ℝ), hW0, fun y hy => ?_⟩
    by_cases hyx : y = x
    · subst hyx
      simp only [sub_self]
      constructor
      · intro h; exact absurd h (hirr _)
      · intro h
        exfalso
        rw [dot_eq_dotProduct, dotProduct_zero] at h
        exact lt_irrefl _ h
    · have hf : K4.StrictFOSD x y := ⟨hxt ▸ (vtx_fosd hK hy).1, fun h => hyx h.symm⟩
      have h1 := hR.strictMono x hx y hy hf
      have h2 := K4.dot_lt_of_strictFOSD hW0 hx hy hf
      rw [hK4, hK4] at h2
      rw [hsub]
      exact ⟨fun _ => by linarith, fun _ => h1⟩
  by_cases hxb : x = K4.vtx K 0
  · refine ⟨fun k => (k.val : ℝ), hW0, fun y hy => ?_⟩
    by_cases hyx : y = x
    · subst hyx
      simp only [sub_self]
      constructor
      · intro h; exact absurd h (hirr _)
      · intro h
        exfalso
        rw [dot_eq_dotProduct, dotProduct_zero] at h
        exact lt_irrefl _ h
    · have hf : K4.StrictFOSD y x := ⟨hxb ▸ (vtx_fosd hK hy).2, hyx⟩
      have h1 := hR.strictMono y hy x hx hf
      have h2 := K4.dot_lt_of_strictFOSD hW0 hy hx hf
      rw [hK4, hK4] at h2
      rw [hsub]
      constructor
      · intro h; exact absurd h.1 h1.2
      · intro h; exfalso; linarith
  · have hf1 : K4.StrictFOSD (K4.vtx K (K - 1)) x := ⟨(vtx_fosd hK hx).1, fun h => hxt h.symm⟩
    have hf2 : K4.StrictFOSD x (K4.vtx K 0) := ⟨(vtx_fosd hK hx).2, hxb⟩
    obtain ⟨W, hW, hs⟩ := lemma_H hR hx htop hbot (hR.strictMono _ htop x hx hf1)
      (hR.strictMono x hx _ hbot hf2)
    have hx0 : dot W x = 0 := by
      rcases lt_trichotomy (dot W x) 0 with h | h | h
      · exact absurd ((hs x hx).2.mpr h) (hirr _)
      · exact h
      · exact absurd ((hs x hx).1.mpr h) (hirr _)
    refine ⟨W, hW, fun y hy => ?_⟩
    rw [hsub, hx0, (hs y hy).2]
    constructor <;> intro h <;> linarith

end Q3L
