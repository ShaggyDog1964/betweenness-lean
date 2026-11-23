/-
`perp_iff_const`: orthogonal to `V` iff constant on `aff(X)`.
-/
import Q3L.Statement
import Q3L.DotEq

namespace Q3L

open K4 (Lot)

/-- `w ⊥ dirSpace X` iff `dot w` is constant on `affHull X`. Holds also for `X = ∅`
(both sides true: `vectorSpan ∅ = ⊥`, `affineSpan ∅ = ⊥` is empty).
Sketch. (⇒) If `X = ∅`, take `γ = 0`; `affineSpan ℝ ∅ = ⊥` has no points
(`AffineSubspace.not_mem_bot` / `affineSpan_empty`). Else fix `x₀ ∈ X`, `γ := dot w x₀`. For
`p ∈ affHull X`, `p -ᵥ x₀ ∈ (affineSpan ℝ X).direction` (`AffineSubspace.vsub_mem_direction`,
`x₀ ∈ affineSpan` by `subset_affineSpan`), and the direction is `vectorSpan ℝ X`
(`direction_affineSpan`); `vsub_eq_sub`. So `dot w (p - x₀) = 0`, i.e. `dot w p = γ`
(`dot_eq_dotProduct`, `dotProduct_sub`).
(⇐) `vectorSpan ℝ X = Submodule.span ℝ (X -ᵥ X)` (`vectorSpan_def`). The map `dot w` is
linear, so it suffices (`Submodule.span_induction`) that it vanishes on generators
`x -ᵥ y = x - y` with `x, y ∈ X ⊆ affHull X`: `dot w x - dot w y = γ - γ = 0`. -/
theorem perp_iff_const {K : ℕ} (X : Finset (Lot K)) (w : Lot K) :
    (∀ v ∈ dirSpace X, dot w v = 0) ↔ ∃ γ : ℝ, ∀ p ∈ affHull X, dot w p = γ := by
  have hsub : ∀ p q : Lot K, dot w (p - q) = dot w p - dot w q := by
    intro p q
    simp only [dot, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]
  constructor
  · intro h
    by_cases hq : ∃ q, q ∈ affHull X
    · obtain ⟨q, hq⟩ := hq
      refine ⟨dot w q, fun p hp => ?_⟩
      have hd : p -ᵥ q ∈ (affHull X).direction := AffineSubspace.vsub_mem_direction hp hq
      have hd' : p - q ∈ dirSpace X := by
        rw [affHull, direction_affineSpan] at hd
        simpa [dirSpace, vsub_eq_sub] using hd
      have := h _ hd'
      rw [hsub] at this
      linarith
    · exact ⟨0, fun p hp => absurd ⟨p, hp⟩ hq⟩
  · rintro ⟨γ, hγ⟩ v hv
    let L : Lot K →ₗ[ℝ] ℝ :=
      { toFun := dot w
        map_add' := by
          intro a b
          simp only [dot, Pi.add_apply, mul_add, Finset.sum_add_distrib]
        map_smul' := by
          intro c a
          simp only [dot, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
          refine Finset.sum_congr rfl fun k _ => by ring }
    have hle : dirSpace X ≤ LinearMap.ker L := by
      rw [dirSpace, vectorSpan_def, Submodule.span_le]
      rintro _ ⟨x, hx, y, hy, rfl⟩
      have hx' : x ∈ affHull X := subset_affineSpan ℝ _ hx
      have hy' : y ∈ affHull X := subset_affineSpan ℝ _ hy
      show dot w (x -ᵥ y) = 0
      rw [vsub_eq_sub, hsub, hγ x hx', hγ y hy', sub_self]
    exact hle hv

end Q3L
