/-
`collinear_binaryReduction`: a binary reduction holds on a collinear `X`.
-/
import Q3L.Statement
import Q3L.CollinearMenu

namespace Q3L

open K4 (Lot Simplex)

/-- On a collinear `X` a binary reduction holds.
Sketch. Let `ρ, ρ'` be mixtures with equal binary probabilities, `A ⊆ X` nonempty, `x ∈ A`.
Take `a, b ∈ A` minimizing / maximizing `φ` (`Finset.exists_min_image`, `exists_max_image`).
If `a = b`: every `y ∈ A` has `φ y = φ a`, so `y = a` (injectivity from `hrep`), hence
`A = {a} = {x, x}` (`Finset.eq_singleton_iff_unique_mem`, `Finset.pair_self`) and the binary
hypothesis at `(x, x)` closes it. If `a ≠ b`: `collinear_menu` for `ρ` and `ρ'` reduces to
`ρ.p x {a, b} = ρ'.p x {a, b}`: for `x = a` it is the hypothesis at `(a, b)`; for `x = b`
it is the hypothesis at `(b, a)` with `{a, b} = {b, a}` (`Finset.pair_comm`); otherwise both
sides are `0` (`zero_of_not_mem`). -/
theorem collinear_binaryReduction {K : ℕ} {X : Finset (Lot K)}
    (hXs : (↑X : Set (Lot K)) ⊆ Simplex K) {x0 d : Lot K} {φ : Lot K → ℝ}
    (hrep : ∀ x ∈ X, x = x0 + φ x • d) : BinaryReduction X := by
  classical
  intro ρ ρ' hρ hρ' hbin A hA hAne x hx
  obtain ⟨a, ha, hmin⟩ := Finset.exists_min_image A φ hAne
  obtain ⟨b, hb, hmax⟩ := Finset.exists_max_image A φ hAne
  have hinj : ∀ x ∈ X, ∀ y ∈ X, φ x = φ y → x = y := by
    intro x hx y hy h
    rw [hrep x hx, hrep y hy, h]
  by_cases hab : a = b
  · subst hab
    have hAeq : A = {x, x} := by
      rw [Finset.insert_eq_self.2 (Finset.mem_singleton_self x),Finset.eq_singleton_iff_unique_mem]
      refine ⟨hx, fun y hy => ?_⟩
      have h1 : φ y = φ a := le_antisymm (hmax y hy) (hmin y hy)
      have h2 : φ x = φ a := le_antisymm (hmax x hx) (hmin x hx)
      exact hinj y (hA hy) x (hA hx) (h1.trans h2.symm)
    rw [hAeq]
    exact hbin x (hA hx) x (hA hx)
  · rw [collinear_menu hXs hrep ρ hρ hA ha hb hab hmin hmax hx,
      collinear_menu hXs hrep ρ' hρ' hA ha hb hab hmin hmax hx]
    have hab2 : ({a, b} : Finset (Lot K)) ⊆ X := by
      intro z hz
      rcases Finset.mem_insert.1 hz with rfl | hz
      · exact hA ha
      · rw [Finset.mem_singleton.1 hz]; exact hA hb
    by_cases hxa : x = a
    · subst hxa; exact hbin x (hA ha) b (hA hb)
    by_cases hxb : x = b
    · subst hxb
      rw [Finset.pair_comm]
      exact hbin x (hA hb) a (hA ha)
    have hn : x ∉ ({a, b} : Finset (Lot K)) := by
      simp [hxa, hxb]
    rw [ρ.zero_of_not_mem _ hab2 x hn, ρ'.zero_of_not_mem _ hab2 x hn]

end Q3L
