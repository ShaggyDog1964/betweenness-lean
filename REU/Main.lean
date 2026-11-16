/-
# Theorem 1

`thm1`: a random choice rule on `X ⊆ Tri` is a finite mixture of betweenness preferences strict
on `X` iff it satisfies Chord Dominance and Bracketing (`necessity` + `sufficiency`).
The REU clause `thm1_reu : thm1_reu_stmt` is proved in `REU.EU` and re-exported by the import.
-/
import REU.EU
import REU.Sufficiency

namespace REU

/-- **Theorem 1.** -/
theorem thm1 : thm1_stmt := fun _ hX ρ =>
  ⟨necessity hX ρ, fun h => sufficiency hX ρ h.1 h.2⟩

/-! ## Tests -/

example : thm1_stmt := thm1
example : thm1_reu_stmt := thm1_reu

/-- Round trip: a mixture's CD and Bracketing feed back through `sufficiency`. -/
example {X : Finset Pt} (hX : (↑X : Set Pt) ⊆ Tri) (ρ : RandomChoiceRule X)
    (h : IsMixture IsBetweennessPref X ρ) : IsMixture IsBetweennessPref X ρ :=
  sufficiency hX ρ (necessity hX ρ h).1 (necessity hX ρ h).2

end REU
