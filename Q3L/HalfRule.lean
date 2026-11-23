/-
`exists_halfRule`: the rule `½[u] + ½[u']` is a random choice rule.
-/
import Q3L.Statement
import Q3L.IsMaxInEu

namespace Q3L

open K4 (Lot)

open Classical in
/-- On a nonempty `A ⊆ X`, with `euRel u` strict on `X`, exactly one element of `A` is the
`u`-best one, so the `½`-indicator sums to `½`. -/
private theorem half_sum {K : ℕ} {X : Finset (Lot K)} {u : Lot K}
    (hu : StrictOn (euRel u) X) {A : Finset (Lot K)} (hA : A ⊆ X) (hne : A.Nonempty) :
    (∑ x ∈ A, (if IsMaxIn (euRel u) x A then (1 / 2 : ℝ) else 0)) = 1 / 2 := by
  obtain ⟨x₀, hx₀, hmax⟩ := Finset.exists_max_image A (dot u) hne
  have key : ∀ x ∈ A, IsMaxIn (euRel u) x A ↔ x = x₀ := by
    intro x hx
    rw [isMaxIn_euRel_iff]
    constructor
    · rintro ⟨_, h⟩
      by_contra hne'
      have h1 := h x₀ hx₀ (fun e => hne' e.symm)
      have h2 := hmax x hx
      linarith
    · rintro rfl
      refine ⟨hx, fun y hy hyx => ?_⟩
      have h2 := hmax y hy
      rcases lt_or_eq_of_le h2 with h | h
      · exact h
      · exact absurd ⟨(le_of_eq h.symm : dot u x ≤ dot u y), (le_of_eq h : dot u y ≤ dot u x)⟩
          (hu y (hA hy) x (hA hx) hyx)
  rw [Finset.sum_congr rfl (fun x hx => if_congr (key x hx) rfl rfl)]
  rw [Finset.sum_ite_eq' A x₀ (fun _ => (1 / 2 : ℝ))]
  simp [hx₀]

open Classical in
/-- For two EU relations strict on `X`, `½[u] + ½[u']` defines a random choice rule on `X`.
Sketch. Define `p x A := (if IsMaxIn (euRel u) x A then 1/2 else 0) + (if IsMaxIn (euRel u')
x A then 1/2 else 0)`; the stated equation is then `rfl`. nonneg: each summand `≥ 0`.
zero_of_not_mem: `IsMaxIn _ x A` requires `x ∈ A`. sum_one: it suffices that for
`A ⊆ X` nonempty, `∑ x ∈ A, (if IsMaxIn (euRel u) x A then 1/2 else 0) = 1/2` (and the same
for `u'`; `Finset.sum_add_distrib`). Take `x₀ ∈ A` maximizing `dot u` (`Finset.exists_max_image`).
By `isMaxIn_euRel_iff` and strictness on `X` (`StrictOn (euRel u) X` says distinct points of `X`
have distinct `u`-values), `IsMaxIn (euRel u) x A ↔ x = x₀` for `x ∈ A`; then
`Finset.sum_ite_eq'`. -/
theorem exists_halfRule {K : ℕ} {X : Finset (Lot K)} {u u' : Lot K}
    (hu : StrictOn (euRel u) X) (hu' : StrictOn (euRel u') X) :
    ∃ ρ : RandomChoiceRule X, ∀ x A, ρ.p x A =
      (if IsMaxIn (euRel u) x A then 1 / 2 else 0) +
        (if IsMaxIn (euRel u') x A then 1 / 2 else 0) := by
  refine ⟨⟨fun x A => (if IsMaxIn (euRel u) x A then 1 / 2 else 0) +
        (if IsMaxIn (euRel u') x A then 1 / 2 else 0), ?_, ?_, ?_⟩, fun x A => rfl⟩
  · intro A _ x
    split_ifs <;> norm_num
  · intro A _ x hx
    have h1 : ¬ IsMaxIn (euRel u) x A := fun h => hx h.1
    have h2 : ¬ IsMaxIn (euRel u') x A := fun h => hx h.1
    simp [h1, h2]
  · intro A hA hne
    rw [Finset.sum_add_distrib, half_sum hu hA hne, half_sum hu' hA hne]
    norm_num

end Q3L
