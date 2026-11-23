/-
`exists_three_points`: a 2-dimensional `X` has three affinely independent
points.
-/
import Q3L.Statement

namespace Q3L

open K4 (Lot)

/-- If `dim V = 2`, there are `a, b, c ∈ X` with `a - b, b - c` linearly independent.
Sketch. `X` is nonempty (else `vectorSpan ℝ ∅ = ⊥`, `finrank = 0`). Fix `b ∈ X`.
`vectorSpan_eq_span_vsub_set_right ℝ hb : vectorSpan ℝ X = span ((· -ᵥ b) '' X)`. By
`exists_linearIndependent ℝ ((· -ᵥ b) '' X)` there is `T ⊆ (· -ᵥ b) '' X`, linearly
independent, with the same span; so `T` is a basis of `dirSpace X` and has cardinality `2`
(`finrank_span_set_eq_card` / `LinearIndependent.finrank_span_eq_card` with `hdim`). Two
distinct elements `a - b`, `c - b` of `T` (`Set.ncard_eq_two` or `Finset.card_eq_two` after
`T.toFinite.toFinset`) are linearly independent (`LinearIndependent.pair_iff` via
`linearIndependent_subtype`/`LinearIndependent.mono`). Then `![a - b, b - c]` is
independent: `s • (a - b) + t • (b - c) = s • (a - b) + (-t) • (c - b)`
(`LinearIndependent.pair_iff`). -/
theorem exists_three_points {K : ℕ} {X : Finset (Lot K)}
    (hdim : Module.finrank ℝ (dirSpace X) = 2) :
    ∃ a ∈ X, ∃ b ∈ X, ∃ c ∈ X, LinearIndependent ℝ ![a - b, b - c] := by
  classical
  have hne : X.Nonempty := by
    rcases X.eq_empty_or_nonempty with h | h
    · subst h
      exfalso
      have : dirSpace (∅ : Finset (Lot K)) = ⊥ := by
        simp [dirSpace]
      rw [this, finrank_bot] at hdim
      exact absurd hdim (by norm_num)
    · exact h
  obtain ⟨b, hb⟩ := hne
  have hspan : dirSpace X = Submodule.span ℝ ((· -ᵥ b) '' (↑X : Set (Lot K))) :=
    vectorSpan_eq_span_vsub_set_right ℝ (Finset.mem_coe.mpr hb)
  obtain ⟨T, hTS, hTspan, hTli⟩ :=
    exists_linearIndependent ℝ ((· -ᵥ b) '' (↑X : Set (Lot K)))
  have hTfin : T.Finite := ((X.finite_toSet.image _)).subset hTS
  letI : Fintype T := hTfin.fintype
  have hcard : T.toFinset.card = 2 := by
    rw [← finrank_span_set_eq_card hTli, hTspan, ← hspan, hdim]
  obtain ⟨x, y, hxy, hTeq⟩ := Finset.card_eq_two.mp hcard
  have hx : x ∈ T := by
    have : x ∈ T.toFinset := by rw [hTeq]; simp
    simpa using this
  have hy : y ∈ T := by
    have : y ∈ T.toFinset := by rw [hTeq]; simp
    simpa using this
  obtain ⟨a, ha, rfl⟩ := hTS hx
  obtain ⟨c, hc, rfl⟩ := hTS hy
  have hpair : LinearIndependent ℝ ![a -ᵥ b, c -ᵥ b] := by
    have hf : Function.Injective (![⟨_, hx⟩, ⟨_, hy⟩] : Fin 2 → T) := by
      intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all [Subtype.ext_iff]
    have := hTli.comp _ hf
    convert this using 1
    funext i
    fin_cases i <;> rfl
  refine ⟨a, Finset.mem_coe.mp ha, b, hb, c, Finset.mem_coe.mp hc, ?_⟩
  rw [LinearIndependent.pair_iff] at hpair ⊢
  intro s t hst
  have h2 := hpair s (-t) (by
    simp only [vsub_eq_sub] at *
    rw [← hst]; simp only [neg_smul, smul_sub]; abel)
  exact ⟨h2.1, neg_eq_zero.mp h2.2⟩

end Q3L
