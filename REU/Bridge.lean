/-
# Bridge lemma

`bridge : bridge_stmt`: for any class `C` of relations, a random choice rule is induced by a
measure-theoretic random preference (probability space `Ω`, `R ω ∈ C` strict on `X`,
measurable "x is the `R ω`-max of `A`" events) iff it is a finite mixture from `C`.

(a) Measure ⇒ mixture: index the finitely many menu–element pairs `P = {(x, A) : A ⊆ X, x ∈ A}`.
Each `ω` has a pattern `pat ω ⊆ P` (the pairs it maximizes). The cells `{ω | pat ω = S}`,
`S ⊆ P`, are measurable and partition `Ω`; weight `w S = μ(cell S)` and pick a representative
`ω_S ∈ cell S` (any point if the cell is empty, in which case its weight is `0`).

(b) Mixture ⇒ measure: `Ω = ULift (Fin n)` with the discrete σ-algebra and
`μ = Σ_i ofReal (w i) • dirac i`.
-/
import REU.Statement

open MeasureTheory

namespace REU

universe u

open Classical in
lemma isMixture_of_finset {C : Rel → Prop} {X : Finset Pt} {ρ : RandomChoiceRule X}
    {ι : Type*} (s : Finset ι) (R : ι → Rel) (w : ι → ℝ)
    (hC : ∀ i ∈ s, C (R i) ∧ StrictOn (R i) X) (hw : ∀ i ∈ s, 0 ≤ w i)
    (hsum : ∑ i ∈ s, w i = 1)
    (hp : ∀ A ⊆ X, A.Nonempty → ∀ x ∈ A,
      ρ.p x A = ∑ i ∈ s, if IsMaxIn (R i) x A then w i else 0) :
    IsMixture C X ρ := by
  classical
  let e : s ≃ Fin s.card := s.equivFin
  have key : ∀ f : ι → ℝ, ∑ j : Fin s.card, f (e.symm j) = ∑ i ∈ s, f i := by
    intro f
    rw [Equiv.sum_comp e.symm (fun i : s => f i), Finset.sum_coe_sort s f]
  refine ⟨s.card, fun j => R (e.symm j), fun j => w (e.symm j),
    fun j => hC _ (e.symm j).2, fun j => hw _ (e.symm j).2, by rw [key w, hsum], ?_⟩
  intro A hA hne x hx
  rw [hp A hA hne x hx, ← key (fun i => if IsMaxIn (R i) x A then w i else 0)]

theorem bridge_a (C : Rel → Prop) (X : Finset Pt) (ρ : RandomChoiceRule X)
    (Ω : Type u) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (R : Ω → Rel)
    (hC : ∀ ω, C (R ω) ∧ StrictOn (R ω) X)
    (hmeas : ∀ A ⊆ X, ∀ x ∈ A, MeasurableSet {ω | IsMaxIn (R ω) x A})
    (hρ : ∀ A ⊆ X, A.Nonempty → ∀ x ∈ A, ρ.p x A = (μ {ω | IsMaxIn (R ω) x A}).toReal) :
    IsMixture C X ρ := by
  classical
  have ω₀ : Ω := (nonempty_of_isProbabilityMeasure μ).some
  -- menu-element pairs `(x, A)` with `A ⊆ X`, `x ∈ A`
  let P : Finset (Pt × Finset Pt) := (X ×ˢ X.powerset).filter (fun p => p.1 ∈ p.2)
  have hP : ∀ p, p ∈ P ↔ (p.1 ∈ X ∧ p.2 ⊆ X) ∧ p.1 ∈ p.2 := by
    intro p; simp [P, Finset.mem_product, Finset.mem_powerset]
  let M : Ω → Pt × Finset Pt → Prop := fun ω p => IsMaxIn (R ω) p.1 p.2
  have hEm : ∀ p ∈ P, MeasurableSet {ω | M ω p} := by
    intro p hp
    obtain ⟨⟨_, hA⟩, hx⟩ := (hP p).1 hp
    exact hmeas p.2 hA p.1 hx
  let pat : Ω → Finset (Pt × Finset Pt) := fun ω => P.filter (M ω)
  let cell : Finset (Pt × Finset Pt) → Set Ω := fun S => {ω | pat ω = S}
  have hpat_mem : ∀ ω p, p ∈ pat ω ↔ p ∈ P ∧ M ω p := fun ω p => Finset.mem_filter
  have hcell_eq : ∀ S ∈ P.powerset, cell S = ⋂ p ∈ P, {ω | p ∈ S ↔ M ω p} := by
    intro S hS
    rw [Finset.mem_powerset] at hS
    ext ω
    simp only [cell, Set.mem_ofPred_eq, Set.mem_iInter]
    constructor
    · rintro h p hp
      rw [← h, hpat_mem]
      exact ⟨fun h' => h'.2, fun h' => ⟨hp, h'⟩⟩
    · intro h
      ext p
      rw [hpat_mem]
      by_cases hp : p ∈ P
      · exact ⟨fun h' => (h p hp).2 h'.2, fun h' => ⟨hp, (h p hp).1 h'⟩⟩
      · exact ⟨fun h' => absurd h'.1 hp, fun h' => absurd (hS h') hp⟩
  have hcellm : ∀ S ∈ P.powerset, MeasurableSet (cell S) := by
    intro S hS
    rw [hcell_eq S hS]
    refine Finset.measurableSet_biInter P (fun p hp => ?_)
    by_cases hpS : p ∈ S
    · simpa [hpS] using hEm p hp
    · have e : {ω | p ∈ S ↔ M ω p} = {ω | M ω p}ᶜ := by
        ext ω; simp [hpS]
      rw [e]; exact (hEm p hp).compl
  have hdisj : ∀ T : Finset (Finset (Pt × Finset Pt)), Set.PairwiseDisjoint (↑T) cell := by
    intro T S _ S' _ hne
    refine Set.disjoint_left.2 (fun ω h1 h2 => hne ?_)
    exact h1.symm.trans h2
  have hunion : ∀ T ⊆ P.powerset, μ (⋃ S ∈ T, cell S) = ∑ S ∈ T, μ (cell S) :=
    fun T hT => measure_biUnion_finset (hdisj T) (fun S hS => hcellm S (hT hS))
  have hpatP : ∀ ω, pat ω ∈ P.powerset := fun ω => Finset.mem_powerset.2 (Finset.filter_subset _ _)
  -- weights and representatives
  let w : Finset (Pt × Finset Pt) → ℝ := fun S => (μ (cell S)).toReal
  let rep : Finset (Pt × Finset Pt) → Ω := fun S =>
    if h : (cell S).Nonempty then h.some else ω₀
  have hrep : ∀ S, w S ≠ 0 → pat (rep S) = S := by
    intro S hw
    have hne : (cell S).Nonempty := by
      refine nonempty_of_measure_ne_zero (μ := μ) ?_
      intro h0; apply hw; simp [w, h0]
    have : rep S = hne.some := dite_eq_left hne
    rw [this]
    exact hne.some_mem
  have htoReal : ∀ T ⊆ P.powerset, (μ (⋃ S ∈ T, cell S)).toReal = ∑ S ∈ T, w S := by
    intro T hT
    rw [hunion T hT, ENNReal.toReal_sum (fun S _ => measure_ne_top μ _)]
  refine isMixture_of_finset (P.powerset) (fun S => R (rep S)) w
    (fun S _ => hC _) (fun S _ => ENNReal.toReal_nonneg) ?_ ?_
  · have huniv : (⋃ S ∈ P.powerset, cell S) = Set.univ := by
      refine Set.eq_univ_of_forall (fun ω => Set.mem_biUnion (hpatP ω) rfl)
    rw [← htoReal _ subset_rfl, huniv, measure_univ, ENNReal.toReal_one]
  · intro A hA hne x hx
    have hp0 : (x, A) ∈ P := (hP _).2 ⟨⟨hA hx, hA⟩, hx⟩
    have hE : {ω | IsMaxIn (R ω) x A} =
        ⋃ S ∈ P.powerset.filter (fun S => (x, A) ∈ S), cell S := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Finset.mem_filter, exists_prop]
      constructor
      · intro h
        exact ⟨pat ω, ⟨hpatP ω, (hpat_mem ω _).2 ⟨hp0, h⟩⟩, rfl⟩
      · rintro ⟨S, ⟨_, hS⟩, hω⟩
        have : (x, A) ∈ pat ω := by
          show (x, A) ∈ pat ω
          have hω' : pat ω = S := hω
          rw [hω']; exact hS
        exact ((hpat_mem ω _).1 this).2
    rw [hρ A hA hne x hx, hE, htoReal _ (Finset.filter_subset _ _), Finset.sum_filter]
    refine Finset.sum_congr rfl (fun S _ => ?_)
    by_cases hw0 : w S = 0
    · simp [hw0]
    · have h1 : pat (rep S) = S := hrep S hw0
      have h2 : ((x, A) ∈ S) ↔ IsMaxIn (R (rep S)) x A := by
        have h3 := hpat_mem (rep S) (x, A)
        rw [h1] at h3
        exact h3.trans ⟨fun h => h.2, fun h => ⟨hp0, h⟩⟩
      by_cases hm : (x, A) ∈ S
      · rw [ite_eq_left hm, ite_eq_left (h2.1 hm)]
      · have hn : ¬ IsMaxIn (R (rep S)) x A := fun h => hm (h2.2 h)
        rw [ite_eq_right hm, ite_eq_right hn]

theorem bridge_b (C : Rel → Prop) (X : Finset Pt) (ρ : RandomChoiceRule X)
    (h : IsMixture C X ρ) :
    ∃ (Ω : Type u) (_ : MeasurableSpace Ω) (μ : Measure Ω) (R : Ω → Rel),
        IsProbabilityMeasure μ ∧
        (∀ ω, C (R ω) ∧ StrictOn (R ω) X) ∧
        (∀ A ⊆ X, ∀ x ∈ A, MeasurableSet {ω | IsMaxIn (R ω) x A}) ∧
        (∀ A ⊆ X, A.Nonempty → ∀ x ∈ A, ρ.p x A = (μ {ω | IsMaxIn (R ω) x A}).toReal) := by
  classical
  obtain ⟨n, R, w, hCR, hw, hsum, hρ⟩ := h
  let _ : MeasurableSpace (ULift.{u} (Fin n)) := ⊤
  let μ : Measure (ULift.{u} (Fin n)) :=
    ∑ i, ENNReal.ofReal (w i) • Measure.dirac (ULift.up i)
  have hμ : ∀ s : Set (ULift.{u} (Fin n)),
      μ s = ∑ i, ENNReal.ofReal (w i) * s.indicator 1 (ULift.up i) := by
    intro s
    simp only [μ, Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply, smul_eq_mul]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Measure.dirac_apply' _ (MeasurableSpace.measurableSet_top)]
  refine ⟨ULift.{u} (Fin n), ⊤, μ, fun ω => R ω.down, ⟨?_⟩, fun ω => hCR ω.down,
    fun _ _ _ _ => MeasurableSpace.measurableSet_top, ?_⟩
  · rw [hμ]
    simp only [Set.indicator_univ, Pi.one_apply, mul_one]
    rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => hw i), hsum, ENNReal.ofReal_one]
  · intro A _ _ x _
    rw [hρ A ‹_› ‹_› x ‹_›, hμ, ENNReal.toReal_sum]
    · refine Finset.sum_congr rfl (fun i _ => ?_)
      by_cases hM : IsMaxIn (R i) x A
      · simp [Set.indicator, hM, ENNReal.toReal_ofReal (hw i)]
      · simp [Set.indicator, hM]
    · intro i _
      exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
        (by unfold Set.indicator; split_ifs <;> simp)

/-- The bridge lemma, at every universe level. -/
theorem bridge : bridge_stmt.{u} := fun C X ρ =>
  ⟨fun Ω _ μ _ R hC hm hρ => bridge_a C X ρ Ω μ R hC hm hρ, bridge_b C X ρ⟩

end REU
