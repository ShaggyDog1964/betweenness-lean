/-
# Necessity (`⇒` of Theorem 1)

A finite mixture of betweenness preferences, each strict on `X ⊆ Tri`, satisfies Chord
Dominance and Bracketing.

* Pair values: `ρ(x, {x, y}) = mass w [x ≻_i y]`.
* CD-dom from strict FOSD monotonicity; CD-cross / CD-col from `chord_iff_tau`, evaluated at a
  common point `y` of the two chord lines (for CD-col, `y = c`).
* Bracketing: fix `x ∈ A` and put `τ_i = tau x` for component `i`. Against `b ∈ A_SW(x)`,
  `x ≻_i b ↔ (NE x b → τ_i < slope x b)` (down-closed in `τ_i`); against `a ∈ A_NE(x)`,
  `x ≻_i a ↔ NE a x ∧ slope a x < τ_i` (up-closed). So `x` is the max iff a down-closed and an
  up-closed event both occur (`max_iff_tau_interval`); nested events give the `minOr1`s and
  `sum_threshold_inter` gives the `max 0 (· + · - 1)`. No vertex case split is needed.
* `bracketing_placement_insensitive`: under CD-dom, moving FOSD-comparable points between the
  two sides does not change the Bracketing formula.
-/
import REU.MixtureBasics

namespace REU

variable {R : Rel}

/-! ## Elementary geometry and preference facts -/

lemma ne_of_NE {a b : Pt} (h : NE a b) : a ≠ b := by
  rintro rfl; exact lt_irrefl _ h.1

lemma onLine_self_left (a b : Pt) : OnLine a b a := by
  unfold OnLine; ring

lemma onLine_self_right (a b : Pt) : OnLine a b b := by
  unfold OnLine; ring

/-- Two chords whose four endpoints are collinear have the same slope. -/
lemma slope_eq_of_collinear4 {a b c d : Pt} (hab : NE a b) (hcd : NE c d)
    (h : collinear4 a b c d) : slope c d = slope a b := by
  obtain ⟨h1, h2⟩ := h
  unfold OnLine at h1 h2
  unfold slope
  rw [div_eq_div_iff (sub_pos.2 hcd.1).ne' (sub_pos.2 hab.1).ne']
  linear_combination h1 - h2

/-- In `Tri`, a point `y ≠ x` is NE of `x`, SW of `x`, or FOSD-comparable with `x`. -/
lemma tri_cases {x y : Pt} (hx : x ∈ Tri) (hy : y ∈ Tri) (hne : y ≠ x) :
    NE y x ∨ NE x y ∨ StrictFOSD x y ∨ StrictFOSD y x := by
  by_cases h1 : FOSD x y
  · exact Or.inr (Or.inr (Or.inl ⟨h1, Ne.symm hne⟩))
  · by_cases h2 : FOSD y x
    · exact Or.inr (Or.inr (Or.inr ⟨h2, hne⟩))
    · rcases (incomparable_iff_NE hy hx hne).1 ⟨h2, h1⟩ with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)

lemma mem_ANE {A : Finset Pt} {x a : Pt} :
    a ∈ ANE A x ↔ a ∈ A ∧ a ≠ x ∧ (NE a x ∨ StrictFOSD a x) := by
  classical
  unfold ANE; exact Finset.mem_filter

lemma mem_ASW {A : Finset Pt} {x b : Pt} :
    b ∈ ASW A x ↔ b ∈ A ∧ b ≠ x ∧ ¬ (NE b x ∨ StrictFOSD b x) := by
  classical
  unfold ASW; exact Finset.mem_filter

/-- Elements of `A_SW(x)` (in `Tri`) are dominated by `x` or strictly SW of `x`. -/
lemma ASW_cases {A : Finset Pt} {x b : Pt} (hx : x ∈ Tri) (hb : b ∈ Tri) (h : b ∈ ASW A x) :
    StrictFOSD x b ∨ NE x b := by
  obtain ⟨_, hne, hn⟩ := mem_ASW.1 h
  rcases tri_cases hx hb hne with h | h | h | h
  · exact absurd (Or.inl h) hn
  · exact Or.inr h
  · exact Or.inl h
  · exact absurd (Or.inr h) hn

/-- For a strict pair, `x ≻ a ↔ ¬ a ≻ x`. -/
lemma spref_iff_not_spref (hR : IsBetweennessPref R) {X : Finset Pt} (hS : StrictOn R X)
    {x a : Pt} (hxX : x ∈ X) (haX : a ∈ X) (hxT : x ∈ Tri) (haT : a ∈ Tri) (hne : x ≠ a) :
    SPref R x a ↔ ¬ SPref R a x := by
  have hc := hR.complete x hxT a haT
  have hs := hS x hxX a haX hne
  unfold SPref
  tauto

lemma pair_subset {X : Finset Pt} {x y : Pt} (hx : x ∈ X) (hy : y ∈ X) :
    ({x, y} : Finset Pt) ⊆ X :=
  Finset.insert_subset_iff.2 ⟨hx, Finset.singleton_subset_iff.2 hy⟩

lemma isMaxIn_pair_iff {x y : Pt} (hne : x ≠ y) : IsMaxIn R x {x, y} ↔ SPref R x y := by
  constructor
  · rintro ⟨_, h⟩; exact h y (by simp) (Ne.symm hne)
  · intro h
    refine ⟨by simp, fun z hz hzx => ?_⟩
    rcases Finset.mem_insert.1 hz with rfl | hz
    · exact absurd rfl hzx
    · rw [Finset.mem_singleton.1 hz]; exact h

/-- `x` is the max of `A` iff it beats every element of `A_SW(x)` and of `A_NE(x)`. -/
lemma isMaxIn_iff_split {A : Finset Pt} {x : Pt} (hx : x ∈ A) :
    IsMaxIn R x A ↔ (∀ b ∈ ASW A x, SPref R x b) ∧ (∀ a ∈ ANE A x, SPref R x a) := by
  constructor
  · rintro ⟨_, h⟩
    exact ⟨fun b hb => h b (mem_ASW.1 hb).1 (mem_ASW.1 hb).2.1,
      fun a ha => h a (mem_ANE.1 ha).1 (mem_ANE.1 ha).2.1⟩
  · rintro ⟨hSW, hNE⟩
    refine ⟨hx, fun y hy hyx => ?_⟩
    by_cases hc : NE y x ∨ StrictFOSD y x
    · exact hNE y (mem_ANE.2 ⟨hy, hyx, hc⟩)
    · exact hSW y (mem_ASW.2 ⟨hy, hyx, hc⟩)

/-! ## One preference: `x` against SW and NE points, via `tau x` -/

/-- Against `b ∈ A_SW(x)`: `x ≻ b ↔ (NE x b → tau x < slope x b)`. -/
lemma spref_ASW_iff (hR : IsBetweennessPref R) {X : Finset Pt} (hX : (↑X : Set Pt) ⊆ Tri)
    (hS : StrictOn R X) {A : Finset Pt} (hA : A ⊆ X) {x b : Pt} (hx : x ∈ A)
    (hb : b ∈ ASW A x) : SPref R x b ↔ (NE x b → tau hR x < slope x b) := by
  have hxX := hA hx
  have hb' := mem_ASW.1 hb
  have hbX := hA hb'.1
  have hxT : x ∈ Tri := hX hxX
  have hbT : b ∈ Tri := hX hbX
  rcases ASW_cases hxT hbT hb with hd | hne
  · have hnNE : ¬ NE x b := fun h => by linarith [h.1, hd.1.1]
    exact ⟨fun _ h => absurd h hnNE, fun _ => hR.strictMono x hxT b hbT hd⟩
  · rw [chord_iff_tau hR hxT hxT hbT hne (onLine_self_left x b)
      (fun hi => hS x hxX b hbX (Ne.symm hb'.2.1) hi)]
    exact ⟨fun h _ => h, fun h => h hne⟩

/-- Against `a ∈ A_NE(x)`: `x ≻ a ↔ NE a x ∧ slope a x < tau x` (strict: equality would make
`a ∼ x`). -/
lemma spref_ANE_iff (hR : IsBetweennessPref R) {X : Finset Pt} (hX : (↑X : Set Pt) ⊆ Tri)
    (hS : StrictOn R X) {A : Finset Pt} (hA : A ⊆ X) {x a : Pt} (hx : x ∈ A)
    (ha : a ∈ ANE A x) : SPref R x a ↔ (NE a x ∧ slope a x < tau hR x) := by
  have hxX := hA hx
  have ha' := mem_ANE.1 ha
  have haX := hA ha'.1
  have hxT : x ∈ Tri := hX hxX
  have haT : a ∈ Tri := hX haX
  rcases ha'.2.2 with hne | hd
  · have hnot : ¬ Indiff R a x := fun hi => hS a haX x hxX ha'.2.1 hi
    have key := chord_iff_tau hR hxT haT hxT hne (onLine_self_right a x) hnot
    rw [spref_iff_not_spref hR hS hxX haX hxT haT (Ne.symm ha'.2.1), key, not_lt]
    constructor
    · intro hle
      refine ⟨hne, lt_of_le_of_ne hle fun heq => hnot ?_⟩
      obtain ⟨hW, hB⟩ := chord_line_avoids_vertices haT hxT hne (onLine_self_right a x)
      refine ((level_is_segment hR hxT hW hB).2 a haT).2 ?_
      have hd : 0 < a.1 - x.1 := by linarith [hne.1]
      unfold slope at heq
      rw [← heq, div_mul_cancel₀ _ hd.ne']
    · rintro ⟨_, h⟩; exact h.le
  · have hsp := hR.strictMono a haT x hxT hd
    have hnNE : ¬ NE a x := fun h => by linarith [h.1, hd.1.1]
    exact ⟨fun h => absurd hsp.1 h.2, fun h => absurd h.1 hnNE⟩

/-- **`x` is the `R`-max of `A` iff `tau x` lies strictly between the slopes**: above every
NE-chord slope `slope a x` (and there is no dominator of `x` in `A`), below every SW-chord slope
`slope x b`. Holds for every `x ∈ A` (at the vertices `W`, `B` the chord conditions are vacuous
or impossible). -/
theorem max_iff_tau_interval (hR : IsBetweennessPref R) {X : Finset Pt}
    (hX : (↑X : Set Pt) ⊆ Tri) (hS : StrictOn R X) {A : Finset Pt} (hA : A ⊆ X) {x : Pt}
    (hx : x ∈ A) :
    IsMaxIn R x A ↔ (∀ b ∈ ASW A x, NE x b → tau hR x < slope x b) ∧
      (∀ a ∈ ANE A x, NE a x ∧ slope a x < tau hR x) := by
  rw [isMaxIn_iff_split hx]
  exact and_congr (forall₂_congr fun b hb => spref_ASW_iff hR hX hS hA hx hb)
    (forall₂_congr fun a ha => spref_ANE_iff hR hX hS hA hx ha)

/-! ## The mixture -/

section Mixture

variable {X : Finset Pt} (ρ : RandomChoiceRule X) {n : ℕ} {Rs : Fin n → Rel} {w : Fin n → ℝ}

/-- Pair values of a mixture. -/
lemma pair_eq_mass
    (hρ : ∀ A ⊆ X, A.Nonempty → ∀ x ∈ A, ρ.p x A = mass w (fun i => IsMaxIn (Rs i) x A))
    {x y : Pt} (hx : x ∈ X) (hy : y ∈ X) (hne : x ≠ y) :
    ρ.p x {x, y} = mass w (fun i => SPref (Rs i) x y) := by
  rw [hρ {x, y} (pair_subset hx hy) (Finset.insert_nonempty x {y}) x
    (Finset.mem_insert_self x {y})]
  exact mass_congr w fun i => isMaxIn_pair_iff hne

theorem cdDom_of_mixture (hRS : ∀ i, IsBetweennessPref (Rs i) ∧ StrictOn (Rs i) X)
    (hX : (↑X : Set Pt) ⊆ Tri)
    (hρ : ∀ A ⊆ X, A.Nonempty → ∀ x ∈ A, ρ.p x A = mass w (fun i => IsMaxIn (Rs i) x A)) :
    CDDom X ρ := by
  intro q hq r hr hqr
  have hne : q ≠ r := hqr.2
  rw [hρ {q, r} (pair_subset hq hr) (Finset.insert_nonempty _ _) r (by simp)]
  have hF : ∀ i, IsMaxIn (Rs i) r {q, r} ↔ False := fun i =>
    ⟨fun h => (h.2 q (by simp) hne).2 ((hRS i).1.strictMono q (hX hq) r (hX hr) hqr).1,
      False.elim⟩
  rw [mass_congr w hF]
  exact mass_false w

theorem cdCross_of_mixture (hRS : ∀ i, IsBetweennessPref (Rs i) ∧ StrictOn (Rs i) X)
    (hw : ∀ i, 0 ≤ w i) (hX : (↑X : Set Pt) ⊆ Tri)
    (hρ : ∀ A ⊆ X, A.Nonempty → ∀ x ∈ A, ρ.p x A = mass w (fun i => IsMaxIn (Rs i) x A)) :
    ∀ a b c d, IsChord X a b → IsChord X c d →
      linesMeetInTri a b c d → slope c d < slope a b → fChord ρ c d ≤ fChord ρ a b := by
  rintro a b c d ⟨haX, hbX, hab⟩ ⟨hcX, hdX, hcd⟩ ⟨y, hy, hyab, hycd⟩ hslope
  unfold fChord
  rw [pair_eq_mass ρ hρ hcX hdX (ne_of_NE hcd), pair_eq_mass ρ hρ haX hbX (ne_of_NE hab)]
  refine mass_mono hw fun i h => ?_
  have k1 := chord_iff_tau (hRS i).1 hy (hX hcX) (hX hdX) hcd hycd
    (fun hi => (hRS i).2 c hcX d hdX (ne_of_NE hcd) hi)
  have k2 := chord_iff_tau (hRS i).1 hy (hX haX) (hX hbX) hab hyab
    (fun hi => (hRS i).2 a haX b hbX (ne_of_NE hab) hi)
  exact k2.2 ((k1.1 h).trans hslope)

theorem cdCol_of_mixture (hRS : ∀ i, IsBetweennessPref (Rs i) ∧ StrictOn (Rs i) X)
    (hX : (↑X : Set Pt) ⊆ Tri)
    (hρ : ∀ A ⊆ X, A.Nonempty → ∀ x ∈ A, ρ.p x A = mass w (fun i => IsMaxIn (Rs i) x A)) :
    ∀ a b c d, IsChord X a b → IsChord X c d →
      collinear4 a b c d → fChord ρ a b = fChord ρ c d := by
  rintro a b c d ⟨haX, hbX, hab⟩ ⟨hcX, hdX, hcd⟩ hcol
  unfold fChord
  rw [pair_eq_mass ρ hρ haX hbX (ne_of_NE hab), pair_eq_mass ρ hρ hcX hdX (ne_of_NE hcd)]
  have hsl := slope_eq_of_collinear4 hab hcd hcol
  refine mass_congr w fun i => ?_
  have k1 := chord_iff_tau (hRS i).1 (hX hcX) (hX haX) (hX hbX) hab hcol.1
    (fun hi => (hRS i).2 a haX b hbX (ne_of_NE hab) hi)
  have k2 := chord_iff_tau (hRS i).1 (hX hcX) (hX hcX) (hX hdX) hcd (onLine_self_left c d)
    (fun hi => (hRS i).2 c hcX d hdX (ne_of_NE hcd) hi)
  rw [k1, k2, hsl]

theorem bracketing_of_mixture (hRS : ∀ i, IsBetweennessPref (Rs i) ∧ StrictOn (Rs i) X)
    (hw : ∀ i, 0 ≤ w i) (hsum : ∑ i, w i = 1) (hX : (↑X : Set Pt) ⊆ Tri)
    (hρ : ∀ A ⊆ X, A.Nonempty → ∀ x ∈ A, ρ.p x A = mass w (fun i => IsMaxIn (Rs i) x A)) :
    Bracketing X ρ := by
  intro A hA x hx
  have hxX := hA hx
  set τ : Fin n → ℝ := fun i => tau (hRS i).1 x with hτ
  have hSW : ∀ b ∈ ASW A x, ∀ i, SPref (Rs i) x b ↔ (NE x b → τ i < slope x b) :=
    fun b hb i => spref_ASW_iff (hRS i).1 hX (hRS i).2 hA hx hb
  have hNE : ∀ a ∈ ANE A x, ∀ i, SPref (Rs i) x a ↔ (NE a x ∧ slope a x < τ i) :=
    fun a ha i => spref_ANE_iff (hRS i).1 hX (hRS i).2 hA hx ha
  -- per-chord events: SW ones down-closed, NE ones up-closed in `τ`
  have dSW : ∀ b ∈ ASW A x, ∀ i j, τ j ≤ τ i → SPref (Rs i) x b → SPref (Rs j) x b :=
    fun b hb i j hij h => (hSW b hb j).2 fun hn => lt_of_le_of_lt hij ((hSW b hb i).1 h hn)
  have uNE : ∀ a ∈ ANE A x, ∀ i j, τ i ≤ τ j → SPref (Rs i) x a → SPref (Rs j) x a :=
    fun a ha i j hij h =>
      (hNE a ha j).2 ⟨((hNE a ha i).1 h).1, lt_of_lt_of_le ((hNE a ha i).1 h).2 hij⟩
  have e1 : mass w (fun i => ∀ b ∈ ASW A x, SPref (Rs i) x b) =
      minOr1 (ASW A x) (fun b => ρ.p x {x, b}) := by
    refine (mass_forall_down hw hsum τ (ASW A x) (fun b i => SPref (Rs i) x b) dSW).trans
      (minOr1_congr fun b hb => ?_)
    exact (pair_eq_mass ρ hρ hxX (hA (mem_ASW.1 hb).1) (Ne.symm (mem_ASW.1 hb).2.1)).symm
  have e2 : mass w (fun i => ∀ a ∈ ANE A x, SPref (Rs i) x a) =
      minOr1 (ANE A x) (fun a => ρ.p x {x, a}) := by
    refine (mass_forall_up hw hsum τ (ANE A x) (fun a i => SPref (Rs i) x a) uNE).trans
      (minOr1_congr fun a ha => ?_)
    exact (pair_eq_mass ρ hρ hxX (hA (mem_ANE.1 ha).1) (Ne.symm (mem_ANE.1 ha).2.1)).symm
  have hE : ∀ i j, τ j ≤ τ i → (∀ b ∈ ASW A x, SPref (Rs i) x b) →
      (∀ b ∈ ASW A x, SPref (Rs j) x b) := fun i j hij h b hb => dSW b hb i j hij (h b hb)
  have hF : ∀ i j, τ i ≤ τ j → (∀ a ∈ ANE A x, SPref (Rs i) x a) →
      (∀ a ∈ ANE A x, SPref (Rs j) x a) := fun i j hij h a ha => uNE a ha i j hij (h a ha)
  rw [hρ A hA ⟨x, hx⟩ x hx, mass_congr w fun i => isMaxIn_iff_split hx,
    sum_threshold_inter hw hsum τ hE hF, e1, e2]

end Mixture

/-- **Necessity (⇒ of Theorem 1).** -/
theorem necessity {X : Finset Pt} (hX : (↑X : Set Pt) ⊆ Tri) (ρ : RandomChoiceRule X) :
    IsMixture IsBetweennessPref X ρ → ChordDominance X ρ ∧ Bracketing X ρ := by
  rintro ⟨n, Rs, w, hRS, hw, hsum, hρ⟩
  have hρ' : ∀ A ⊆ X, A.Nonempty → ∀ x ∈ A,
      ρ.p x A = mass w (fun i => IsMaxIn (Rs i) x A) := hρ
  exact ⟨⟨cdDom_of_mixture ρ hRS hX hρ', cdCross_of_mixture ρ hRS hw hX hρ',
    cdCol_of_mixture ρ hRS hX hρ'⟩, bracketing_of_mixture ρ hRS hw hsum hX hρ'⟩

/-! ## Placement insensitivity of Bracketing -/

section Placement

variable {X : Finset Pt} (ρ : RandomChoiceRule X)

lemma pair_nonneg {x y : Pt} (hx : x ∈ X) (hy : y ∈ X) : 0 ≤ ρ.p x {x, y} :=
  ρ.nonneg _ (pair_subset hx hy) _

lemma pair_le_one {x y : Pt} (hx : x ∈ X) (hy : y ∈ X) (hne : x ≠ y) : ρ.p x {x, y} ≤ 1 := by
  have h := ρ.sum_one {x, y} (pair_subset hx hy) (Finset.insert_nonempty _ _)
  rw [Finset.sum_pair hne] at h
  linarith [ρ.nonneg {x, y} (pair_subset hx hy) y]

lemma pair_eq_one_of_strictFOSD (hCD : CDDom X ρ) {x y : Pt} (hx : x ∈ X) (hy : y ∈ X)
    (h : StrictFOSD x y) : ρ.p x {x, y} = 1 := by
  have h0 := hCD x hx y hy h
  have h1 := ρ.sum_one {x, y} (pair_subset hx hy) (Finset.insert_nonempty _ _)
  rw [Finset.sum_pair h.2] at h1
  linarith

lemma pair_eq_zero_of_dominator (hCD : CDDom X ρ) {x d : Pt} (hx : x ∈ X) (hd : d ∈ X)
    (h : StrictFOSD d x) : ρ.p x {x, d} = 0 := by
  rw [Finset.pair_comm]; exact hCD d hd x hx h

/-- General placement lemma: any split `S ∪ N = A \ {x}` with no NE point of `x` in `S` and no
SW point of `x` in `N` gives the same Bracketing value as the canonical `A_SW`, `A_NE`. -/
theorem bracketing_formula_placement (hX : (↑X : Set Pt) ⊆ Tri) (hCD : CDDom X ρ)
    {A : Finset Pt} (hA : A ⊆ X) {x : Pt} (hx : x ∈ A) (S N : Finset Pt)
    (hcover : ∀ y, (y ∈ S ∨ y ∈ N) ↔ (y ∈ A ∧ y ≠ x))
    (hS : ∀ y ∈ S, ¬ NE y x) (hN : ∀ y ∈ N, ¬ NE x y) :
    max 0 (minOr1 S (fun b => ρ.p x {x, b}) + minOr1 N (fun a => ρ.p x {x, a}) - 1) =
      max 0 (minOr1 (ASW A x) (fun b => ρ.p x {x, b}) +
        minOr1 (ANE A x) (fun a => ρ.p x {x, a}) - 1) := by
  set g : Pt → ℝ := fun y => ρ.p x {x, y} with hg
  have hxX := hA hx
  have hxT : x ∈ Tri := hX hxX
  have g1 : ∀ y ∈ A, y ≠ x → g y ≤ 1 := fun y hy hyx => pair_le_one ρ hxX (hA hy) (Ne.symm hyx)
  have g0 : ∀ y ∈ A, 0 ≤ g y := fun y hy => pair_nonneg ρ hxX (hA hy)
  have hSA : ∀ y ∈ S, y ∈ A ∧ y ≠ x := fun y hy => (hcover y).1 (Or.inl hy)
  have hNA : ∀ y ∈ N, y ∈ A ∧ y ≠ x := fun y hy => (hcover y).1 (Or.inr hy)
  have bS : ∀ y ∈ S, g y ≤ 1 := fun y hy => g1 y (hSA y hy).1 (hSA y hy).2
  have bN : ∀ y ∈ N, g y ≤ 1 := fun y hy => g1 y (hNA y hy).1 (hNA y hy).2
  have bSW : ∀ y ∈ ASW A x, g y ≤ 1 := fun y hy => g1 y (mem_ASW.1 hy).1 (mem_ASW.1 hy).2.1
  have bNE : ∀ y ∈ ANE A x, g y ≤ 1 := fun y hy => g1 y (mem_ANE.1 hy).1 (mem_ANE.1 hy).2.1
  by_cases hdom : ∃ d ∈ A, StrictFOSD d x
  · obtain ⟨d, hdA, hd⟩ := hdom
    have gd : g d = 0 := pair_eq_zero_of_dominator ρ hCD hxX (hA hdA) hd
    have z : ∀ T : Finset Pt, d ∈ T → (∀ y ∈ T, y ∈ A) → minOr1 T g = 0 :=
      fun T hdT hTA => minOr1_eq_zero hdT gd fun y hy => g0 y (hTA y hy)
    have hzero : ∀ m1 m2 : ℝ, m1 ≤ 1 → m2 ≤ 1 → (m1 = 0 ∨ m2 = 0) → max 0 (m1 + m2 - 1) = 0 := by
      intro m1 m2 h1 h2 h
      rcases h with h | h <;> rw [h] <;> exact max_eq_left (by linarith)
    have hR : minOr1 (ANE A x) g = 0 :=
      z _ (mem_ANE.2 ⟨hdA, hd.2, Or.inr hd⟩) fun y hy => (mem_ANE.1 hy).1
    have hL : minOr1 S g = 0 ∨ minOr1 N g = 0 := by
      rcases (hcover d).2 ⟨hdA, hd.2⟩ with h | h
      · exact Or.inl (z S h fun y hy => (hSA y hy).1)
      · exact Or.inr (z N h fun y hy => (hNA y hy).1)
    rw [hzero _ _ (minOr1_le_one bS) (minOr1_le_one bN) hL,
      hzero _ _ (minOr1_le_one bSW) (minOr1_le_one bNE) (Or.inr hR)]
  · push Not at hdom
    have one : ∀ y ∈ A, StrictFOSD x y → g y = 1 :=
      fun y hy h => pair_eq_one_of_strictFOSD ρ hCD hxX (hA hy) h
    have eS : minOr1 S g = minOr1 (ASW A x) g := by
      refine minOr1_congr_one bS bSW (fun y hy hn => ?_) (fun y hy hn => ?_)
      · exfalso
        obtain ⟨hyA, hyx⟩ := hSA y hy
        refine hn (mem_ASW.2 ⟨hyA, hyx, ?_⟩)
        rintro (h | h)
        · exact hS y hy h
        · exact hdom y hyA h
      · obtain ⟨hyA, hyx, hc⟩ := mem_ASW.1 hy
        have hyN : y ∈ N := ((hcover y).2 ⟨hyA, hyx⟩).resolve_left hn
        rcases tri_cases hxT (hX (hA hyA)) hyx with h | h | h | h
        · exact absurd (Or.inl h) hc
        · exact absurd h (hN y hyN)
        · exact one y hyA h
        · exact absurd (Or.inr h) hc
    have eN : minOr1 N g = minOr1 (ANE A x) g := by
      refine minOr1_congr_one bN bNE (fun y hy hn => ?_) (fun y hy hn => ?_)
      · obtain ⟨hyA, hyx⟩ := hNA y hy
        have hc : ¬ (NE y x ∨ StrictFOSD y x) := fun hc => hn (mem_ANE.2 ⟨hyA, hyx, hc⟩)
        rcases tri_cases hxT (hX (hA hyA)) hyx with h | h | h | h
        · exact absurd (Or.inl h) hc
        · exact absurd h (hN y hy)
        · exact one y hyA h
        · exact absurd (Or.inr h) hc
      · exfalso
        obtain ⟨hyA, hyx, hc⟩ := mem_ANE.1 hy
        have hyS : y ∈ S := ((hcover y).2 ⟨hyA, hyx⟩).resolve_right hn
        rcases hc with h | h
        · exact hS y hyS h
        · exact hdom y hyA h
    rw [eS, eN]

end Placement

open Classical in
/-- Alternative placement: strict dominators of `x` go to the SW side, strictly dominated
points to the NE side. -/
noncomputable def ANEalt (A : Finset Pt) (x : Pt) : Finset Pt :=
  A.filter (fun a => a ≠ x ∧ (NE a x ∨ StrictFOSD x a))

open Classical in
/-- Complement of `ANEalt` in `A \ {x}`. -/
noncomputable def ASWalt (A : Finset Pt) (x : Pt) : Finset Pt :=
  A.filter (fun a => a ≠ x ∧ ¬ (NE a x ∨ StrictFOSD x a))

lemma mem_ANEalt {A : Finset Pt} {x a : Pt} :
    a ∈ ANEalt A x ↔ a ∈ A ∧ a ≠ x ∧ (NE a x ∨ StrictFOSD x a) := by
  classical
  unfold ANEalt; exact Finset.mem_filter

lemma mem_ASWalt {A : Finset Pt} {x b : Pt} :
    b ∈ ASWalt A x ↔ b ∈ A ∧ b ≠ x ∧ ¬ (NE b x ∨ StrictFOSD x b) := by
  classical
  unfold ASWalt; exact Finset.mem_filter

/-- Bracketing with the alternative placement of FOSD-comparable points. -/
def BracketingAlt (X : Finset Pt) (ρ : RandomChoiceRule X) : Prop :=
  ∀ A ⊆ X, ∀ x ∈ A,
    ρ.p x A = max 0 (minOr1 (ASWalt A x) (fun b => ρ.p x {x, b})
                    + minOr1 (ANEalt A x) (fun a => ρ.p x {x, a}) - 1)

/-- **Placement insensitivity**: under CD-dom, Bracketing does not depend on
which side FOSD-comparable points are placed. -/
theorem bracketing_placement_insensitive {X : Finset Pt} (hX : (↑X : Set Pt) ⊆ Tri)
    (ρ : RandomChoiceRule X) (hCD : CDDom X ρ) : Bracketing X ρ ↔ BracketingAlt X ρ := by
  have key : ∀ A ⊆ X, ∀ x ∈ A,
      max 0 (minOr1 (ASWalt A x) (fun b => ρ.p x {x, b}) +
        minOr1 (ANEalt A x) (fun a => ρ.p x {x, a}) - 1) =
      max 0 (minOr1 (ASW A x) (fun b => ρ.p x {x, b}) +
        minOr1 (ANE A x) (fun a => ρ.p x {x, a}) - 1) := by
    intro A hA x hx
    refine bracketing_formula_placement ρ hX hCD hA hx _ _ (fun y => ?_) (fun y hy h => ?_)
      (fun y hy h => ?_)
    · rw [mem_ASWalt, mem_ANEalt]
      tauto
    · exact (mem_ASWalt.1 hy).2.2 (Or.inl h)
    · rcases (mem_ANEalt.1 hy).2.2 with h' | h'
      · linarith [h.1, h'.1]
      · linarith [h.1, h'.1.1]
  constructor
  · intro hB A hA x hx
    rw [hB A hA x hx, key A hA x hx]
  · intro hB A hA x hx
    rw [hB A hA x hx, key A hA x hx]

/-! ## Tests -/

section Tests

/-- Four points on the diagonal `v = u`; the chord segments `[b, a]` and `[d, c]` are disjoint. -/
noncomputable def colA : Pt := (1/2, 1/2)
noncomputable def colB : Pt := (3/8, 3/8)
noncomputable def colC : Pt := (1/4, 1/4)
noncomputable def colD : Pt := (0, 0)
noncomputable def Xcol : Finset Pt := {colA, colB, colC, colD}

lemma Xcol_subset_Tri : (↑Xcol : Set Pt) ⊆ Tri := by
  intro p hp
  simp only [Xcol, Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
    Set.mem_singleton_iff] at hp
  rcases hp with rfl | rfl | rfl | rfl <;>
    (refine ⟨?_, ?_, ?_⟩ <;> norm_num [colA, colB, colC, colD])

/-- Collinear chords with disjoint segments get equal `f` under any betweenness mixture. -/
example (ρ : RandomChoiceRule Xcol) (h : IsMixture IsBetweennessPref Xcol ρ) :
    fChord ρ colA colB = fChord ρ colC colD := by
  refine (necessity Xcol_subset_Tri ρ h).1.2.2 colA colB colC colD
    ⟨by simp [Xcol], by simp [Xcol], ?_⟩ ⟨by simp [Xcol], by simp [Xcol], ?_⟩ ⟨?_, ?_⟩ <;>
    norm_num [NE, OnLine, colA, colB, colC, colD]

/-- `x`, a strict dominator `d` of `x`, and a point `z` strictly dominated by `x`. -/
noncomputable def dx : Pt := (1/4, 1/4)
noncomputable def dd : Pt := (0, 1/2)
noncomputable def dz : Pt := (1/2, 0)
noncomputable def Xdom : Finset Pt := {dx, dd, dz}

lemma Xdom_subset_Tri : (↑Xdom : Set Pt) ⊆ Tri := by
  intro p hp
  simp only [Xdom, Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
    Set.mem_singleton_iff] at hp
  rcases hp with rfl | rfl | rfl <;>
    (refine ⟨?_, ?_, ?_⟩ <;> norm_num [dx, dd, dz])

/-- In the menu `{x, d, z}`: `x` beats the dominated `z` in the pair, and Bracketing (from
necessity) forces `ρ(x, {x, d, z}) = 0` because the dominator sits in `A_NE(x)`. -/
example (ρ : RandomChoiceRule Xdom) (h : IsMixture IsBetweennessPref Xdom ρ) :
    ρ.p dx {dx, dz} = 1 ∧ ρ.p dx Xdom = 0 := by
  obtain ⟨⟨hCD, -, -⟩, hB⟩ := necessity Xdom_subset_Tri ρ h
  have hxX : dx ∈ Xdom := by simp [Xdom]
  have hdX : dd ∈ Xdom := by simp [Xdom]
  have hzX : dz ∈ Xdom := by simp [Xdom]
  have hdom : StrictFOSD dd dx := ⟨by norm_num [FOSD, dd, dx], by norm_num [dd, dx, Prod.ext_iff]⟩
  have hzd : StrictFOSD dx dz := ⟨by norm_num [FOSD, dz, dx], by norm_num [dz, dx, Prod.ext_iff]⟩
  refine ⟨pair_eq_one_of_strictFOSD ρ hCD hxX hzX hzd, ?_⟩
  rw [hB Xdom (Finset.Subset.refl _) dx hxX]
  have hANE : dd ∈ ANE Xdom dx := mem_ANE.2 ⟨hdX, hdom.2, Or.inr hdom⟩
  have z := minOr1_eq_zero (g := fun a => ρ.p dx {dx, a}) hANE
    (pair_eq_zero_of_dominator ρ hCD hxX hdX hdom)
    (fun y hy => pair_nonneg ρ hxX (mem_ANE.1 hy).1)
  have o := minOr1_le_one (S := ASW Xdom dx) (g := fun b => ρ.p dx {dx, b})
    (fun y hy => pair_le_one ρ hxX (mem_ASW.1 hy).1 (Ne.symm (mem_ASW.1 hy).2.1))
  rw [z]
  exact max_eq_left (by linarith)

/-- `|X| = 1`: the only menu is `{p}`; Bracketing reads `ρ(p, {p}) = max 0 (1 + 1 - 1) = 1`. -/
example (p : Pt) (hp : p ∈ Tri) (ρ : RandomChoiceRule {p})
    (h : IsMixture IsBetweennessPref {p} ρ) :
    (ChordDominance {p} ρ ∧ Bracketing {p} ρ) ∧ ρ.p p {p} = 1 := by
  have hX : (↑({p} : Finset Pt) : Set Pt) ⊆ Tri := by
    intro q hq
    rw [Finset.coe_singleton, Set.mem_singleton_iff] at hq
    rw [hq]; exact hp
  have hN := necessity hX ρ h
  refine ⟨hN, ?_⟩
  have hsw : ASW {p} p = ∅ := by
    ext y
    simp only [mem_ASW, Finset.mem_singleton, Finset.notMem_empty, iff_false]
    rintro ⟨h1, h2, -⟩; exact h2 h1
  have hne : ANE {p} p = ∅ := by
    ext y
    simp only [mem_ANE, Finset.mem_singleton, Finset.notMem_empty, iff_false]
    rintro ⟨h1, h2, -⟩; exact h2 h1
  rw [hN.2 {p} (Finset.Subset.refl _) p (Finset.mem_singleton_self p), hsw, hne,
    minOr1_empty]
  norm_num

end Tests

end REU
