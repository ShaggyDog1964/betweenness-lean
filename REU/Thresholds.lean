/-
# Threshold mixtures (shared by the REU clause and Theorem 1 sufficiency)

Given, for every threshold `v`, a betweenness preference `R v` strict on `X` that ranks the NE end
of a chord first exactly when `v ≤ f(ab)`, the components `R v` for the positive values `v` of
`V = {chord values} ∪ {0, 1}`, weighted by the gaps `v − prevIn V v`, have chord masses that
telescope back to `f` (`telescope`), so `ρ` is that mixture (`isMixture_of_thresholds`, via
`isMixture_of_chords`). Also: the finite set of chords `chordSet X`.
-/
import REU.MixtureRule

namespace REU

/-! ## Chords as a finite set -/

open Classical in
/-- The chords of `X`, as pairs `(a, b)` with `a` strictly NE of `b`. -/
noncomputable def chordSet (X : Finset Pt) : Finset (Pt × Pt) :=
  (X ×ˢ X).filter (fun p => NE p.1 p.2)

lemma mem_chordSet {X : Finset Pt} {p : Pt × Pt} : p ∈ chordSet X ↔ IsChord X p.1 p.2 := by
  classical
  simp only [chordSet, Finset.mem_filter, Finset.mem_product, IsChord, and_assoc]

/-! ## Gap weights telescope -/

open Classical in
/-- The largest element of `V` below `v` (`0` if none). -/
noncomputable def prevIn (V : Finset ℝ) (v : ℝ) : ℝ :=
  if h : (V.filter (· < v)).Nonempty then (V.filter (· < v)).max' h else 0

lemma prevIn_spec {V : Finset ℝ} (h0 : 0 ∈ V) {v : ℝ} (hv : 0 < v) :
    prevIn V v ∈ V ∧ prevIn V v < v ∧ ∀ u ∈ V, u < v → u ≤ prevIn V v := by
  classical
  have hne : (V.filter (· < v)).Nonempty := ⟨0, Finset.mem_filter.2 ⟨h0, hv⟩⟩
  have e : prevIn V v = (V.filter (· < v)).max' hne := by
    unfold prevIn; exact dite_eq_left hne
  have hm := Finset.max'_mem _ hne
  rw [e]
  refine ⟨(Finset.mem_filter.1 hm).1, (Finset.mem_filter.1 hm).2, fun u hu huv => ?_⟩
  exact Finset.le_max' _ u (Finset.mem_filter.2 ⟨hu, huv⟩)

open Classical in
/-- Telescoping: the gaps of `V` up to `f ∈ V` sum to `f`. -/
lemma telescope {V : Finset ℝ} (h0 : 0 ∈ V) (hnn : ∀ v ∈ V, 0 ≤ v) {f : ℝ} (hf : f ∈ V) :
    ∑ v ∈ V.filter (fun v => 0 < v ∧ v ≤ f), (v - prevIn V v) = f := by
  suffices H : ∀ n, ∀ f ∈ V, (V.filter (· < f)).card = n →
      ∑ v ∈ V.filter (fun v => 0 < v ∧ v ≤ f), (v - prevIn V v) = f from H _ f hf rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro f hf hn
  rcases (hnn f hf).eq_or_lt with h | h
  · rw [← h]
    refine Finset.sum_eq_zero fun v hv => ?_
    rw [Finset.mem_filter] at hv
    exfalso; linarith [hv.2.1, hv.2.2]
  · obtain ⟨hpV, hplt, hpmax⟩ := prevIn_spec h0 h
    have hset : V.filter (fun v => 0 < v ∧ v ≤ f) =
        insert f (V.filter (fun v => 0 < v ∧ v ≤ prevIn V f)) := by
      ext v
      simp only [Finset.mem_filter, Finset.mem_insert]
      constructor
      · rintro ⟨hv, h1, h2⟩
        rcases h2.lt_or_eq with h2 | h2
        · exact Or.inr ⟨hv, h1, hpmax v hv h2⟩
        · exact Or.inl h2
      · rintro (rfl | ⟨hv, h1, h2⟩)
        · exact ⟨hf, h, le_rfl⟩
        · exact ⟨hv, h1, h2.trans hplt.le⟩
    have hnot : f ∉ V.filter (fun v => 0 < v ∧ v ≤ prevIn V f) := fun hm => by
      rw [Finset.mem_filter] at hm; linarith [hm.2.2]
    have hcard : (V.filter (· < prevIn V f)).card < n := by
      rw [← hn]
      refine Finset.card_lt_card ((Finset.ssubset_iff_of_subset ?_).2 ⟨prevIn V f, ?_, ?_⟩)
      · intro u hu
        rw [Finset.mem_filter] at hu ⊢
        exact ⟨hu.1, hu.2.trans hplt⟩
      · exact Finset.mem_filter.2 ⟨hpV, hplt⟩
      · intro hm; rw [Finset.mem_filter] at hm; exact lt_irrefl _ hm.2
    rw [hset, Finset.sum_insert hnot, ih _ hcard (prevIn V f) hpV rfl]
    ring


/-- **Threshold mixtures.** If `ρ` satisfies CD-dom and Bracketing and, for every threshold `v`,
`R v` is a betweenness preference of class `C`, strict on `X`, with
`a ≻_{R v} b ↔ v ≤ f(ab)` on every chord, then `ρ` is a mixture from class `C`. -/
theorem isMixture_of_thresholds {C : Rel → Prop} {X : Finset Pt} (hX : (↑X : Set Pt) ⊆ Tri)
    (ρ : RandomChoiceRule X) (hCD : CDDom X ρ) (hB : Bracketing X ρ) (R : ℝ → Rel)
    (hC : ∀ v, C (R v)) (hRS : ∀ v, IsBetweennessPref (R v) ∧ StrictOn (R v) X)
    (hspref : ∀ v a b, IsChord X a b → (SPref (R v) a b ↔ v ≤ fChord ρ a b)) :
    IsMixture C X ρ := by
  classical
  let f : Pt × Pt → ℝ := fun p => fChord ρ p.1 p.2
  -- the chord values, with `0` and `1` added
  set V : Finset ℝ := (chordSet X).image f ∪ {0, 1} with hV
  have hV0 : (0 : ℝ) ∈ V := by simp [hV]
  have hV1 : (1 : ℝ) ∈ V := by simp [hV]
  have hVr : ∀ v ∈ V, 0 ≤ v ∧ v ≤ 1 := by
    intro v hv
    rcases Finset.mem_union.1 hv with hv | hv
    · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hv
      have hab := mem_chordSet.1 hp
      exact ⟨pair_nonneg ρ hab.1 hab.2.1, pair_le_one ρ hab.1 hab.2.1 (ne_of_NE hab.2.2)⟩
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hv
      rcases hv with rfl | rfl <;> norm_num
  -- one component per positive value `v`, weight `v - prev v`
  set Vp := V.filter (fun v => 0 < v) with hVp
  let Rs : Vp → Rel := fun v => R v.1
  let w : Vp → ℝ := fun v => v.1 - prevIn V v.1
  have hgap : ∀ F ∈ V, mass w (fun v : Vp => v.1 ≤ F) = F := by
    intro F hF
    have e1 : mass w (fun v : Vp => v.1 ≤ F) =
        ∑ v ∈ Vp, (if v ≤ F then v - prevIn V v else 0) := by
      unfold mass
      rw [← Finset.sum_coe_sort Vp]
    rw [e1]
    refine Eq.trans ?_ (telescope hV0 (fun v hv => (hVr v hv).1) hF)
    rw [hVp, Finset.sum_filter, Finset.sum_filter]
    refine Finset.sum_congr rfl fun v _ => ?_
    by_cases h1 : 0 < v <;> by_cases h2 : v ≤ F <;> simp [h1, h2]
  refine isMixture_of_chords hX ρ hCD hB Rs w (fun v => hC v.1) (fun v => hRS v.1)
    (fun v => ?_) ?_ (fun a b hab => ?_)
  · have hv := Finset.mem_filter.1 v.2
    exact sub_nonneg.2 (prevIn_spec hV0 hv.2).2.1.le
  · rw [← hgap 1 hV1]
    unfold mass
    refine Finset.sum_congr rfl fun v _ => ?_
    exact (ite_eq_left (hVr v.1 (Finset.mem_filter.1 v.2).1).2).symm
  · rw [mass_congr w (fun v => hspref v.1 a b hab)]
    exact (hgap (f (a, b))
      (Finset.mem_union_left _ (Finset.mem_image_of_mem f (mem_chordSet.2 hab)))).symm

end REU
