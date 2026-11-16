/-
# Sufficiency of Chord Dominance and Bracketing (Theorem 1, `⇐`)

For each threshold `v`, the chords of `X` split by `f(ab) ≥ v` / `f(ab) < v`; their line
parameters `c(ab) = lineParams a b` give two finite point sets `Up`, `Dn`. CD-cross (via
`cross_of_SE`) and CD-col (via `collinear4_of_lineParams_eq`) make the split consistent, so
`realize_upset` gives knots `K` and the chain preference `chainPref K` ranks every chord's NE
end first exactly when `v ≤ f(ab)` (`exists_threshold_knots`). Weighting the thresholds
`v ∈ V = {f values} ∪ {0, 1}` by their gaps gives chord masses equal to `f`
(`isMixture_of_thresholds`, shared with the REU clause in `Thresholds.lean`).
-/
import REU.Thresholds
import REU.Construct

namespace REU

open Set

/-- 8.2–8.3: for a threshold `v`, a chain preference whose chord ranking is the indicator
`[v ≤ f(ab)]`, with every chord on a knot's hypotenuse parameter but off its knot line. -/
theorem exists_threshold_knots {X : Finset Pt} (hX : (↑X : Set Pt) ⊆ Tri)
    (ρ : RandomChoiceRule X) (hCD : ChordDominance X ρ) (v : ℝ) :
    ∃ K : Knots, ∀ a b, IsChord X a b → ∃ k : Fin K.n,
      (lineParams a b).1 = K.α k ∧ (lineParams a b).2 ≠ K.β k ∧
      (SPref (chainPref K) a b ↔ v ≤ fChord ρ a b) := by
  classical
  obtain ⟨-, hcross, hcol⟩ := hCD
  set Ch := chordSet X
  have memCh : ∀ p : Pt × Pt, p ∈ Ch ↔ IsChord X p.1 p.2 := fun _ => mem_chordSet
  let lp : Pt × Pt → ℝ × ℝ := fun p => lineParams p.1 p.2
  let f : Pt × Pt → ℝ := fun p => fChord ρ p.1 p.2
  set Up := (Ch.filter (fun p => v ≤ f p)).image lp with hUp
  set Dn := (Ch.filter (fun p => f p < v)).image lp with hDn
  have hP : ∀ c ∈ Up ∪ Dn, band c ∧ c.1 ∈ Ioo (0 : ℝ) 1 := by
    intro c hc
    have : ∃ p ∈ Ch, lp p = c := by
      rcases Finset.mem_union.1 hc with hc | hc
      · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hc
        exact ⟨p, (Finset.mem_filter.1 hp).1, rfl⟩
      · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hc
        exact ⟨p, (Finset.mem_filter.1 hp).1, rfl⟩
    obtain ⟨p, hp, rfl⟩ := this
    have h := (memCh p).1 hp
    exact ⟨lineParams_band h.2.2 (hX h.1) (hX h.2.1), lineAlpha_mem h.2.2 (hX h.1) (hX h.2.1)⟩
  have hcons : ¬ ∃ c₁ ∈ Up, ∃ c₂ ∈ Dn, c₁.1 ≤ c₂.1 ∧ c₂.2 ≤ c₁.2 := by
    rintro ⟨c₁, h₁, c₂, h₂, hα, hβ⟩
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 h₁
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.1 h₂
    rw [Finset.mem_filter] at hp hq
    have hpc := (memCh p).1 hp.1
    have hqc := (memCh q).1 hq.1
    have hle : f p ≤ f q := by
      by_cases he : lp p = lp q
      · -- same line parameters: collinear chords (CD-col)
        exact (hcol _ _ _ _ hpc hqc (collinear4_of_lineParams_eq hpc.2.2 (hX hpc.1)
          (hX hpc.2.1) hqc.2.2 (hX hqc.1) (hX hqc.2.1) he)).le
      · -- distinct: the lines cross in `Tri`, `q`'s chord is steeper (CD-cross)
        obtain ⟨⟨y, hy, h1, h2⟩, hsl⟩ := cross_of_SE hpc.2.2 (hX hpc.1) (hX hpc.2.1) hqc.2.2
          (hX hqc.1) (hX hqc.2.1) hα hβ he
        exact hcross _ _ _ _ hqc hpc ⟨y, hy, h2, h1⟩ hsl
    linarith [hp.2, hq.2]
  obtain ⟨K, hK1, hKup, hKdn⟩ := realize_upset Up Dn hP hcons
  refine ⟨K, fun a b hab => ?_⟩
  have hp : (a, b) ∈ Ch := (memCh (a, b)).2 hab
  by_cases hv : v ≤ fChord ρ a b
  · have hc : lineParams a b ∈ Up :=
      Finset.mem_image.2 ⟨(a, b), Finset.mem_filter.2 ⟨hp, hv⟩, rfl⟩
    obtain ⟨k, hk⟩ := hK1 _ (Finset.mem_union_left _ hc)
    have hlt := hKup _ hc k hk
    refine ⟨k, hk.symm, hlt.ne, ?_⟩
    rw [(chainPref_chord K k (hX hab.1) (hX hab.2.1) hab.2.2 hk.symm hlt.ne).2]
    exact ⟨fun _ => hv, fun _ => hlt⟩
  · push Not at hv
    have hc : lineParams a b ∈ Dn :=
      Finset.mem_image.2 ⟨(a, b), Finset.mem_filter.2 ⟨hp, hv⟩, rfl⟩
    obtain ⟨k, hk⟩ := hK1 _ (Finset.mem_union_right _ hc)
    have hlt := hKdn _ hc k hk
    refine ⟨k, hk.symm, hlt.ne', ?_⟩
    rw [(chainPref_chord K k (hX hab.1) (hX hab.2.1) hab.2.2 hk.symm hlt.ne').2]
    exact ⟨fun h => absurd h (not_lt.2 hlt.le), fun h => absurd h (not_le.2 hv)⟩

/-- **Theorem 1, sufficiency.** Chord Dominance and Bracketing make `ρ` a finite mixture of
betweenness preferences strict on `X`. -/
theorem sufficiency {X : Finset Pt} (hX : (↑X : Set Pt) ⊆ Tri) (ρ : RandomChoiceRule X) :
    ChordDominance X ρ → Bracketing X ρ → IsMixture IsBetweennessPref X ρ := by
  classical
  intro hCDfull hB
  have hCD := hCDfull.1
  choose K hK using exists_threshold_knots hX ρ hCDfull
  refine isMixture_of_thresholds hX ρ hCD hB (fun v => chainPref (K v))
    (fun v => chainPref_isBtw _)
    (fun v => ⟨chainPref_isBtw _, chainPref_strictOn _ hX fun a b hab => ?_⟩)
    (fun v a b hab => (hK v a b hab).choose_spec.2.2)
  obtain ⟨k, h1, h2, -⟩ := hK v a b hab
  exact ⟨k, h1, h2⟩

end REU
