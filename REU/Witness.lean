/-
# Random betweenness is strictly larger than random EU

A machine-checked witness that the two clauses of Theorem 1 differ. On the four-point set
`Xpar = {ppa, ppb, ppc, ppd}` of `REU.EU` (two chords on the parallel lines `v = u - 1/4` and
`v = u + 1/4`, slope 1, which do not meet in `Tri`), take the one-component mixture of a
single chain preference with two knots:
* knot 0 at `(α, β) = (3/8, 1/2)`: the chord `(ppa, ppb)` has parameters `(3/8, 3/8)`, so
  `ppa ≻ ppb` and `f(ppa ppb) = 1`;
* knot 1 at `(α, β) = (5/8, 9/16)`: the chord `(ppc, ppd)` has parameters `(5/8, 5/8)`, so
  `ppd ≻ ppc` and `f(ppc ppd) = 0`.
The rule is a betweenness mixture (so it satisfies Chord Dominance and Bracketing), but the
two parallel chords get different `f`, so Extended Chord Dominance fails and, by `thm1_reu`,
the rule is not a mixture of EU preferences.
-/
import REU.Main

namespace REU

open Set

/-- Two knots `(3/8, 1/2)` and `(5/8, 9/16)`. -/
noncomputable def knotsW : Knots where
  n := 2
  α := ![3/8, 5/8]
  β := ![1/2, 9/16]
  α_mono := by
    intro i j h
    fin_cases i <;> fin_cases j <;> first | exact absurd h (by decide) | norm_num
  β_mono := by
    intro i j h
    fin_cases i <;> fin_cases j <;> first | exact absurd h (by decide) | norm_num
  inBand := fun k => by fin_cases k <;> norm_num [band]
  α_mem := fun k => by fin_cases k <;> norm_num

/-- Knot indices. -/
def k0 : Fin knotsW.n := ⟨0, show 0 < 2 by norm_num⟩
def k1 : Fin knotsW.n := ⟨1, show 1 < 2 by norm_num⟩

lemma knotsW_α0 : knotsW.α k0 = 3/8 := rfl
lemma knotsW_β0 : knotsW.β k0 = 1/2 := rfl
lemma knotsW_α1 : knotsW.α k1 = 5/8 := rfl
lemma knotsW_β1 : knotsW.β k1 = 9/16 := rfl

lemma Xpar_subset_Tri : (↑Xpar : Set Pt) ⊆ Tri := by
  intro x hx
  simp only [Xpar, Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
    Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl | rfl <;> norm_num [Tri, ppa, ppb, ppc, ppd]

lemma lineParams_ab : lineParams ppa ppb = ((3/8 : ℝ), (3/8 : ℝ)) := by
  norm_num [lineParams, lineAlpha, lineBeta, lineU0, lineV0, ppa, ppb]

lemma lineParams_cd : lineParams ppc ppd = ((5/8 : ℝ), (5/8 : ℝ)) := by
  norm_num [lineParams, lineAlpha, lineBeta, lineU0, lineV0, ppc, ppd]

lemma NE_ab : NE ppa ppb := by unfold NE ppa ppb; norm_num

lemma NE_cd : NE ppc ppd := by unfold NE ppc ppd; norm_num

/-- The only chords of `Xpar` are `(ppa, ppb)` and `(ppc, ppd)`. -/
lemma isChord_Xpar {a b : Pt} (h : IsChord Xpar a b) :
    (a = ppa ∧ b = ppb) ∨ (a = ppc ∧ b = ppd) := by
  obtain ⟨ha, hb, hne⟩ := h
  simp only [Xpar, Finset.mem_insert, Finset.mem_singleton] at ha hb
  rcases ha with rfl | rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl | rfl <;>
    first
    | exact Or.inl ⟨rfl, rfl⟩
    | exact Or.inr ⟨rfl, rfl⟩
    | (exfalso; revert hne; norm_num [NE, ppa, ppb, ppc, ppd])

lemma chord_ab : ¬ Indiff (chainPref knotsW) ppa ppb ∧
    (SPref (chainPref knotsW) ppa ppb ↔ (lineParams ppa ppb).2 < knotsW.β k0) :=
  chainPref_chord knotsW k0 (Xpar_subset_Tri (by simp [Xpar]))
    (Xpar_subset_Tri (by simp [Xpar])) NE_ab
    (by rw [lineParams_ab, knotsW_α0]) (by rw [lineParams_ab, knotsW_β0]; norm_num)

lemma chord_cd : ¬ Indiff (chainPref knotsW) ppc ppd ∧
    (SPref (chainPref knotsW) ppc ppd ↔ (lineParams ppc ppd).2 < knotsW.β k1) :=
  chainPref_chord knotsW k1 (Xpar_subset_Tri (by simp [Xpar]))
    (Xpar_subset_Tri (by simp [Xpar])) NE_cd
    (by rw [lineParams_cd, knotsW_α1]) (by rw [lineParams_cd, knotsW_β1]; norm_num)

lemma spref_ab : SPref (chainPref knotsW) ppa ppb :=
  chord_ab.2.2 (by rw [lineParams_ab, knotsW_β0]; norm_num)

lemma not_spref_cd : ¬ SPref (chainPref knotsW) ppc ppd := fun h => by
  have := chord_cd.2.1 h
  rw [lineParams_cd, knotsW_β1] at this
  norm_num at this

lemma strictOn_knotsW : StrictOn (chainPref knotsW) Xpar :=
  chainPref_strictOn knotsW Xpar_subset_Tri fun a b h => by
    rcases isChord_Xpar h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨k0, by rw [lineParams_ab, knotsW_α0], by rw [lineParams_ab, knotsW_β0]; norm_num⟩
    · exact ⟨k1, by rw [lineParams_cd, knotsW_α1], by rw [lineParams_cd, knotsW_β1]; norm_num⟩

/-- The witness rule: the one-component mixture of `chainPref knotsW` on `Xpar`. -/
noncomputable def ρW : RandomChoiceRule Xpar :=
  mixtureRule Xpar_subset_Tri (fun _ : Fin 1 => chainPref knotsW) (fun _ => 1)
    (fun _ => ⟨chainPref_isBtw knotsW, strictOn_knotsW⟩) (fun _ => zero_le_one) (by simp)

open Classical in
lemma ρW_pair {x y : Pt} (hne : x ≠ y) :
    ρW.p x {x, y} = if SPref (chainPref knotsW) x y then 1 else 0 := by
  unfold ρW
  rw [mixtureRule_p, mass_congr _ fun _ => isMaxIn_pair_iff hne]
  simp [mass]

lemma fChord_ab : fChord ρW ppa ppb = 1 := by
  unfold fChord; simp [ρW_pair (ne_of_NE NE_ab), spref_ab]

lemma fChord_cd : fChord ρW ppc ppd = 0 := by
  unfold fChord; simp [ρW_pair (ne_of_NE NE_cd), not_spref_cd]

/-- `ρW` is a mixture of betweenness preferences. -/
theorem ρW_isMixture : IsMixture IsBetweennessPref Xpar ρW :=
  isMixture_mixtureRule _ _ _ _ _ _ fun _ => chainPref_isBtw knotsW

/-- **Witness.** `ρW` satisfies Chord Dominance and Bracketing but not Extended Chord Dominance:
the parallel chords `(ppa, ppb)` and `(ppc, ppd)` (equal slope 1) have `f = 1` and `f = 0`. -/
theorem witness_CD_B_not_CDAll :
    ChordDominance Xpar ρW ∧ Bracketing Xpar ρW ∧ ¬ ChordDominanceAll Xpar ρW := by
  obtain ⟨hCD, hB⟩ := necessity Xpar_subset_Tri ρW ρW_isMixture
  refine ⟨hCD, hB, fun ⟨_, _, hpar⟩ => ?_⟩
  have h := hpar ppa ppb ppc ppd
    ⟨by simp [Xpar], by simp [Xpar], NE_ab⟩ ⟨by simp [Xpar], by simp [Xpar], NE_cd⟩
    (by unfold slope ppa ppb ppc ppd; norm_num)
  rw [fChord_ab, fChord_cd] at h
  norm_num at h

/-- **Corollary (via `thm1`, `thm1_reu`).** Random betweenness is strictly larger than random
EU: `ρW` is a mixture of betweenness preferences but not a mixture of EU preferences. -/
theorem witness_btw_not_EU :
    IsMixture IsBetweennessPref Xpar ρW ∧ ¬ IsMixture IsEUPref Xpar ρW := by
  obtain ⟨_, _, hnot⟩ := witness_CD_B_not_CDAll
  exact ⟨(thm1 Xpar Xpar_subset_Tri ρW).2 ⟨witness_CD_B_not_CDAll.1, witness_CD_B_not_CDAll.2.1⟩,
    fun h => hnot ((thm1_reu Xpar Xpar_subset_Tri ρW).1 h).1⟩

/-- The same, stated existentially. -/
theorem btw_strictly_larger_than_EU :
    ∃ X : Finset Pt, (↑X : Set Pt) ⊆ Tri ∧ ∃ ρ : RandomChoiceRule X,
      (ChordDominance X ρ ∧ Bracketing X ρ ∧ ¬ ChordDominanceAll X ρ) ∧
      (IsMixture IsBetweennessPref X ρ ∧ ¬ IsMixture IsEUPref X ρ) :=
  ⟨Xpar, Xpar_subset_Tri, ρW, witness_CD_B_not_CDAll, witness_btw_not_EU⟩

end REU
