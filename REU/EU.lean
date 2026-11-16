/-
# The REU clause of Theorem 1

`thm1_reu : thm1_reu_stmt`: on `X ⊆ Tri`, `ρ` is a finite mixture of EU preferences (each strict
on `X`) iff it satisfies extended Chord Dominance (CD-all) and Bracketing.

* **A.** An EU preference has level lines of one common slope (`eu_tau_eq`): independence
  translates an indifferent pair along any segment, and two points of `Tri \ {W, B}` share their
  midpoint. Hence `R` agrees on `Tri` with the linear preference `euPref c` (`eu_linear`), and on
  chords `a ≻ b ↔ c < slope a b` (`eu_spref_chord`).
* **B.** `euPref τ` (`U(u,v) = v - τ u`, `τ > 0`) is an EU preference (`euPref_isEU`).
* **D.** Necessity: EU ⊆ betweenness gives CD-dom and Bracketing (`Necessity.lean`); CD-all from the
  common slope of each component.
* **E.** Sufficiency: the chord values `f` are nondecreasing in slope; for each positive value `v`
  of `f` (with `1` added) pick a cutoff `τ_v` strictly separating the chord slopes with `f < v` from
  those with `f ≥ v`; the component `euPref τ_v` gets weight `v - (previous value)`. Chord values
  telescope back to `f` (`isMixture_of_thresholds`, `Thresholds.lean`).
-/
import REU.Thresholds

namespace REU

open Set

variable {R : Rel}

/-! ## A. EU preferences have a constant level-line slope -/

/-- Every point of `Tri \ {W, B}` has an indifferent partner in `Tri` with a different
`u`-coordinate. -/
lemma exists_indiff_partner (hR : IsBetweennessPref R) {y : Pt} (hy : y ∈ Tri)
    (hW : y ≠ ((1 : ℝ), (0 : ℝ))) (hB : y ≠ ((0 : ℝ), (1 : ℝ))) :
    ∃ r ∈ Tri, Indiff R r y ∧ r.1 ≠ y.1 := by
  have ht := util_mem_Ioo hR hy hW hB
  obtain ⟨he, hu, _, _⟩ := levelPt_spec hR ht
  have hp := hyp_mem_tri ht.1.le ht.2.le
  have hup : util hR (hyp (util hR y)) = util hR y := util_hyp hR ⟨ht.1.le, ht.2.le⟩
  have hNE := levelPt_NE hR ht
  by_cases h : (hyp (util hR y)).1 = y.1
  · refine ⟨levelPt hR (util hR y), he, (indiff_iff_util hR he hy).2 hu, ?_⟩
    rw [← h]; exact hNE.1.ne
  · exact ⟨hyp (util hR y), hp, (indiff_iff_util hR hp hy).2 hup, h⟩

lemma mid_ne_W {y z : Pt} (hy : y ∈ Tri) (hz : z ∈ Tri) (hW : y ≠ ((1 : ℝ), (0 : ℝ))) :
    mix (1/2) y z ≠ ((1 : ℝ), (0 : ℝ)) := by
  intro h
  have h1 := congrArg Prod.fst h
  have h2 := congrArg Prod.snd h
  simp only [mix_fst, mix_snd] at h1 h2
  obtain ⟨a1, a2, a3⟩ := hy
  obtain ⟨b1, b2, b3⟩ := hz
  exact hW (Prod.ext (show y.1 = 1 by linarith) (show y.2 = 0 by linarith))

lemma mid_ne_B {y z : Pt} (hy : y ∈ Tri) (hz : z ∈ Tri) (hB : y ≠ ((0 : ℝ), (1 : ℝ))) :
    mix (1/2) y z ≠ ((0 : ℝ), (1 : ℝ)) := by
  intro h
  have h1 := congrArg Prod.fst h
  have h2 := congrArg Prod.snd h
  simp only [mix_fst, mix_snd] at h1 h2
  obtain ⟨a1, a2, a3⟩ := hy
  obtain ⟨b1, b2, b3⟩ := hz
  exact hB (Prod.ext (show y.1 = 0 by linarith) (show y.2 = 1 by linarith))

/-- Independence transports the level-line slope along segments. -/
lemma eu_tau_transport (hEU : IsEUPref R) {y s : Pt} (hy : y ∈ Tri) (hs : s ∈ Tri)
    (hW : y ≠ ((1 : ℝ), (0 : ℝ))) (hB : y ≠ ((0 : ℝ), (1 : ℝ))) {l : ℝ} (hl : l ∈ Ioc (0 : ℝ) 1)
    (hmW : mix l y s ≠ ((1 : ℝ), (0 : ℝ))) (hmB : mix l y s ≠ ((0 : ℝ), (1 : ℝ))) :
    tau hEU.1 (mix l y s) = tau hEU.1 y := by
  obtain ⟨r, hr, ⟨h1, h2⟩, hr1⟩ := exists_indiff_partner hEU.1 hy hW hB
  have hm := mix_mem_tri hy hs hl.1.le hl.2
  have hm' := mix_mem_tri hr hs hl.1.le hl.2
  have hi : Indiff R (mix l r s) (mix l y s) :=
    ⟨(hEU.2 r hr y hy s hs l hl).1 h1, (hEU.2 y hy r hr s hs l hl).1 h2⟩
  have e1 := ((level_is_segment hEU.1 hy hW hB).2 r hr).1 ⟨h1, h2⟩
  have e2 := ((level_is_segment hEU.1 hm hmW hmB).2 _ hm').1 hi
  simp only [mix_fst, mix_snd] at e2
  have hd : l * (r.1 - y.1) ≠ 0 := mul_ne_zero hl.1.ne' (sub_ne_zero.2 hr1)
  have key : l * (r.1 - y.1) * (tau hEU.1 (mix l y s) - tau hEU.1 y) = 0 := by
    linear_combination l * e1 - e2
  exact sub_eq_zero.1 ((mul_eq_zero.1 key).resolve_left hd)

theorem eu_tau_eq (hEU : IsEUPref R) {y z : Pt} (hy : y ∈ Tri) (hz : z ∈ Tri)
    (hyW : y ≠ ((1 : ℝ), (0 : ℝ))) (hyB : y ≠ ((0 : ℝ), (1 : ℝ)))
    (hzW : z ≠ ((1 : ℝ), (0 : ℝ))) (hzB : z ≠ ((0 : ℝ), (1 : ℝ))) :
    tau hEU.1 y = tau hEU.1 z := by
  have hl : (1/2 : ℝ) ∈ Ioc (0 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
  have e : mix (1/2) z y = mix (1/2) y z := by rw [mix_symm]; norm_num
  rw [← eu_tau_transport hEU hy hz hyW hyB hl (mid_ne_W hy hz hyW) (mid_ne_B hy hz hyB),
    ← eu_tau_transport hEU hz hy hzW hzB hl (mid_ne_W hz hy hzW) (mid_ne_B hz hy hzB), e]

/-- **Constant `tau`.** An EU preference has one level-line slope `c > 0` on `Tri \ {W, B}`. -/
theorem eu_tau_const (hEU : IsEUPref R) :
    ∃ c, 0 < c ∧ ∀ y ∈ Tri, y ≠ ((1 : ℝ), (0 : ℝ)) → y ≠ ((0 : ℝ), (1 : ℝ)) → tau hEU.1 y = c := by
  have hM : ((0 : ℝ), (0 : ℝ)) ∈ Tri := by refine ⟨?_, ?_, ?_⟩ <;> norm_num
  have hMW : ((0 : ℝ), (0 : ℝ)) ≠ ((1 : ℝ), (0 : ℝ)) := by simp [Prod.ext_iff]
  have hMB : ((0 : ℝ), (0 : ℝ)) ≠ ((0 : ℝ), (1 : ℝ)) := by simp [Prod.ext_iff]
  exact ⟨tau hEU.1 ((0 : ℝ), (0 : ℝ)), tau_pos hEU.1 hM hMW hMB,
    fun y hy hW hB => eu_tau_eq hEU hy hM hW hB hMW hMB⟩

/-! ## B. Concrete EU preferences -/

/-- The linear EU preference with utility `U(u, v) = v - τ u` (indifference lines of slope `τ`). -/
def euPref (τ : ℝ) : Rel := fun q r => r.2 - τ * r.1 ≤ q.2 - τ * q.1

lemma euPref_iff (τ : ℝ) (q r : Pt) : euPref τ q r ↔ r.2 - τ * r.1 ≤ q.2 - τ * q.1 := Iff.rfl

lemma euPref_spref (τ : ℝ) (q r : Pt) :
    SPref (euPref τ) q r ↔ r.2 - τ * r.1 < q.2 - τ * q.1 := by
  simp only [SPref, euPref_iff, not_le]
  exact ⟨fun h => h.2, fun h => ⟨h.le, h⟩⟩

lemma euU_mix (τ t : ℝ) (q r : Pt) :
    (mix t q r).2 - τ * (mix t q r).1 = t * (q.2 - τ * q.1) + (1 - t) * (r.2 - τ * r.1) := by
  rw [mix_fst, mix_snd]; ring

theorem euPref_isEU {τ : ℝ} (hτ : 0 < τ) : IsEUPref (euPref τ) := by
  have hc : Continuous fun q : Tri => (q : Pt).2 - τ * (q : Pt).1 := by fun_prop
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · intro q _ r _; exact le_total _ _
  · intro q _ r _ s _ h1 h2; exact le_trans h2 h1
  · intro r _; exact isClosed_le continuous_const hc
  · intro r _; exact isClosed_le hc continuous_const
  · intro q _ r _ h
    obtain ⟨⟨h1, h2⟩, hne⟩ := h
    rw [euPref_spref]
    by_contra hle
    push Not at hle
    have h3 : τ * (q.1 - r.1) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hτ.le (by linarith)
    have h4 : q.2 = r.2 := by linarith
    have h5 : τ * (q.1 - r.1) = 0 := by linarith
    have h6 : q.1 = r.1 := by
      have := (mul_eq_zero.1 h5).resolve_left hτ.ne'; linarith
    exact hne (Prod.ext h6 h4)
  · intro q _ r _ t ht h
    rw [euPref_spref] at h
    obtain ⟨ht0, ht1⟩ := ht
    rw [euPref_spref, euPref_spref, euU_mix]
    have h1 : 0 < (1 - t) * ((q.2 - τ * q.1) - (r.2 - τ * r.1)) :=
      mul_pos (by linarith) (by linarith)
    have h2 : 0 < t * ((q.2 - τ * q.1) - (r.2 - τ * r.1)) := mul_pos ht0 (by linarith)
    constructor <;> nlinarith
  · intro q _ r _ t _ h
    obtain ⟨h1, h2⟩ := h
    simp only [Indiff, euPref_iff, euU_mix]
    have : q.2 - τ * q.1 = r.2 - τ * r.1 := le_antisymm h2 h1
    rw [← this]
    constructor <;> nlinarith
  · intro q _ r _ s _ t ht
    obtain ⟨ht0, _⟩ := ht
    rw [euPref_iff, euPref_iff, euU_mix, euU_mix]
    constructor
    · intro h; nlinarith
    · intro h
      by_contra hc
      push Not at hc
      have : 0 < t * ((r.2 - τ * r.1) - (q.2 - τ * q.1)) := mul_pos ht0 (by linarith)
      linarith

/-- On a chord, `a ≻ b` under `euPref τ` iff the chord is steeper than `τ`. -/
theorem euPref_spref_chord (τ : ℝ) {a b : Pt} (hab : NE a b) :
    SPref (euPref τ) a b ↔ τ < slope a b := by
  have hd : 0 < a.1 - b.1 := by linarith [hab.1]
  rw [euPref_spref, slope, lt_div_iff₀ hd]
  constructor <;> intro h <;> linarith

/-- `euPref τ` is strict on `X` when `τ` is not the slope of a chord of `X`. -/
theorem euPref_strictOn {τ : ℝ} (hτ : 0 < τ) {X : Finset Pt} (hX : (↑X : Set Pt) ⊆ Tri)
    (h : ∀ a b, IsChord X a b → slope a b ≠ τ) : StrictOn (euPref τ) X := by
  have hEU := euPref_isEU hτ
  have hsl : ∀ a b, NE a b → a.2 - τ * a.1 = b.2 - τ * b.1 → slope a b = τ := by
    intro a b hab he
    have hd : 0 < a.1 - b.1 := by linarith [hab.1]
    rw [slope, div_eq_iff hd.ne']
    linarith
  intro x hx y hy hxy hi
  have he : x.2 - τ * x.1 = y.2 - τ * y.1 := le_antisymm hi.2 hi.1
  rcases tri_cases (hX hx) (hX hy) (Ne.symm hxy) with hc | hc | hc | hc
  · exact h y x ⟨hy, hx, hc⟩ (hsl y x hc he.symm)
  · exact h x y ⟨hx, hy, hc⟩ (hsl x y hc he)
  · exact (hEU.1.strictMono x (hX hx) y (hX hy) hc).2 hi.2
  · exact (hEU.1.strictMono y (hX hy) x (hX hx) hc).2 hi.1

/-- The level-line slope of `euPref τ` is `τ` (connects B with A). -/
theorem tau_euPref {τ : ℝ} (hτ : 0 < τ) {y : Pt} (hy : y ∈ Tri) (hW : y ≠ ((1 : ℝ), (0 : ℝ)))
    (hB : y ≠ ((0 : ℝ), (1 : ℝ))) : tau (euPref_isEU hτ).1 y = τ := by
  obtain ⟨r, hr, hi, hr1⟩ := exists_indiff_partner (euPref_isEU hτ).1 hy hW hB
  have e1 := ((level_is_segment (euPref_isEU hτ).1 hy hW hB).2 r hr).1 hi
  have e2 : r.2 - τ * r.1 = y.2 - τ * y.1 := le_antisymm hi.2 hi.1
  have key : (r.1 - y.1) * (tau (euPref_isEU hτ).1 y - τ) = 0 := by linear_combination e2 - e1
  exact sub_eq_zero.1 ((mul_eq_zero.1 key).resolve_left (sub_ne_zero.2 hr1))

/-! ## A'. Every EU preference is some `euPref c` on `Tri` -/

/-- **EU is linear.** An EU preference agrees on `Tri` with `euPref c` for some `c > 0`, i.e.
`q ≽ r ↔ -c q₁ + q₂ ≥ -c r₁ + r₂` (`c₁ = -c < 0`, `c₂ = 1 > 0`). -/
theorem eu_linear (hEU : IsEUPref R) :
    ∃ c, 0 < c ∧ ∀ q ∈ Tri, ∀ r ∈ Tri, (R q r ↔ euPref c q r) := by
  obtain ⟨c, hc, hτ⟩ := eu_tau_const hEU
  have hE := euPref_isEU hc
  have hch : ∀ a ∈ Tri, ∀ b ∈ Tri, NE a b →
      (R a b ↔ euPref c a b) ∧ (R b a ↔ euPref c b a) := by
    intro a ha b hb hab
    obtain ⟨hW, hB⟩ := chord_line_avoids_vertices ha hb hab (onLine_self_left a b)
    have hseg := (level_is_segment hEU.1 ha hW hB).2 b hb
    rw [hτ a ha hW hB] at hseg
    by_cases hi : Indiff R a b
    · have he := hseg.1 ⟨hi.2, hi.1⟩
      simp only [euPref_iff]
      exact ⟨⟨fun _ => by linarith, fun _ => hi.1⟩, ⟨fun _ => by linarith, fun _ => hi.2⟩⟩
    · have key := chord_iff_tau hEU.1 ha ha hb hab (onLine_self_left a b) hi
      rw [hτ a ha hW hB, ← euPref_spref_chord c hab, euPref_spref] at key
      have hne : b.2 - c * b.1 ≠ a.2 - c * a.1 := fun h =>
        hi ⟨(hseg.2 (by linarith)).2, (hseg.2 (by linarith)).1⟩
      have hcomp := hEU.1.complete a ha b hb
      simp only [euPref_iff]
      refine ⟨⟨fun h => (key.1 ⟨h, fun h' => hi ⟨h, h'⟩⟩).le,
        fun h => (key.2 (lt_of_le_of_ne h hne)).1⟩, ⟨fun h => ?_, fun h => ?_⟩⟩
      · by_contra hlt
        push Not at hlt
        exact (key.2 hlt).2 h
      · by_contra hba
        have := key.1 ⟨hcomp.resolve_right hba, hba⟩
        linarith
  refine ⟨c, hc, fun q hq r hr => ?_⟩
  by_cases hqr : q = r
  · subst hqr; exact ⟨fun _ => le_refl _, fun _ => R_refl hEU.1 hq⟩
  rcases tri_cases hq hr (Ne.symm hqr) with h | h | h | h
  · exact (hch r hr q hq h).2
  · exact (hch q hq r hr h).1
  · exact ⟨fun _ => (hE.1.strictMono q hq r hr h).1, fun _ => (hEU.1.strictMono q hq r hr h).1⟩
  · exact ⟨fun h' => absurd h' (hEU.1.strictMono r hr q hq h).2,
      fun h' => absurd h' (hE.1.strictMono r hr q hq h).2⟩

/-- For an EU preference, on chords `a ≻ b ↔ c < slope a b` for one constant `c > 0`. -/
theorem eu_spref_chord (hEU : IsEUPref R) :
    ∃ c, 0 < c ∧ ∀ a ∈ Tri, ∀ b ∈ Tri, NE a b → (SPref R a b ↔ c < slope a b) := by
  obtain ⟨c, hc, hlin⟩ := eu_linear hEU
  refine ⟨c, hc, fun a ha b hb hab => ?_⟩
  rw [← euPref_spref_chord c hab]
  unfold SPref
  rw [hlin a ha b hb, hlin b hb a ha]

/-! ## D. Necessity -/

theorem reu_necessity {X : Finset Pt} (hX : (↑X : Set Pt) ⊆ Tri) (ρ : RandomChoiceRule X) :
    IsMixture IsEUPref X ρ → ChordDominanceAll X ρ ∧ Bracketing X ρ := by
  intro hmix
  have hmixB : IsMixture IsBetweennessPref X ρ := by
    obtain ⟨n, Rs, w, hRS, hw, hsum, hρ⟩ := hmix
    exact ⟨n, Rs, w, fun i => ⟨(hRS i).1.1, (hRS i).2⟩, hw, hsum, hρ⟩
  obtain ⟨⟨hCD, -, -⟩, hB⟩ := necessity hX ρ hmixB
  obtain ⟨n, Rs, w, hRS, hw, hsum, hρ⟩ := hmix
  have hρ' : ∀ A ⊆ X, A.Nonempty → ∀ x ∈ A,
      ρ.p x A = mass w (fun i => IsMaxIn (Rs i) x A) := hρ
  choose c _ hc using fun i => eu_spref_chord (hRS i).1
  have key : ∀ i a b, IsChord X a b → (SPref (Rs i) a b ↔ c i < slope a b) :=
    fun i a b hab => hc i a (hX hab.1) b (hX hab.2.1) hab.2.2
  refine ⟨⟨hCD, ?_, ?_⟩, hB⟩
  · intro a b c' d hab hcd hsl
    unfold fChord
    rw [pair_eq_mass ρ hρ' hcd.1 hcd.2.1 (ne_of_NE hcd.2.2),
      pair_eq_mass ρ hρ' hab.1 hab.2.1 (ne_of_NE hab.2.2)]
    exact mass_mono hw fun i h => (key i a b hab).2 (((key i c' d hcd).1 h).trans hsl)
  · intro a b c' d hab hcd hsl
    unfold fChord
    rw [pair_eq_mass ρ hρ' hcd.1 hcd.2.1 (ne_of_NE hcd.2.2),
      pair_eq_mass ρ hρ' hab.1 hab.2.1 (ne_of_NE hab.2.2)]
    exact mass_congr w fun i => by rw [key i a b hab, key i c' d hcd, hsl]

/-! ## E. Sufficiency -/

/-- Strict separation of two finite sets of positive reals by a positive cutoff. -/
lemma exists_strict_sep (L U : Finset ℝ) (hU : ∀ y ∈ U, 0 < y) (h : ∀ x ∈ L, ∀ y ∈ U, x < y) :
    ∃ τ, 0 < τ ∧ (∀ x ∈ L, x < τ) ∧ ∀ y ∈ U, τ < y := by
  classical
  have hL0 : (insert 0 L).Nonempty := Finset.insert_nonempty 0 L
  set lo := (insert 0 L).max' hL0 with hlo
  have hlo0 : 0 ≤ lo := Finset.le_max' _ 0 (Finset.mem_insert_self 0 L)
  have hloL : ∀ x ∈ L, x ≤ lo := fun x hx => Finset.le_max' _ x (Finset.mem_insert_of_mem hx)
  have hloU : ∀ y ∈ U, lo < y := by
    intro y hy
    rw [hlo, Finset.max'_lt_iff]
    intro x hx
    rcases Finset.mem_insert.1 hx with rfl | hx
    · exact hU y hy
    · exact h x hx y hy
  have hU0 : (insert (lo + 2) U).Nonempty := Finset.insert_nonempty _ U
  set hi := (insert (lo + 2) U).min' hU0 with hhi
  have hhiU : ∀ y ∈ U, hi ≤ y := fun y hy => Finset.min'_le _ y (Finset.mem_insert_of_mem hy)
  have hlohi : lo < hi := by
    rw [hhi, Finset.lt_min'_iff]
    intro y hy
    rcases Finset.mem_insert.1 hy with rfl | hy
    · linarith
    · exact hloU y hy
  refine ⟨(lo + hi) / 2, by linarith, fun x hx => ?_, fun y hy => ?_⟩
  · linarith [hloL x hx]
  · linarith [hhiU y hy]

theorem reu_sufficiency {X : Finset Pt} (hX : (↑X : Set Pt) ⊆ Tri) (ρ : RandomChoiceRule X)
    (hCDA : ChordDominanceAll X ρ) (hB : Bracketing X ρ) : IsMixture IsEUPref X ρ := by
  classical
  obtain ⟨hCD, hmono, heq⟩ := hCDA
  -- chords, their values `f` and slopes `sl`
  set Ch := chordSet X
  have memCh : ∀ p : Pt × Pt, p ∈ Ch ↔ IsChord X p.1 p.2 := fun _ => mem_chordSet
  let f : Pt × Pt → ℝ := fun p => fChord ρ p.1 p.2
  let sl : Pt × Pt → ℝ := fun p => slope p.1 p.2
  -- CD-all: `f` is nondecreasing in slope, so lower values sit on strictly flatter chords
  have hsep : ∀ p ∈ Ch, ∀ q ∈ Ch, f p < f q → sl p < sl q := by
    intro p hp q hq hlt
    rcases lt_trichotomy (sl p) (sl q) with h | h | h
    · exact h
    · exact absurd (heq p.1 p.2 q.1 q.2 ((memCh p).1 hp) ((memCh q).1 hq) h) hlt.ne
    · exact absurd (hmono p.1 p.2 q.1 q.2 ((memCh p).1 hp) ((memCh q).1 hq) h) (not_le.2 hlt)
  -- cutoffs: `τ v` strictly separates slopes of chords with `f < v` from those with `f ≥ v`
  have hcut : ∀ v : ℝ, ∃ τ, 0 < τ ∧ ∀ p ∈ Ch, (v ≤ f p → τ < sl p) ∧ (f p < v → sl p < τ) := by
    intro v
    have hpos : ∀ y ∈ (Ch.filter (fun p => v ≤ f p)).image sl, 0 < y := by
      intro y hy
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hy
      exact slope_pos_of_NE ((memCh p).1 (Finset.mem_filter.1 hp).1).2.2
    have hlt : ∀ x ∈ (Ch.filter (fun p => f p < v)).image sl,
        ∀ y ∈ (Ch.filter (fun p => v ≤ f p)).image sl, x < y := by
      intro x hx y hy
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hx
      obtain ⟨q, hq, rfl⟩ := Finset.mem_image.1 hy
      rw [Finset.mem_filter] at hp hq
      exact hsep p hp.1 q hq.1 (lt_of_lt_of_le hp.2 hq.2)
    obtain ⟨τ, hτ, hL, hU⟩ := exists_strict_sep _ _ hpos hlt
    exact ⟨τ, hτ, fun p hp =>
      ⟨fun h => hU _ (Finset.mem_image_of_mem sl (Finset.mem_filter.2 ⟨hp, h⟩)),
        fun h => hL _ (Finset.mem_image_of_mem sl (Finset.mem_filter.2 ⟨hp, h⟩))⟩⟩
  choose τ hτpos hτ using hcut
  -- threshold `v` component: `euPref (τ v)`; `isMixture_of_thresholds` does the weighting
  have hspref : ∀ (v : ℝ) a b, IsChord X a b → (SPref (euPref (τ v)) a b ↔ v ≤ f (a, b)) := by
    intro v a b hab
    have hp : (a, b) ∈ Ch := (memCh _).2 hab
    rw [euPref_spref_chord _ hab.2.2]
    constructor
    · intro h
      by_contra h'
      push Not at h'
      exact absurd ((hτ v _ hp).2 h') (not_lt.2 h.le)
    · intro h; exact (hτ v _ hp).1 h
  refine isMixture_of_thresholds hX ρ hCD hB (fun v => euPref (τ v))
    (fun v => euPref_isEU (hτpos v))
    (fun v => ⟨(euPref_isEU (hτpos v)).1, euPref_strictOn (hτpos v) hX fun a b hab => ?_⟩)
    hspref
  have hp : (a, b) ∈ Ch := (memCh _).2 hab
  by_cases h : v ≤ f (a, b)
  · exact ((hτ v _ hp).1 h).ne'
  · exact ((hτ v _ hp).2 (not_le.1 h)).ne

/-! ## Tests -/

/-- B meets A: the level lines of `euPref 2` have slope `2` at an interior point. -/
example : tau (euPref_isEU (show (0 : ℝ) < 2 by norm_num)).1 ((1/4 : ℝ), (1/4 : ℝ)) = 2 :=
  tau_euPref (by norm_num) (by refine ⟨?_, ?_, ?_⟩ <;> norm_num) (by simp [Prod.ext_iff])
    (by simp [Prod.ext_iff])

/-- ... and agrees with the constant of `eu_tau_const`. -/
example {τ : ℝ} (hτ : 0 < τ) : ∀ y ∈ Tri, y ≠ ((1 : ℝ), (0 : ℝ)) → y ≠ ((0 : ℝ), (1 : ℝ)) →
    tau (euPref_isEU hτ).1 y = τ := fun _ hy hW hB => tau_euPref hτ hy hW hB

/-- Two parallel chords, `(pa, pb)` on `v = u - 1/4` and `(pc, pd)` on `v = u + 1/4` (slope 1). -/
noncomputable def ppa : Pt := (1/2, 1/4)
noncomputable def ppb : Pt := (1/4, 0)
noncomputable def ppc : Pt := (1/4, 1/2)
noncomputable def ppd : Pt := (0, 1/4)
noncomputable def Xpar : Finset Pt := {ppa, ppb, ppc, ppd}

/-- The two parallel lines do not meet (anywhere), so CD-cross / CD-col say nothing about them. -/
example : ¬ linesMeetInTri ppa ppb ppc ppd := by
  rintro ⟨y, _, h1, h2⟩
  unfold OnLine ppa ppb at h1
  unfold OnLine ppc ppd at h2
  norm_num at h1 h2
  linarith

/-- CD-all has content beyond CD: the Luce rule gives the parallel chords different values
(`52/77 ≠ 25/41`), violating the equal-slope clause of `ChordDominanceAll`. -/
example : ¬ ChordDominanceAll Xpar (Sanity.luce Xpar) := by
  rintro ⟨_, _, hpar⟩
  have hab : ppa ≠ ppb := by simp [ppa, ppb, Prod.ext_iff]
  have hcd : ppc ≠ ppd := by simp [ppc, ppd, Prod.ext_iff]
  have h := hpar ppa ppb ppc ppd
    ⟨by simp [Xpar], by simp [Xpar], by unfold NE ppa ppb; norm_num⟩
    ⟨by simp [Xpar], by simp [Xpar], by unfold NE ppc ppd; norm_num⟩
    (by unfold slope ppa ppb ppc ppd; norm_num)
  unfold fChord at h
  rw [Sanity.luce_p, Sanity.luce_p, ite_eq_left (by simp), ite_eq_left (by simp),
    Finset.sum_pair hab, Finset.sum_pair hcd] at h
  unfold Sanity.wt ppa ppb ppc ppd at h
  norm_num at h

/-! ## The REU clause -/

/-- **Theorem 1, REU clause.** -/
theorem thm1_reu : thm1_reu_stmt := fun _ hX ρ =>
  ⟨reu_necessity hX ρ, fun h => reu_sufficiency hX ρ h.1 h.2⟩

end REU
