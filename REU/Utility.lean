/-
# A utility representation on the triangle

From `hR : IsBetweennessPref R` alone: the hypotenuse `t ↦ hyp t` is a strict FOSD chain, every
`q ∈ Tri` is indifferent to exactly one `hyp t` (connectedness of `[0,1]` + closed contour
sets), and `util q := t` represents `R` on `Tri`. Betweenness makes `util` "between" along
segments; continuity of `util` on `Tri`; an intermediate-value lemma along segments.
-/
import REU.Geometry

namespace REU

open Set

variable {R : Rel}

/-- Clamp to `[0,1]` (used to build total paths into `Tri`). -/
noncomputable def clamp01 (t : ℝ) : ℝ := max 0 (min 1 t)

lemma clamp01_nonneg (t : ℝ) : 0 ≤ clamp01 t := le_max_left _ _

lemma clamp01_le_one (t : ℝ) : clamp01 t ≤ 1 := max_le zero_le_one (min_le_left _ _)

lemma clamp01_of_mem {t : ℝ} (h : t ∈ Icc (0 : ℝ) 1) : clamp01 t = t := by
  unfold clamp01; rw [min_eq_right h.2, max_eq_right h.1]

lemma continuous_clamp01 : Continuous clamp01 := by
  unfold clamp01; fun_prop

lemma hyp_mem_tri {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) : hyp t ∈ Tri := by
  refine ⟨?_, ?_, ?_⟩ <;> simp only [hyp] <;> linarith

lemma hyp_zero : hyp 0 = ((1 : ℝ), (0 : ℝ)) := by simp [hyp]

lemma hyp_one : hyp 1 = ((0 : ℝ), (1 : ℝ)) := by simp [hyp]

lemma mix_zero (q r : Pt) : mix 0 q r = r := by simp [mix]

lemma mix_one (q r : Pt) : mix 1 q r = q := by simp [mix]

lemma mix_symm (t : ℝ) (q r : Pt) : mix t q r = mix (1 - t) r q := by
  ext <;> simp [mix] <;> ring

lemma mix_fst (t : ℝ) (q r : Pt) : (mix t q r).1 = t * q.1 + (1 - t) * r.1 := by simp [mix]

lemma mix_snd (t : ℝ) (q r : Pt) : (mix t q r).2 = t * q.2 + (1 - t) * r.2 := by simp [mix]

lemma R_refl (hR : IsBetweennessPref R) {q : Pt} (hq : q ∈ Tri) : R q q :=
  (hR.complete q hq q hq).elim id id

lemma hyp_strictFOSD {s t : ℝ} (h : s < t) : StrictFOSD (hyp t) (hyp s) := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · simp only [hyp]; linarith
  · simp only [hyp]; linarith
  · intro e
    have := congrArg Prod.snd e
    simp only [hyp] at this
    linarith

/-- On the hypotenuse, `R` is the order of the parameter. -/
lemma R_hyp_iff (hR : IsBetweennessPref R) {s t : ℝ} (hs : s ∈ Icc (0 : ℝ) 1)
    (ht : t ∈ Icc (0 : ℝ) 1) : R (hyp s) (hyp t) ↔ t ≤ s := by
  constructor
  · intro h
    by_contra hlt
    push Not at hlt
    exact (hR.strictMono _ (hyp_mem_tri ht.1 ht.2) _ (hyp_mem_tri hs.1 hs.2)
      (hyp_strictFOSD hlt)).2 h
  · intro h
    rcases h.lt_or_eq with h | h
    · exact (hR.strictMono _ (hyp_mem_tri hs.1 hs.2) _ (hyp_mem_tri ht.1 ht.2)
        (hyp_strictFOSD h)).1
    · rw [h]; exact R_refl hR (hyp_mem_tri hs.1 hs.2)

/-- The best vertex `B = hyp 1` is weakly preferred to every point of `Tri`. -/
lemma R_hyp_one (hR : IsBetweennessPref R) {q : Pt} (hq : q ∈ Tri) : R (hyp 1) q := by
  have hB : hyp 1 ∈ Tri := hyp_mem_tri zero_le_one le_rfl
  by_cases hq1 : hyp 1 = q
  · rw [← hq1]; exact R_refl hR hB
  · refine (hR.strictMono _ hB _ hq ⟨?_, hq1⟩).1
    obtain ⟨h1, h2, h3⟩ := hq
    constructor <;> simp only [hyp] <;> linarith

/-- Every point of `Tri` is weakly preferred to the worst vertex `W = hyp 0`. -/
lemma R_hyp_zero (hR : IsBetweennessPref R) {q : Pt} (hq : q ∈ Tri) : R q (hyp 0) := by
  have hW : hyp 0 ∈ Tri := hyp_mem_tri le_rfl zero_le_one
  by_cases hq1 : q = hyp 0
  · rw [hq1]; exact R_refl hR hW
  · refine (hR.strictMono _ hq _ hW ⟨?_, hq1⟩).1
    obtain ⟨h1, h2, h3⟩ := hq
    constructor <;> simp only [hyp] <;> linarith

/-- Intermediate value property of a continuous preference along a path in `Tri`. -/
lemma exists_indiff_of_path (hR : IsBetweennessPref R) {γ : ℝ → Pt} (hγ : Continuous γ)
    (hγT : ∀ s, γ s ∈ Tri) {h : Pt} (hh : h ∈ Tri) {a b : ℝ} (hab : a ≤ b)
    (ha : R h (γ a)) (hb : R (γ b) h) : ∃ s ∈ Icc a b, Indiff R (γ s) h := by
  let g : ℝ → Tri := fun s => ⟨γ s, hγT s⟩
  have hg : Continuous g := hγ.subtype_mk hγT
  have h1 : IsClosed {s | R (γ s) h} := (hR.closed_upper h hh).preimage hg
  have h2 : IsClosed {s | R h (γ s)} := (hR.closed_lower h hh).preimage hg
  obtain ⟨s, hs, hs1, hs2⟩ := isPreconnected_closed_iff.1 isPreconnected_Icc _ _ h1 h2
    (fun s _ => hR.complete (γ s) (hγT s) h hh) ⟨b, right_mem_Icc.2 hab, hb⟩
    ⟨a, left_mem_Icc.2 hab, ha⟩
  exact ⟨s, hs, hs1, hs2⟩

lemma exists_hyp_indiff (hR : IsBetweennessPref R) {q : Pt} (hq : q ∈ Tri) :
    ∃ t, t ∈ Icc (0 : ℝ) 1 ∧ Indiff R (hyp t) q := by
  have hγ : Continuous fun s => hyp (clamp01 s) := by
    unfold hyp; exact (continuous_const.sub continuous_clamp01).prodMk continuous_clamp01
  have hγT : ∀ s, hyp (clamp01 s) ∈ Tri := fun s => hyp_mem_tri (clamp01_nonneg s)
    (clamp01_le_one s)
  have h0 : clamp01 0 = 0 := clamp01_of_mem ⟨le_rfl, zero_le_one⟩
  have h1 : clamp01 1 = 1 := clamp01_of_mem ⟨zero_le_one, le_rfl⟩
  obtain ⟨s, hs, hind⟩ := exists_indiff_of_path hR hγ hγT hq zero_le_one
    (by simp only [h0]; exact R_hyp_zero hR hq) (by simp only [h1]; exact R_hyp_one hR hq)
  exact ⟨s, hs, by rwa [clamp01_of_mem hs] at hind⟩

/-- The utility of `q`: the hypotenuse parameter of the (unique) `hyp t ∼ q`. Meaningful for
`q ∈ Tri`. -/
noncomputable def util (_hR : IsBetweennessPref R) (q : Pt) : ℝ :=
  Classical.epsilon (fun t => t ∈ Icc (0 : ℝ) 1 ∧ Indiff R (hyp t) q)

lemma util_spec (hR : IsBetweennessPref R) {q : Pt} (hq : q ∈ Tri) :
    util hR q ∈ Icc (0 : ℝ) 1 ∧ Indiff R (hyp (util hR q)) q :=
  Classical.epsilon_spec (exists_hyp_indiff hR hq)

lemma util_mem_Icc (hR : IsBetweennessPref R) {q : Pt} (hq : q ∈ Tri) :
    util hR q ∈ Icc (0 : ℝ) 1 := (util_spec hR hq).1

/-- Representation: on `Tri`, `q ≽ r ↔ util r ≤ util q`. -/
theorem pref_iff_util (hR : IsBetweennessPref R) {q r : Pt} (hq : q ∈ Tri) (hr : r ∈ Tri) :
    R q r ↔ util hR r ≤ util hR q := by
  obtain ⟨hu, hqu1, hqu2⟩ := util_spec hR hq
  obtain ⟨hv, hrv1, hrv2⟩ := util_spec hR hr
  have hU := hyp_mem_tri hu.1 hu.2
  have hV := hyp_mem_tri hv.1 hv.2
  rw [← R_hyp_iff hR hu hv]
  constructor
  · intro h
    exact hR.trans _ hU _ hq _ hV hqu1 (hR.trans _ hq _ hr _ hV h hrv2)
  · intro h
    exact hR.trans _ hq _ hU _ hr hqu2 (hR.trans _ hU _ hV _ hr h hrv1)

lemma util_hyp (hR : IsBetweennessPref R) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    util hR (hyp t) = t := by
  have hT := hyp_mem_tri ht.1 ht.2
  obtain ⟨hu, h1, h2⟩ := util_spec hR hT
  exact le_antisymm ((R_hyp_iff hR ht hu).1 h2) ((R_hyp_iff hR hu ht).1 h1)

lemma indiff_iff_util (hR : IsBetweennessPref R) {q r : Pt} (hq : q ∈ Tri) (hr : r ∈ Tri) :
    Indiff R q r ↔ util hR q = util hR r := by
  rw [Indiff, pref_iff_util hR hq hr, pref_iff_util hR hr hq]
  constructor
  · rintro ⟨h1, h2⟩; exact le_antisymm h2 h1
  · intro h; exact ⟨h.ge, h.le⟩

lemma spref_iff_util (hR : IsBetweennessPref R) {q r : Pt} (hq : q ∈ Tri) (hr : r ∈ Tri) :
    SPref R q r ↔ util hR r < util hR q := by
  rw [SPref, pref_iff_util hR hq hr, pref_iff_util hR hr hq, not_le]
  exact ⟨fun h => h.2, fun h => ⟨h.le, h⟩⟩

theorem util_strictFOSD (hR : IsBetweennessPref R) {q r : Pt} (hq : q ∈ Tri) (hr : r ∈ Tri)
    (h : StrictFOSD q r) : util hR r < util hR q := by
  exact (spref_iff_util hR hq hr).1 (hR.strictMono q hq r hr h)

/-- `util W = 0`, `util B = 1`. -/
lemma util_hyp_zero (hR : IsBetweennessPref R) : util hR (hyp 0) = 0 :=
  util_hyp hR ⟨le_rfl, zero_le_one⟩

lemma util_hyp_one (hR : IsBetweennessPref R) : util hR (hyp 1) = 1 :=
  util_hyp hR ⟨zero_le_one, le_rfl⟩

/-- `0 < util y < 1` off the worst and best vertices. -/
lemma util_mem_Ioo (hR : IsBetweennessPref R) {y : Pt} (hy : y ∈ Tri)
    (hW : y ≠ ((1 : ℝ), (0 : ℝ))) (hB : y ≠ ((0 : ℝ), (1 : ℝ))) :
    util hR y ∈ Ioo (0 : ℝ) 1 := by
  obtain ⟨h1, h2, h3⟩ := hy
  have hW' : hyp 0 ∈ Tri := hyp_mem_tri le_rfl zero_le_one
  have hB' : hyp 1 ∈ Tri := hyp_mem_tri zero_le_one le_rfl
  constructor
  · have := util_strictFOSD hR ⟨h1, h2, h3⟩ hW' ⟨⟨by simp only [hyp]; linarith,
      by simp only [hyp]; linarith⟩, by rwa [hyp_zero]⟩
    rwa [util_hyp_zero] at this
  · have := util_strictFOSD hR hB' ⟨h1, h2, h3⟩ ⟨⟨by simp only [hyp]; linarith,
      by simp only [hyp]; linarith⟩, by rw [hyp_one]; exact fun e => hB e.symm⟩
    rwa [util_hyp_one] at this

/-- Betweenness: along a segment, `util` lies between its endpoint values. -/
theorem util_mix_mem (hR : IsBetweennessPref R) {x z : Pt} (hx : x ∈ Tri) (hz : z ∈ Tri)
    {l : ℝ} (hl : l ∈ Icc (0 : ℝ) 1) :
    util hR (mix l x z) ∈ uIcc (util hR x) (util hR z) := by
  have hm := mix_mem_tri hx hz hl.1 hl.2
  rcases hl.1.eq_or_lt with h0 | h0
  · rw [← h0, mix_zero]; exact right_mem_uIcc
  rcases hl.2.eq_or_lt with h1 | h1
  · rw [h1, mix_one]; exact left_mem_uIcc
  rcases lt_trichotomy (util hR z) (util hR x) with h | h | h
  · have hs := (spref_iff_util hR hx hz).2 h
    obtain ⟨hA, hB⟩ := hR.btw_strict x hx z hz l ⟨h0, h1⟩ hs
    rw [spref_iff_util hR hx hm] at hA
    rw [spref_iff_util hR hm hz] at hB
    exact Set.mem_uIcc.2 (Or.inr ⟨hB.le, hA.le⟩)
  · have hi := (indiff_iff_util hR hx hz).2 h.symm
    have := (indiff_iff_util hR hm hx).1 (hR.btw_indiff x hx z hz l ⟨h0, h1⟩ hi)
    rw [this]; exact left_mem_uIcc
  · have hs := (spref_iff_util hR hz hx).2 h
    rw [mix_symm] at hm ⊢
    obtain ⟨hA, hB⟩ := hR.btw_strict z hz x hx (1 - l) ⟨by linarith, by linarith⟩ hs
    rw [spref_iff_util hR hz hm] at hA
    rw [spref_iff_util hR hm hx] at hB
    exact Set.mem_uIcc.2 (Or.inl ⟨hB.le, hA.le⟩)

/-- Level sets are convex. -/
theorem level_convex (hR : IsBetweennessPref R) {x z : Pt} (hx : x ∈ Tri) (hz : z ∈ Tri)
    (hxz : util hR x = util hR z) {l : ℝ} (hl : l ∈ Icc (0 : ℝ) 1) :
    util hR (mix l x z) = util hR x := by
  have h := util_mix_mem hR hx hz hl
  rw [← hxz, Set.uIcc_self] at h
  exact h

theorem util_continuousOn (hR : IsBetweennessPref R) : ContinuousOn (util hR) Tri := by
  rw [continuousOn_iff_continuous_domRestrict, OrderTopology.continuous_iff]
  intro a
  constructor
  · rcases lt_or_ge a 0 with ha | ha
    · convert isOpen_univ
      ext q
      simp only [Set.mem_preimage, Set.domRestrict_apply, Set.mem_Ioi, Set.mem_univ, iff_true]
      exact lt_of_lt_of_le ha (util_mem_Icc hR q.2).1
    rcases le_or_gt a 1 with ha1 | ha1
    · have hA := hyp_mem_tri ha ha1
      convert (hR.closed_lower _ hA).isOpen_compl
      ext q
      simp only [Set.mem_preimage, Set.domRestrict_apply, Set.mem_Ioi, Set.mem_compl_iff,
        Set.mem_ofPred_eq]
      rw [pref_iff_util hR hA q.2, util_hyp hR ⟨ha, ha1⟩, not_le]
    · convert isOpen_empty
      ext q
      simp only [Set.mem_preimage, Set.domRestrict_apply, Set.mem_Ioi, Set.mem_empty_iff_false,
        iff_false, not_lt]
      exact (util_mem_Icc hR q.2).2.trans ha1.le
  · rcases lt_or_ge a 0 with ha | ha
    · convert isOpen_empty
      ext q
      simp only [Set.mem_preimage, Set.domRestrict_apply, Set.mem_Iio, Set.mem_empty_iff_false,
        iff_false, not_lt]
      exact ha.le.trans (util_mem_Icc hR q.2).1
    rcases le_or_gt a 1 with ha1 | ha1
    · have hA := hyp_mem_tri ha ha1
      convert (hR.closed_upper _ hA).isOpen_compl
      ext q
      simp only [Set.mem_preimage, Set.domRestrict_apply, Set.mem_Iio, Set.mem_compl_iff,
        Set.mem_ofPred_eq]
      rw [pref_iff_util hR q.2 hA, util_hyp hR ⟨ha, ha1⟩, not_le]
    · convert isOpen_univ
      ext q
      simp only [Set.mem_preimage, Set.domRestrict_apply, Set.mem_Iio, Set.mem_univ, iff_true]
      exact lt_of_le_of_lt (util_mem_Icc hR q.2).2 ha1

/-- Intermediate values of `util` are attained on every segment. -/
theorem exists_mix_util_eq (hR : IsBetweennessPref R) {x z : Pt} (hx : x ∈ Tri) (hz : z ∈ Tri)
    {c : ℝ} (hc1 : util hR z ≤ c) (hc2 : c ≤ util hR x) :
    ∃ l ∈ Icc (0 : ℝ) 1, util hR (mix l x z) = c := by
  have hc : c ∈ Icc (0 : ℝ) 1 :=
    ⟨(util_mem_Icc hR hz).1.trans hc1, hc2.trans (util_mem_Icc hR hx).2⟩
  have hH := hyp_mem_tri hc.1 hc.2
  have hγ : Continuous fun s => mix (clamp01 s) x z := by
    unfold mix
    exact (continuous_clamp01.smul continuous_const).add
      ((continuous_const.sub continuous_clamp01).smul continuous_const)
  have hγT : ∀ s, mix (clamp01 s) x z ∈ Tri := fun s =>
    mix_mem_tri hx hz (clamp01_nonneg s) (clamp01_le_one s)
  have h0 : clamp01 0 = 0 := clamp01_of_mem ⟨le_rfl, zero_le_one⟩
  have h1 : clamp01 1 = 1 := clamp01_of_mem ⟨zero_le_one, le_rfl⟩
  obtain ⟨s, hs, hind⟩ := exists_indiff_of_path hR hγ hγT hH zero_le_one
    (by simp only [h0, mix_zero]; rw [pref_iff_util hR hH hz, util_hyp hR hc]; exact hc1)
    (by simp only [h1, mix_one]; rw [pref_iff_util hR hx hH, util_hyp hR hc]; exact hc2)
  refine ⟨s, hs, ?_⟩
  rw [clamp01_of_mem hs] at hind
  rw [(indiff_iff_util hR (mix_mem_tri hx hz hs.1 hs.2) hH).1 hind, util_hyp hR hc]

end REU
