/-
# The chain preference satisfies the betweenness axioms

Given knots `K` (`Chains.lean`), the chain of affine functionals is `L₀ = LW`, `L_{k+1} = ℓ(α k, β k)`
for `k < n`, `L_{n+1} = LB`. Consecutive members are nested on `Tri`
(`L_{j+1} q ≥ 0 → L_j q > 0`), so every `q ∈ Tri` lies in a region `j` with
`L_j q ≥ 0 ≥ L_{j+1} q`; the utility is `U q = j + L_j q / (L_j q − L_{j+1} q)`.

Deviation from the note (7.1/7.2): instead of `Σ φ_j` with `max`es, `chainUtil` uses the region
index directly (same function on `Tri`), and the generic criterion `isBetweenness_of_util`
asks, for every level `c = U r`, for a continuous affine `G` (strictly FOSD increasing) whose
sign on `Tri` is the sign of `U − c` (`IsLevelSep`). For the chain, `G = (1−λ) L_j + λ L_{j+1}`
with `j, λ` the region data of `r` (the "pencil interpolation"). This gives continuity
(closed contour sets), monotonicity and both betweenness axioms directly.
-/
import REU.Chains
import REU.Necessity

namespace REU

open Set

/-! ## 7.1 Generic criterion -/

/-- `G` is an affine, continuous, strictly FOSD-increasing functional whose sign on `Tri`
is the sign of `U − c`. -/
def IsLevelSep (U : Pt → ℝ) (c : ℝ) (G : Pt → ℝ) : Prop :=
  Continuous G ∧ (∀ t q r, G (mix t q r) = t * G q + (1 - t) * G r) ∧
    (∀ q r, StrictFOSD q r → G r < G q) ∧
    ∀ q ∈ Tri, (U q < c ↔ G q < 0) ∧ (U q = c ↔ G q = 0)

lemma IsLevelSep.gt_iff {U : Pt → ℝ} {c : ℝ} {G : Pt → ℝ} (h : IsLevelSep U c G) {q : Pt}
    (hq : q ∈ Tri) : c < U q ↔ 0 < G q := by
  obtain ⟨h1, h2⟩ := h.2.2.2 q hq
  constructor
  · intro hc
    rcases lt_trichotomy (G q) 0 with hg | hg | hg
    · linarith [h1.2 hg]
    · linarith [h2.2 hg]
    · exact hg
  · intro hg
    rcases lt_trichotomy (U q) c with hu | hu | hu
    · linarith [h1.1 hu]
    · linarith [h2.1 hu]
    · exact hu

lemma IsLevelSep.le_iff {U : Pt → ℝ} {c : ℝ} {G : Pt → ℝ} (h : IsLevelSep U c G) {q : Pt}
    (hq : q ∈ Tri) : U q ≤ c ↔ G q ≤ 0 := by
  rw [← not_lt, h.gt_iff hq, not_lt]

/-- 7.1: a utility with affine level separators induces a betweenness preference. -/
theorem isBetweenness_of_util (U : Pt → ℝ) (hsep : ∀ r ∈ Tri, ∃ G, IsLevelSep U (U r) G) :
    IsBetweennessPref (fun q r => U r ≤ U q) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro q _ r _; exact le_total _ _
  · intro q _ r _ s _ h1 h2; exact le_trans h2 h1
  · intro r hr
    obtain ⟨G, hG⟩ := hsep r hr
    have : {q : Tri | U r ≤ U q.1} = {q : Tri | 0 ≤ G q.1} := by
      ext q
      simp only [Set.mem_ofPred_eq]
      rw [← not_lt, ← not_lt, (hG.2.2.2 q.1 q.2).1]
    rw [this]
    exact isClosed_le continuous_const (hG.1.comp continuous_subtype_val)
  · intro r hr
    obtain ⟨G, hG⟩ := hsep r hr
    have : {q : Tri | U q.1 ≤ U r} = {q : Tri | G q.1 ≤ 0} := by
      ext q
      simp only [Set.mem_ofPred_eq]
      exact hG.le_iff q.2
    rw [this]
    exact isClosed_le (hG.1.comp continuous_subtype_val) continuous_const
  · intro q hq r hr h
    obtain ⟨G, hG⟩ := hsep r hr
    have h0 : G r = 0 := ((hG.2.2.2 r hr).2).1 rfl
    have := hG.2.2.1 q r h
    have hlt : U r < U q := (hG.gt_iff hq).2 (by linarith)
    exact ⟨hlt.le, not_le.2 hlt⟩
  · intro q hq r hr t ht h
    have hlt : U r < U q := lt_of_not_ge h.2
    obtain ⟨G, hG⟩ := hsep r hr
    obtain ⟨G', hG'⟩ := hsep q hq
    have hm := mix_mem_tri hq hr ht.1.le ht.2.le
    have g0 : G r = 0 := ((hG.2.2.2 r hr).2).1 rfl
    have g1 : 0 < G q := (hG.gt_iff hq).1 hlt
    have g0' : G' q = 0 := ((hG'.2.2.2 q hq).2).1 rfl
    have g1' : G' r < 0 := ((hG'.2.2.2 r hr).1).1 hlt
    have a1 : U r < U (mix t q r) :=
      (hG.gt_iff hm).2 (by rw [hG.2.1, g0]; nlinarith [ht.1])
    have a2 : U (mix t q r) < U q :=
      ((hG'.2.2.2 _ hm).1).2 (by rw [hG'.2.1, g0']; nlinarith [ht.2])
    exact ⟨⟨a2.le, not_le.2 a2⟩, ⟨a1.le, not_le.2 a1⟩⟩
  · intro q hq r hr t ht h
    have he : U q = U r := le_antisymm h.2 h.1
    obtain ⟨G, hG⟩ := hsep r hr
    have hm := mix_mem_tri hq hr ht.1.le ht.2.le
    have g0 : G r = 0 := ((hG.2.2.2 r hr).2).1 rfl
    have gq : G q = 0 := ((hG.2.2.2 q hq).2).1 he
    have : U (mix t q r) = U r := ((hG.2.2.2 _ hm).2).2 (by rw [hG.2.1, g0, gq]; ring)
    show U q ≤ U (mix t q r) ∧ U (mix t q r) ≤ U q
    constructor <;> linarith

/-- Level sets of such a utility are line pieces: if `U a = U b` (`a.1 ≠ b.1`), every
`y ∈ Tri` on line `ab` has the same utility. -/
lemma util_eq_of_onLine {U : Pt → ℝ} (hsep : ∀ r ∈ Tri, ∃ G, IsLevelSep U (U r) G) {a b y : Pt}
    (ha : a ∈ Tri) (hb : b ∈ Tri) (hy : y ∈ Tri) (hab : a.1 ≠ b.1) (hline : OnLine a b y)
    (he : U a = U b) : U y = U a := by
  obtain ⟨G, hG⟩ := hsep a ha
  have hd : a.1 - b.1 ≠ 0 := sub_ne_zero.2 hab
  have hmix : y = mix ((y.1 - b.1) / (a.1 - b.1)) a b := by
    unfold OnLine at hline
    ext
    · rw [mix_fst]; field_simp; ring
    · rw [mix_snd]; field_simp; linear_combination hline
  have g0 : G a = 0 := ((hG.2.2.2 a ha).2).1 rfl
  have g1 : G b = 0 := ((hG.2.2.2 b hb).2).1 he.symm
  exact ((hG.2.2.2 y hy).2).2 (by rw [hmix, hG.2.1, g0, g1]; ring)

/-! ## 7.2 The chain and its utility -/

/-- The chain `L₀ = LW`, `L_{k+1} = ℓ(α k, β k)` (`k < n`), `L_j = LB` for `j ≥ n + 1`. -/
noncomputable def chainL (K : Knots) : ℕ → Pt → ℝ
  | 0 => LW
  | k + 1 => if h : k < K.n then lineFun (K.α ⟨k, h⟩) (K.β ⟨k, h⟩) else LB

lemma chainL_succ (K : Knots) (k : ℕ) : chainL K (k + 1) =
    if h : k < K.n then lineFun (K.α ⟨k, h⟩) (K.β ⟨k, h⟩) else LB := rfl

lemma chainL_fin (K : Knots) (k : Fin K.n) :
    chainL K ((k : ℕ) + 1) = lineFun (K.α k) (K.β k) := by
  rw [chainL_succ, dite_eq_left k.isLt]

lemma chainL_last (K : Knots) : chainL K (K.n + 1) = LB := by
  rw [chainL_succ, dite_eq_right (lt_irrefl _)]

lemma chainL_mix (K : Knots) (j : ℕ) (t : ℝ) (q r : Pt) :
    chainL K j (mix t q r) = t * chainL K j q + (1 - t) * chainL K j r := by
  cases j with
  | zero => exact LW_mix t q r
  | succ k =>
    rw [chainL_succ]
    split_ifs with h
    · exact lineFun_mix _ _ t q r
    · exact LB_mix t q r

lemma continuous_chainL (K : Knots) (j : ℕ) : Continuous (chainL K j) := by
  cases j with
  | zero => exact continuous_LW
  | succ k =>
    rw [chainL_succ]
    split_ifs with h
    · exact continuous_lineFun _ _
    · exact continuous_LB

lemma chainL_lt_of_strictFOSD (K : Knots) (j : ℕ) {q r : Pt} (h : StrictFOSD q r) :
    chainL K j r < chainL K j q := by
  cases j with
  | zero => exact LW_lt_of_strictFOSD h
  | succ k =>
    rw [chainL_succ]
    split_ifs with hk
    · exact lineFun_lt_of_strictFOSD (K.inBand _) (K.α_mem _) h
    · exact LB_lt_of_strictFOSD h

lemma chainL_zero_nonneg (K : Knots) {q : Pt} (hq : q ∈ Tri) : 0 ≤ chainL K 0 q :=
  LW_nonneg hq

lemma chainL_last_nonpos (K : Knots) {q : Pt} (hq : q ∈ Tri) : chainL K (K.n + 1) q ≤ 0 := by
  rw [chainL_last]; exact LB_nonpos hq

/-- Consecutive nesting: `L_{j+1} q ≥ 0 → L_j q > 0` on `Tri`, for `j ≤ n`. -/
lemma chainL_nested_succ (K : Knots) {j : ℕ} (hj : j ≤ K.n) {q : Pt} (hq : q ∈ Tri)
    (h : 0 ≤ chainL K (j + 1) q) : 0 < chainL K j q := by
  cases j with
  | zero =>
    rw [chainL_succ] at h
    change 0 < LW q
    split_ifs at h with h0
    · exact nested_W (K.inBand _) (K.α_mem _) hq h
    · exact nested_WB hq h
  | succ k =>
    have hk : k < K.n := hj
    rw [chainL_fin K ⟨k, hk⟩]
    rw [chainL_succ] at h
    split_ifs at h with h1
    · exact nested (K.inBand _) (K.α_mem _) (K.inBand _) (K.α_mem _)
        (K.α_mono (show (⟨k, hk⟩ : Fin K.n) < ⟨k + 1, h1⟩ from Nat.lt_succ_self k))
        (K.β_mono (show (⟨k, hk⟩ : Fin K.n) < ⟨k + 1, h1⟩ from Nat.lt_succ_self k)) hq h
    · exact nested_B (K.inBand _) (K.α_mem _) hq h

/-- Nesting along the chain: `i < m ≤ n + 1`, `L_m q ≥ 0 → L_i q > 0`. -/
lemma chainL_nested (K : Knots) {i m : ℕ} (him : i < m) (hm : m ≤ K.n + 1) {q : Pt}
    (hq : q ∈ Tri) (h : 0 ≤ chainL K m q) : 0 < chainL K i q := by
  induction m with
  | zero => omega
  | succ m ih =>
    have h1 := chainL_nested_succ K (by omega : m ≤ K.n) hq h
    rcases Nat.lt_succ_iff_lt_or_eq.1 him with h2 | h2
    · exact ih h2 (by omega) h1.le
    · rw [h2]; exact h1

open Classical in
/-- Region index of `q`: the least `j` with `L_{j+1} q ≤ 0` (capped at `n`). -/
noncomputable def chainIdx (K : Knots) (q : Pt) : ℕ :=
  Nat.find (⟨K.n, Or.inl rfl⟩ : ∃ i, i = K.n ∨ chainL K (i + 1) q ≤ 0)

/-- Position inside region `j`: `L_j / (L_j − L_{j+1})`. -/
noncomputable def chainPhi (K : Knots) (j : ℕ) (q : Pt) : ℝ :=
  chainL K j q / (chainL K j q - chainL K (j + 1) q)

/-- The chain utility: `U q = j + L_j q / (L_j q − L_{j+1} q)` for `q` in region `j`. -/
noncomputable def chainUtil (K : Knots) (q : Pt) : ℝ :=
  (chainIdx K q : ℝ) + chainPhi K (chainIdx K q) q

/-- `q` lies in region `j`. -/
def InRegion (K : Knots) (j : ℕ) (q : Pt) : Prop :=
  j ≤ K.n ∧ 0 ≤ chainL K j q ∧ chainL K (j + 1) q ≤ 0

lemma chainIdx_region (K : Knots) {q : Pt} (hq : q ∈ Tri) : InRegion K (chainIdx K q) q := by
  classical
  unfold chainIdx
  refine ⟨Nat.find_min' _ (Or.inl rfl), ?_, ?_⟩
  · rcases hidx : Nat.find (⟨K.n, Or.inl rfl⟩ : ∃ i, i = K.n ∨ chainL K (i + 1) q ≤ 0)
      with _ | i
    · exact chainL_zero_nonneg K hq
    · have := Nat.find_min (⟨K.n, Or.inl rfl⟩ : ∃ i, i = K.n ∨ chainL K (i + 1) q ≤ 0)
        (show i < Nat.find (⟨K.n, Or.inl rfl⟩ : ∃ i, i = K.n ∨ chainL K (i + 1) q ≤ 0) by
          omega)
      push Not at this
      exact this.2.le
  · rcases Nat.find_spec (⟨K.n, Or.inl rfl⟩ : ∃ i, i = K.n ∨ chainL K (i + 1) q ≤ 0)
      with h | h
    · rw [h]; exact chainL_last_nonpos K hq
    · exact h

lemma region_den_pos (K : Knots) {j : ℕ} {q : Pt} (hq : q ∈ Tri) (h : InRegion K j q) :
    0 < chainL K j q - chainL K (j + 1) q := by
  obtain ⟨hj, h0, h1⟩ := h
  rcases h1.lt_or_eq with h1 | h1
  · linarith
  · have := chainL_nested_succ K hj hq h1.ge
    linarith

lemma region_phi_nonneg (K : Knots) {j : ℕ} {q : Pt} (hq : q ∈ Tri) (h : InRegion K j q) :
    0 ≤ chainPhi K j q :=
  div_nonneg h.2.1 (region_den_pos K hq h).le

lemma region_phi_le_one (K : Knots) {j : ℕ} {q : Pt} (hq : q ∈ Tri) (h : InRegion K j q) :
    chainPhi K j q ≤ 1 :=
  (div_le_one (region_den_pos K hq h)).2 (by linarith [h.2.2])

lemma region_phi_lt_one (K : Knots) {j : ℕ} {q : Pt} (hq : q ∈ Tri) (h : InRegion K j q)
    (hl : chainL K (j + 1) q < 0) : chainPhi K j q < 1 :=
  (div_lt_one (region_den_pos K hq h)).2 (by linarith)

lemma region_phi_pos (K : Knots) {j : ℕ} {q : Pt} (hq : q ∈ Tri) (h : InRegion K j q)
    (hl : 0 < chainL K j q) : 0 < chainPhi K j q :=
  div_pos hl (region_den_pos K hq h)

/-- The utility can be computed in any region containing `q` (regions overlap only on a
boundary line, where both formulas agree). -/
lemma region_util (K : Knots) {j : ℕ} {q : Pt} (hq : q ∈ Tri) (h : InRegion K j q) :
    chainUtil K q = j + chainPhi K j q := by
  have hr := chainIdx_region K hq
  show (chainIdx K q : ℝ) + chainPhi K (chainIdx K q) q = j + chainPhi K j q
  generalize chainIdx K q = r at hr ⊢
  have hjn := h.1
  have hrn := hr.1
  rcases lt_trichotomy r j with hlt | heq | hgt
  · have hr1 : r + 1 = j := by
      by_contra hne
      have := chainL_nested K (show r + 1 < j by omega) (by omega) hq h.2.1
      linarith [hr.2.2]
    subst hr1
    have hz : chainL K (r + 1) q = 0 := le_antisymm hr.2.2 h.2.1
    have hpos := chainL_nested_succ K hr.1 hq hz.ge
    unfold chainPhi
    rw [hz, sub_zero, div_self hpos.ne', zero_div]
    push_cast; ring
  · rw [heq]
  · have hj1 : j + 1 = r := by
      by_contra hne
      have := chainL_nested K (show j + 1 < r by omega) (by omega) hq hr.2.1
      linarith [h.2.2]
    subst hj1
    have hz : chainL K (j + 1) q = 0 := le_antisymm h.2.2 hr.2.1
    have hpos := chainL_nested_succ K h.1 hq hz.ge
    unfold chainPhi
    rw [hz, sub_zero, div_self hpos.ne', zero_div]
    push_cast; ring

lemma chainUtil_lt_of_neg (K : Knots) {m : ℕ} {q : Pt} (hq : q ∈ Tri)
    (hl : chainL K m q < 0) : chainUtil K q < m := by
  have hr := chainIdx_region K hq
  have hu := region_util K hq hr
  generalize chainIdx K q = r at hr hu
  have hrn := hr.1
  have hrm : r < m := by
    by_contra hge
    push Not at hge
    rcases hge.lt_or_eq with hgt | heq
    · linarith [chainL_nested K hgt (by omega) hq hr.2.1]
    · subst heq; linarith [hr.2.1]
  rw [hu]
  rcases Nat.lt_or_ge (r + 1) m with h1 | h1
  · have : ((r : ℕ) : ℝ) + 1 < m := by exact_mod_cast h1
    linarith [region_phi_le_one K hq hr]
  · have he : r + 1 = m := by omega
    rw [← he] at hl
    have := region_phi_lt_one K hq hr hl
    rw [← he]; push_cast; linarith

lemma chainUtil_gt_of_pos (K : Knots) {m : ℕ} (hm : m ≤ K.n + 1) {q : Pt} (hq : q ∈ Tri)
    (hl : 0 < chainL K m q) : (m : ℝ) < chainUtil K q := by
  have hr := chainIdx_region K hq
  have hu := region_util K hq hr
  generalize chainIdx K q = r at hr hu
  have hrn := hr.1
  have hrm : m ≤ r := by
    by_contra hlt
    push Not at hlt
    rcases Nat.lt_or_ge (r + 1) m with h1 | h1
    · linarith [chainL_nested K h1 hm hq hl.le, hr.2.2]
    · have he : r + 1 = m := by omega
      rw [← he] at hl; linarith [hr.2.2]
  rw [hu]
  rcases hrm.lt_or_eq with h1 | h1
  · have : (m : ℝ) < r := by exact_mod_cast h1
    linarith [region_phi_nonneg K hq hr]
  · subst h1
    have := region_phi_pos K hq hr hl
    linarith

lemma combo_pos {a b l : ℝ} (ha : 0 < a) (hb : 0 < b) (hl0 : 0 ≤ l) (hl1 : l ≤ 1) :
    0 < (1 - l) * a + l * b := by
  rcases le_total a b with h | h
  · nlinarith [mul_nonneg hl0 (sub_nonneg.2 h)]
  · nlinarith [mul_nonneg (sub_nonneg.2 hl1) (sub_nonneg.2 h)]

/-- The level separator of `chainUtil` at the level of `r`: the pencil interpolation
`(1 − λ) L_j + λ L_{j+1}` with `j`, `λ` the region data of `r`. -/
theorem chainUtil_levelSep (K : Knots) {r : Pt} (hr : r ∈ Tri) :
    IsLevelSep (chainUtil K) (chainUtil K r)
      (fun q => (1 - chainPhi K (chainIdx K r) r) * chainL K (chainIdx K r) q +
        chainPhi K (chainIdx K r) r * chainL K (chainIdx K r + 1) q) := by
  have hreg := chainIdx_region K hr
  have hjn := hreg.1
  set j := chainIdx K r
  set l := chainPhi K j r with hl
  have hl0 : 0 ≤ l := region_phi_nonneg K hr hreg
  have hl1 : l ≤ 1 := region_phi_le_one K hr hreg
  have hc : chainUtil K r = j + l := rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (continuous_const.mul (continuous_chainL K j)).add
      (continuous_const.mul (continuous_chainL K (j + 1)))
  · intro t q s
    simp only [chainL_mix]
    ring
  · intro q s h
    have h1 := chainL_lt_of_strictFOSD K j h
    have h2 := chainL_lt_of_strictFOSD K (j + 1) h
    have := combo_pos (sub_pos.2 h1) (sub_pos.2 h2) hl0 hl1
    simp only
    linarith
  · intro q hq
    rw [hc]
    simp only
    by_cases hA : 0 < chainL K (j + 1) q
    · have hU := chainUtil_gt_of_pos K (by omega : j + 1 ≤ K.n + 1) hq hA
      have hJ := chainL_nested_succ K hreg.1 hq hA.le
      have hG := combo_pos hJ hA hl0 hl1
      push_cast at hU
      constructor
      · constructor <;> intro h <;> linarith
      · constructor <;> intro h <;> linarith
    by_cases hB : chainL K j q < 0
    · have hU := chainUtil_lt_of_neg K hq hB
      have hJ : chainL K (j + 1) q < 0 := by
        by_contra hcon
        push Not at hcon
        linarith [chainL_nested_succ K hreg.1 hq hcon]
      have hG := combo_pos (neg_pos.2 hB) (neg_pos.2 hJ) hl0 hl1
      constructor
      · constructor <;> intro h <;> linarith
      · constructor <;> intro h <;> linarith
    push Not at hA hB
    have hq' : InRegion K j q := ⟨hreg.1, hB, hA⟩
    have hD := region_den_pos K hq hq'
    rw [region_util K hq hq']
    unfold chainPhi
    constructor
    · rw [add_lt_add_iff_left, div_lt_iff₀ hD]
      constructor <;> intro h <;> linarith
    · rw [add_right_inj, div_eq_iff hD.ne']
      constructor <;> intro h <;> linarith

/-! ## 7.5 The chain preference -/

/-- The chain preference: `q ≽ r ↔ chainUtil r ≤ chainUtil q`. -/
def chainPref (K : Knots) : Rel := fun q r => chainUtil K r ≤ chainUtil K q

theorem chainPref_isBtw (K : Knots) : IsBetweennessPref (chainPref K) :=
  isBetweenness_of_util (chainUtil K) fun _ hr => ⟨_, chainUtil_levelSep K hr⟩

/-! ## 7.6 Knot lines and chords -/

/-- 7.6: `chainUtil` is constant `= k + 1` on the knot line `ℓ(α k, β k)`. -/
theorem chainPref_knot (K : Knots) (k : Fin K.n) {q : Pt} (hq : q ∈ Tri)
    (h : lineFun (K.α k) (K.β k) q = 0) : chainUtil K q = ((k : ℕ) : ℝ) + 1 := by
  have h0 : chainL K ((k : ℕ) + 1) q = 0 := by rw [chainL_fin]; exact h
  have h1 : chainL K ((k : ℕ) + 1 + 1) q ≤ 0 := by
    by_contra hcon
    push Not at hcon
    linarith [chainL_nested_succ K (show (k : ℕ) + 1 ≤ K.n from k.isLt) hq hcon.le]
  rw [region_util K hq ⟨k.isLt, h0.ge, h1⟩]
  unfold chainPhi
  rw [h0, zero_div]
  push_cast; ring

/-- On `Tri`, the level `k + 1` of `chainUtil` is exactly the knot line `ℓ(α k, β k)`. -/
theorem chainUtil_eq_knot_iff (K : Knots) (k : Fin K.n) {q : Pt} (hq : q ∈ Tri) :
    chainUtil K q = ((k : ℕ) : ℝ) + 1 ↔ lineFun (K.α k) (K.β k) q = 0 := by
  refine ⟨fun hu => ?_, chainPref_knot K k hq⟩
  rw [← chainL_fin]
  have hm : (k : ℕ) + 1 ≤ K.n + 1 := by omega
  rcases lt_trichotomy (chainL K ((k : ℕ) + 1) q) 0 with h | h | h
  · have := chainUtil_lt_of_neg K hq h
    push_cast at this; linarith
  · exact h
  · have := chainUtil_gt_of_pos K hm hq h
    push_cast at this; linarith

/-- Two points on a line `PQ` (with `NE P Q`) span a chord of the same slope. -/
lemma slope_eq_of_onLine {P Q a b : Pt} (hPQ : NE P Q) (hab : NE a b) (ha : OnLine P Q a)
    (hb : OnLine P Q b) : slope a b = slope P Q := by
  unfold OnLine at ha hb
  unfold slope
  rw [div_eq_div_iff (sub_pos.2 hab.1).ne' (sub_pos.2 hPQ.1).ne']
  linear_combination ha - hb

/-- 7.6 (chords): for a chord whose line passes through the knot point `hyp (α k)` with a
different arc parameter, the chain preference is strict and `a ≻ b ↔ β' < β k`. -/
theorem chainPref_chord (K : Knots) (k : Fin K.n) {a b : Pt} (ha : a ∈ Tri) (hb : b ∈ Tri)
    (hab : NE a b) (hα : (lineParams a b).1 = K.α k) (hβ : (lineParams a b).2 ≠ K.β k) :
    ¬ Indiff (chainPref K) a b ∧
      (SPref (chainPref K) a b ↔ (lineParams a b).2 < K.β k) := by
  have hR := chainPref_isBtw K
  have hsep : ∀ r ∈ Tri, ∃ G, IsLevelSep (chainUtil K) (chainUtil K r) G :=
    fun _ hr => ⟨_, chainUtil_levelSep K hr⟩
  have hmem := K.α_mem k
  have hband := K.inBand k
  have hband' : band (K.α k, (lineParams a b).2) := by
    have := lineParams_band hab ha hb
    rw [← hα]; exact this
  set α := K.α k
  set β := K.β k
  set β' := (lineParams a b).2
  have hH : hyp α ∈ Tri := hyp_mem_tri hmem.1.le hmem.2.le
  have hHline : OnLine a b (hyp α) := by have := hyp_onLine hab; rwa [hα] at this
  have hHU : chainUtil K (hyp α) = ((k : ℕ) : ℝ) + 1 :=
    chainPref_knot K k hH (by rw [lineFun_hyp]; ring)
  have hslab : slope a b = slope (hyp α) (arc β') := by rw [slope_chord hab ha hb, hα]
  have hcmp1 : β' < β → slope (hyp α) (arc β) < slope a b := fun h => by
    rw [hslab]; exact line_slope_anti_beta hband' hband hmem h
  have hcmp2 : β < β' → slope a b < slope (hyp α) (arc β) := fun h => by
    rw [hslab]; exact line_slope_anti_beta hband hband' hmem h
  have hslne : slope a b ≠ slope (hyp α) (arc β) := by
    rcases lt_or_gt_of_ne hβ with h | h
    · exact (hcmp1 h).ne'
    · exact (hcmp2 h).ne
  have hNEk : NE (hyp α) (arc β) := NE_hyp_arc hband hmem
  have hnot : ¬ Indiff (chainPref K) a b := by
    intro hI
    have he : chainUtil K a = chainUtil K b := le_antisymm hI.2 hI.1
    have hHa := util_eq_of_onLine hsep ha hb hH (ne_of_gt hab.1) hHline he
    have hua : chainUtil K a = ((k : ℕ) : ℝ) + 1 := by rw [← hHa, hHU]
    have hub : chainUtil K b = ((k : ℕ) : ℝ) + 1 := by rw [← he, hua]
    have la := (lineFun_eq_zero_iff _ _ _).1 ((chainUtil_eq_knot_iff K k ha).1 hua)
    have lb := (lineFun_eq_zero_iff _ _ _).1 ((chainUtil_eq_knot_iff K k hb).1 hub)
    exact hslne (slope_eq_of_onLine hNEk hab la lb)
  refine ⟨hnot, ?_⟩
  -- the level slope at `hyp α` is the knot slope
  have hW : hyp α ≠ ((1 : ℝ), (0 : ℝ)) := by
    intro e; have := congrArg Prod.snd e; simp only [hyp] at this; linarith [hmem.1]
  have hB : hyp α ≠ ((0 : ℝ), (1 : ℝ)) := by
    intro e; have := congrArg Prod.snd e; simp only [hyp] at this; linarith [hmem.2]
  have hA : arc β ∈ Tri := by
    obtain ⟨b1, b2⟩ := hband
    simp only at b1 b2
    exact arc_mem_tri (by linarith [hmem.1]) (by linarith [hmem.2])
  have hAU : chainUtil K (arc β) = ((k : ℕ) : ℝ) + 1 :=
    chainPref_knot K k hA (lineFun_arc_self _ _)
  have hAI : Indiff (chainPref K) (arc β) (hyp α) := by
    show chainUtil K (hyp α) ≤ chainUtil K (arc β) ∧ chainUtil K (arc β) ≤ chainUtil K (hyp α)
    rw [hAU, hHU]; exact ⟨le_rfl, le_rfl⟩
  have heq := ((level_is_segment hR hH hW hB).2 (arc β) hA).1 hAI
  have hτ : tau hR (hyp α) = slope (hyp α) (arc β) := by
    unfold slope
    rw [eq_div_iff (sub_pos.2 hNEk.1).ne']
    linarith
  rw [chord_iff_tau hR hH ha hb hab hHline hnot, hτ]
  constructor
  · intro h
    rcases lt_or_gt_of_ne hβ with h' | h'
    · exact h'
    · exact absurd (hcmp2 h') (not_lt.2 h.le)
  · exact hcmp1

/-! ## 7.7 Strictness on `X` -/

/-- 7.7: if every chord of `X` passes through a knot point `hyp (α k)` with arc parameter
`≠ β k`, the chain preference is strict on `X`. -/
theorem chainPref_strictOn (K : Knots) {X : Finset Pt} (hX : (↑X : Set Pt) ⊆ Tri)
    (h : ∀ a b, IsChord X a b →
      ∃ k : Fin K.n, (lineParams a b).1 = K.α k ∧ (lineParams a b).2 ≠ K.β k) :
    StrictOn (chainPref K) X := by
  have hR := chainPref_isBtw K
  intro x hx y hy hxy hI
  rcases tri_cases (hX hx) (hX hy) (Ne.symm hxy) with hc | hc | hc | hc
  · obtain ⟨k, hk1, hk2⟩ := h y x ⟨hy, hx, hc⟩
    exact (chainPref_chord K k (hX hy) (hX hx) hc hk1 hk2).1 ⟨hI.2, hI.1⟩
  · obtain ⟨k, hk1, hk2⟩ := h x y ⟨hx, hy, hc⟩
    exact (chainPref_chord K k (hX hx) (hX hy) hc hk1 hk2).1 hI
  · exact (hR.strictMono x (hX hx) y (hX hy) hc).2 hI.2
  · exact (hR.strictMono y (hX hy) x (hX hx) hc).2 hI.1

/-! ## Concrete tests -/

/-- The empty chain (`n = 0`). -/
def knots0 : Knots where
  n := 0
  α := Fin.elim0
  β := Fin.elim0
  α_mono := fun i => Fin.elim0 i
  β_mono := fun i => Fin.elim0 i
  inBand := fun i => Fin.elim0 i
  α_mem := fun i => Fin.elim0 i

/-- With no knots the chain preference is still a betweenness preference. -/
example : IsBetweennessPref (chainPref knots0) := chainPref_isBtw knots0

/-- One knot at `(α, β) = (1/2, 1/2)`: the knot line is the diagonal `v = u`. -/
noncomputable def knots1 : Knots where
  n := 1
  α := fun _ => 1/2
  β := fun _ => 1/2
  α_mono := fun i j h => absurd h (by simp [Subsingleton.elim i j])
  β_mono := fun i j h => absurd h (by simp [Subsingleton.elim i j])
  inBand := fun _ => by norm_num [band]
  α_mem := fun _ => by norm_num

/-- The chord `a = (1/2, 1/2)`, `b = (1/4, 0)` has parameters `(1/2, 3/8)`: same `α` as the knot,
smaller `β` (steeper than the knot line), so the riskier end `a` is strictly preferred. -/
example : SPref (chainPref knots1) ((1/2 : ℝ), (1/2 : ℝ)) ((1/4 : ℝ), (0 : ℝ)) := by
  have hp : lineParams ((1/2 : ℝ), (1/2 : ℝ)) ((1/4 : ℝ), (0 : ℝ)) = ((1/2 : ℝ), (3/8 : ℝ)) := by
    norm_num [lineParams, lineAlpha, lineBeta, lineU0]
  have h := chainPref_chord knots1 ⟨0, Nat.one_pos⟩ (a := ((1/2 : ℝ), (1/2 : ℝ)))
    (b := ((1/4 : ℝ), (0 : ℝ))) (by norm_num [Tri]) (by norm_num [Tri])
    (by norm_num [NE]) (by rw [hp]; rfl) (by rw [hp]; show (3/8 : ℝ) ≠ 1/2; norm_num)
  rw [h.2, hp]
  show (3/8 : ℝ) < 1/2
  norm_num

/-- The opposite orientation: the chord `a = (1/2, 1/2)`, `b = (0, 1/4)` (parameters
`(1/2, 5/8)`, flatter than the knot line) has `b ≻ a`. -/
example : ¬ SPref (chainPref knots1) ((1/2 : ℝ), (1/2 : ℝ)) ((0 : ℝ), (1/4 : ℝ)) := by
  have hp : lineParams ((1/2 : ℝ), (1/2 : ℝ)) ((0 : ℝ), (1/4 : ℝ)) = ((1/2 : ℝ), (5/8 : ℝ)) := by
    norm_num [lineParams, lineAlpha, lineBeta, lineU0, lineV0]
  have h := chainPref_chord knots1 ⟨0, Nat.one_pos⟩ (a := ((1/2 : ℝ), (1/2 : ℝ)))
    (b := ((0 : ℝ), (1/4 : ℝ))) (by norm_num [Tri]) (by norm_num [Tri])
    (by norm_num [NE]) (by rw [hp]; rfl) (by rw [hp]; show (5/8 : ℝ) ≠ 1/2; norm_num)
  rw [h.2, hp]
  show ¬ (5/8 : ℝ) < 1/2
  norm_num

end REU
