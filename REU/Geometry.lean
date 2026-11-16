/-
# Triangle geometry basics

Mixtures stay in the triangle, FOSD in 3-vector form, incomparability = NE, and the
(hypotenuse, arc) parametrization `lineParams` of the line through a chord.
-/
import REU.Statement

namespace REU

lemma mix_mem_tri {q r : Pt} (hq : q ∈ Tri) (hr : r ∈ Tri) {t : ℝ} (ht0 : 0 ≤ t)
    (ht1 : t ≤ 1) : mix t q r ∈ Tri := by
  obtain ⟨hq1, hq2, hq3⟩ := hq
  obtain ⟨hr1, hr2, hr3⟩ := hr
  have h1t : 0 ≤ 1 - t := by linarith
  simp only [Tri, mix, Set.mem_ofPred_eq, Prod.fst_add, Prod.snd_add, Prod.smul_fst,
    Prod.smul_snd, smul_eq_mul]
  refine ⟨by positivity, by positivity, ?_⟩
  nlinarith [mul_le_mul_of_nonneg_left hq3 ht0, mul_le_mul_of_nonneg_left hr3 h1t]

/-- The 3-coordinate probability vector `(p₁, p₂, p₃) = (u, 1-u-v, v)`. -/
def vec3 (p : Pt) : ℝ × ℝ × ℝ := (p.1, 1 - p.1 - p.2, p.2)

lemma vec3_mix (t : ℝ) (q r : Pt) : vec3 (mix t q r) = t • vec3 q + (1 - t) • vec3 r := by
  ext <;> simp [vec3, mix]
  ring

lemma fosd_iff_vec3 (q r : Pt) :
    FOSD q r ↔ ((vec3 q).1 ≤ (vec3 r).1 ∧
      (vec3 q).1 + (vec3 q).2.1 ≤ (vec3 r).1 + (vec3 r).2.1) := by
  simp only [FOSD, vec3]
  constructor
  · rintro ⟨h1, h2⟩; constructor <;> linarith
  · rintro ⟨h1, h2⟩; constructor <;> linarith

lemma incomparable_iff_NE {a b : Pt} (_ha : a ∈ Tri) (_hb : b ∈ Tri) (_hne : a ≠ b) :
    (¬ FOSD a b ∧ ¬ FOSD b a) ↔ (NE a b ∨ NE b a) := by
  simp only [FOSD, NE, not_and_or, not_le]
  constructor
  · rintro ⟨h1 | h1, h2 | h2⟩
    · exact absurd h1 (not_lt.2 h2.le)
    · exact Or.inl ⟨h1, h2⟩
    · exact Or.inr ⟨h2, h1⟩
    · exact absurd h1 (not_lt.2 h2.le)
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · exact ⟨Or.inl h1, Or.inr h2⟩
    · exact ⟨Or.inr h2, Or.inl h1⟩

lemma slope_pos_of_NE {a b : Pt} (h : NE a b) : 0 < slope a b := by
  exact div_pos (by linarith [h.2]) (by linarith [h.1])

/-- Point of the hypotenuse `u + v = 1` with parameter `α`. -/
def hyp (α : ℝ) : Pt := (1 - α, α)

/-- Point of the arc (bottom edge for `β ≤ 1/2`, left edge for `β ≥ 1/2`). -/
noncomputable def arc (β : ℝ) : Pt := if β ≤ 1/2 then (1 - 2 * β, 0) else (0, 2 * β - 1)

/-- Hypotenuse parameter of the line through `a, b`. -/
noncomputable def lineAlpha (a b : Pt) : ℝ :=
  (a.2 * (a.1 - b.1) + (1 - a.1) * (a.2 - b.2)) / ((a.1 - b.1) + (a.2 - b.2))

/-- `u`-intercept of the line through `a, b`. -/
noncomputable def lineU0 (a b : Pt) : ℝ := a.1 - a.2 * (a.1 - b.1) / (a.2 - b.2)

/-- `v`-intercept of the line through `a, b`. -/
noncomputable def lineV0 (a b : Pt) : ℝ := a.2 - a.1 * (a.2 - b.2) / (a.1 - b.1)

/-- Arc parameter of the line through `a, b`. -/
noncomputable def lineBeta (a b : Pt) : ℝ :=
  if 0 ≤ lineU0 a b then (1 - lineU0 a b) / 2 else (1 + lineV0 a b) / 2

/-- `(α, β)` of the line through `a, b`: it meets the hypotenuse at `hyp α` and the arc at
`arc β`. -/
noncomputable def lineParams (a b : Pt) : ℝ × ℝ := (lineAlpha a b, lineBeta a b)

def band (p : ℝ × ℝ) : Prop := p.1 / 2 < p.2 ∧ p.2 < (1 + p.1) / 2

lemma lineParams_band {a b : Pt} (h : NE a b) (ha : a ∈ Tri) (hb : b ∈ Tri) :
    band (lineParams a b) := by
  obtain ⟨a1, a2⟩ := a
  obtain ⟨b1, b2⟩ := b
  obtain ⟨h1, h2⟩ := h
  obtain ⟨ha1, ha2, ha3⟩ := ha
  obtain ⟨hb1, hb2, hb3⟩ := hb
  simp only at h1 h2 ha1 ha2 ha3 hb1 hb2
  have hdx : 0 < a1 - b1 := by linarith
  have hdy : 0 < a2 - b2 := by linarith
  have hD : 0 < (a1 - b1) + (a2 - b2) := by linarith
  have ha1p : 0 < a1 := by linarith
  have ha2p : 0 < a2 := by linarith
  have hαpos : 0 < lineAlpha (a1, a2) (b1, b2) := by
    unfold lineAlpha
    simp only
    apply div_pos _ hD
    nlinarith [mul_pos ha2p hdx, mul_nonneg (show 0 ≤ 1 - a1 by linarith) hdy.le]
  unfold band lineParams lineBeta
  simp only
  by_cases hu : 0 ≤ lineU0 (a1, a2) (b1, b2)
  · rw [ite_eq_left hu]
    have hm : lineU0 (a1, a2) (b1, b2) + lineAlpha (a1, a2) (b1, b2) < 1 := by
      have e : 1 - lineU0 (a1, a2) (b1, b2) - lineAlpha (a1, a2) (b1, b2) =
          ((1 - a1) * (a2 - b2) * (a1 - b1) + a2 * (a1 - b1) ^ 2) /
            ((a2 - b2) * ((a1 - b1) + (a2 - b2))) := by
        unfold lineU0 lineAlpha; simp only; field_simp; ring
      have : 0 < 1 - lineU0 (a1, a2) (b1, b2) - lineAlpha (a1, a2) (b1, b2) := by
        rw [e]
        apply div_pos _ (mul_pos hdy hD)
        nlinarith [mul_nonneg (mul_nonneg (show 0 ≤ 1 - a1 by linarith) hdy.le) hdx.le,
          mul_pos ha2p (pow_pos hdx 2)]
      linarith
    constructor <;> linarith
  · rw [ite_eq_right hu]
    push Not at hu
    have hm : (a1 * (a2 - b2) - a2 * (a1 - b1)) < 0 := by
      have : a1 - a2 * (a1 - b1) / (a2 - b2) < 0 := hu
      have h3 : a2 * (a1 - b1) / (a2 - b2) > a1 := by linarith
      rw [gt_iff_lt, lt_div_iff₀ hdy] at h3
      linarith
    have hv : (a1 * (a2 - b2) - a2 * (a1 - b1)) * (a2 - b2) < 0 := mul_neg_of_neg_of_pos hm hdy
    constructor
    · have e : 1 + lineV0 (a1, a2) (b1, b2) - lineAlpha (a1, a2) (b1, b2) =
          ((a1 - b1) ^ 2 + a2 * (a1 - b1) * (a2 - b2) - a1 * (a2 - b2) ^ 2) /
            ((a1 - b1) * ((a1 - b1) + (a2 - b2))) := by
        unfold lineV0 lineAlpha; simp only; field_simp; ring
      have : 0 < 1 + lineV0 (a1, a2) (b1, b2) - lineAlpha (a1, a2) (b1, b2) := by
        rw [e]
        apply div_pos _ (mul_pos hdx hD)
        nlinarith [pow_pos hdx 2]
      linarith
    · have e : lineAlpha (a1, a2) (b1, b2) - lineV0 (a1, a2) (b1, b2) =
          ((a1 - b1) * (a2 - b2) * (1 - a2) + a1 * (a2 - b2) ^ 2) /
            ((a1 - b1) * ((a1 - b1) + (a2 - b2))) := by
        unfold lineV0 lineAlpha; simp only; field_simp; ring
      have : 0 < lineAlpha (a1, a2) (b1, b2) - lineV0 (a1, a2) (b1, b2) := by
        rw [e]
        apply div_pos _ (mul_pos hdx hD)
        nlinarith [mul_nonneg (mul_nonneg hdx.le hdy.le) (show 0 ≤ 1 - a2 by linarith),
          mul_pos ha1p (pow_pos hdy 2)]
      linarith

lemma hyp_onLine {a b : Pt} (h : NE a b) : OnLine a b (hyp (lineParams a b).1) := by
  obtain ⟨a1, a2⟩ := a
  obtain ⟨b1, b2⟩ := b
  obtain ⟨h1, h2⟩ := h
  simp only at h1 h2
  have hD : (a1 - b1) + (a2 - b2) ≠ 0 := by linarith
  unfold OnLine hyp lineParams lineAlpha
  simp only
  field_simp
  ring

lemma arc_onLine {a b : Pt} (h : NE a b) (ha : a ∈ Tri) (hb : b ∈ Tri) :
    OnLine a b (arc (lineParams a b).2) := by
  obtain ⟨a1, a2⟩ := a
  obtain ⟨b1, b2⟩ := b
  obtain ⟨h1, h2⟩ := h
  obtain ⟨ha1, ha2, ha3⟩ := ha
  obtain ⟨hb1, hb2, hb3⟩ := hb
  simp only at h1 h2 ha1 ha2 ha3 hb1 hb2
  have hdx : 0 < a1 - b1 := by linarith
  have hdy : 0 < a2 - b2 := by linarith
  unfold lineParams lineBeta
  simp only
  by_cases hu : 0 ≤ lineU0 (a1, a2) (b1, b2)
  · rw [ite_eq_left hu]
    have hle : (1 - lineU0 (a1, a2) (b1, b2)) / 2 ≤ 1 / 2 := by linarith
    unfold arc
    rw [ite_eq_left hle]
    have e : 1 - 2 * ((1 - lineU0 (a1, a2) (b1, b2)) / 2) = lineU0 (a1, a2) (b1, b2) := by ring
    rw [e]
    unfold OnLine lineU0
    simp only
    field_simp
    ring
  · rw [ite_eq_right hu]
    push Not at hu
    have hv : 0 < lineV0 (a1, a2) (b1, b2) := by
      have h3 : a2 * (a1 - b1) / (a2 - b2) > a1 := by
        have : a1 - a2 * (a1 - b1) / (a2 - b2) < 0 := hu
        linarith
      rw [gt_iff_lt, lt_div_iff₀ hdy] at h3
      unfold lineV0; simp only
      have : a1 * (a2 - b2) / (a1 - b1) < a2 := by
        rw [div_lt_iff₀ hdx]; linarith
      linarith
    have hnle : ¬ ((1 + lineV0 (a1, a2) (b1, b2)) / 2 ≤ 1 / 2) := by
      intro h; linarith
    unfold arc
    rw [ite_eq_right hnle]
    have e : 2 * ((1 + lineV0 (a1, a2) (b1, b2)) / 2) - 1 = lineV0 (a1, a2) (b1, b2) := by ring
    rw [e]
    unfold OnLine lineV0
    simp only
    field_simp
    ring

end REU
