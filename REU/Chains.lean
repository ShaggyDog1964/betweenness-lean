/-
# Line chains and up-set realization

For `(α, β)` in the band with `α ∈ (0,1)`, `ℓ(α,β)` is the line through `hyp α` and `arc β`.
`lineFun α β` is an affine functional vanishing exactly on `ℓ(α,β)`, positive toward the best
vertex `B = (0,1)` and negative at the worst vertex `W = (1,0)`. Key facts:
* `line_slope`: `ℓ(α,β)` has positive slope, strictly decreasing in `β`, increasing in `α`;
* `nested`: if `α < α'` and `β < β'`, then on `Tri` the closed `B`-side of `ℓ(α',β')` lies in
  the open `B`-side of `ℓ(α,β)` (also for the end functionals `LW`, `LB`);
* chord lines: for a chord `(a,b)`, `lineFun (lineParams a b)` vanishes exactly on line `ab`;
* `cross_of_SE`: chord lines whose parameters are SE-ordered meet in `Tri`, the second steeper;
* `realize_upset`: a consistent finite up/down constraint set is realized by a strictly
  increasing knot chain (`Knots`) in the band.
-/
import REU.Utility

namespace REU

open Set

/-! ## The line functional -/

/-- `x`-component of the direction `hyp α - arc β` of `ℓ(α,β)`. -/
noncomputable def dirX (α β : ℝ) : ℝ := if β ≤ 1/2 then 2 * β - α else 1 - α

/-- `y`-component of the direction `hyp α - arc β` of `ℓ(α,β)`. -/
noncomputable def dirY (α β : ℝ) : ℝ := if β ≤ 1/2 then α else 1 + α - 2 * β

/-- Affine functional of `ℓ(α,β)`: zero exactly on the line, positive toward `B = (0,1)`. -/
noncomputable def lineFun (α β : ℝ) (q : Pt) : ℝ :=
  dirX α β * (q.2 - α) - dirY α β * (q.1 - (1 - α))

/-- End functional at `W = (1,0)`: on `Tri`, zero only at `W`, positive elsewhere. -/
def LW (q : Pt) : ℝ := 1 - q.1 + q.2

/-- End functional at `B = (0,1)`: on `Tri`, zero only at `B`, negative elsewhere. -/
def LB (q : Pt) : ℝ := q.2 - q.1 - 1

lemma dirX_pos {α β : ℝ} (hb : band (α, β)) (hα : α ∈ Ioo (0 : ℝ) 1) : 0 < dirX α β := by
  unfold dirX
  obtain ⟨h1, h2⟩ := hb
  obtain ⟨h3, h4⟩ := hα
  simp only at h1 h2
  split_ifs <;> linarith

lemma dirY_pos {α β : ℝ} (hb : band (α, β)) (hα : α ∈ Ioo (0 : ℝ) 1) : 0 < dirY α β := by
  unfold dirY
  obtain ⟨h1, h2⟩ := hb
  obtain ⟨h3, h4⟩ := hα
  simp only at h1 h2
  split_ifs <;> linarith

lemma arc_eq (α β : ℝ) : arc β = (1 - α - dirX α β, α - dirY α β) := by
  unfold arc dirX dirY
  split_ifs <;> ext <;> simp only <;> ring

/-- `lineFun α β q` is the `OnLine` cross product of `hyp α`, `arc β`, `q`. -/
lemma lineFun_eq_cross (α β : ℝ) (q : Pt) :
    lineFun α β q = (q.1 - (hyp α).1) * ((arc β).2 - (hyp α).2)
      - (q.2 - (hyp α).2) * ((arc β).1 - (hyp α).1) := by
  rw [arc_eq α β]
  simp only [lineFun, hyp]
  ring

lemma lineFun_eq_zero_iff (α β : ℝ) (q : Pt) : lineFun α β q = 0 ↔ OnLine (hyp α) (arc β) q :=
  by rw [lineFun_eq_cross]; rfl

lemma lineFun_mix (α β t : ℝ) (q r : Pt) :
    lineFun α β (mix t q r) = t * lineFun α β q + (1 - t) * lineFun α β r := by
  simp only [lineFun, mix_fst, mix_snd]
  ring

lemma continuous_lineFun (α β : ℝ) : Continuous (lineFun α β) := by
  unfold lineFun
  fun_prop

lemma lineFun_hyp (α β α' : ℝ) : lineFun α β (hyp α') = (α' - α) * (dirX α β + dirY α β) := by
  simp only [lineFun, hyp]
  ring

lemma lineFun_W_neg {α β : ℝ} (hb : band (α, β)) (hα : α ∈ Ioo (0 : ℝ) 1) :
    lineFun α β ((1 : ℝ), (0 : ℝ)) < 0 := by
  have e := lineFun_hyp α β 0
  rw [hyp_zero] at e
  rw [e]
  have := dirX_pos hb hα
  have := dirY_pos hb hα
  nlinarith [hα.1]

lemma lineFun_B_pos {α β : ℝ} (hb : band (α, β)) (hα : α ∈ Ioo (0 : ℝ) 1) :
    0 < lineFun α β ((0 : ℝ), (1 : ℝ)) := by
  have e := lineFun_hyp α β 1
  rw [hyp_one] at e
  rw [e]
  have := dirX_pos hb hα
  have := dirY_pos hb hα
  nlinarith [hα.2]

lemma lineFun_arc_self (α β : ℝ) : lineFun α β (arc β) = 0 := by
  rw [lineFun_eq_zero_iff]
  unfold OnLine
  ring

lemma lineFun_arc_neg {α β β' : ℝ} (hb : band (α, β)) (hα : α ∈ Ioo (0 : ℝ) 1) (h : β' < β) :
    lineFun α β (arc β') < 0 := by
  obtain ⟨h1, h2⟩ := hb
  obtain ⟨h3, h4⟩ := hα
  simp only at h1 h2
  unfold lineFun dirX dirY arc
  split_ifs with hβ' hβ hβ <;> simp only <;> nlinarith

lemma lineFun_arc_pos {α β β' : ℝ} (hb : band (α, β)) (hα : α ∈ Ioo (0 : ℝ) 1) (h : β < β') :
    0 < lineFun α β (arc β') := by
  obtain ⟨h1, h2⟩ := hb
  obtain ⟨h3, h4⟩ := hα
  simp only at h1 h2
  unfold lineFun dirX dirY arc
  split_ifs with hβ' hβ hβ <;> simp only <;> nlinarith

/-- Strict FOSD strictly increases `lineFun` (normal `(-dirY, dirX)` has positive entries). -/
lemma lineFun_lt_of_strictFOSD {α β : ℝ} (hb : band (α, β)) (hα : α ∈ Ioo (0 : ℝ) 1)
    {q r : Pt} (h : StrictFOSD q r) : lineFun α β r < lineFun α β q := by
  obtain ⟨⟨h1, h2⟩, hne⟩ := h
  have hx := dirX_pos hb hα
  have hy := dirY_pos hb hα
  have key : lineFun α β q - lineFun α β r = dirX α β * (q.2 - r.2) + dirY α β * (r.1 - q.1) := by
    simp only [lineFun]; ring
  rcases h1.lt_or_eq with h1 | h1
  · nlinarith [mul_nonneg hx.le (sub_nonneg.2 h2), mul_pos hy (sub_pos.2 h1)]
  · rcases h2.lt_or_eq with h2 | h2
    · nlinarith [mul_pos hx (sub_pos.2 h2)]
    · exact absurd (Prod.ext h1 h2.symm) hne

lemma LW_lt_of_strictFOSD {q r : Pt} (h : StrictFOSD q r) : LW r < LW q := by
  obtain ⟨⟨h1, h2⟩, hne⟩ := h
  unfold LW
  rcases h1.lt_or_eq with h1 | h1
  · linarith
  · rcases h2.lt_or_eq with h2 | h2
    · linarith
    · exact absurd (Prod.ext h1 h2.symm) hne

lemma LB_lt_of_strictFOSD {q r : Pt} (h : StrictFOSD q r) : LB r < LB q := by
  obtain ⟨⟨h1, h2⟩, hne⟩ := h
  unfold LB
  rcases h1.lt_or_eq with h1 | h1
  · linarith
  · rcases h2.lt_or_eq with h2 | h2
    · linarith
    · exact absurd (Prod.ext h1 h2.symm) hne

lemma LW_mix (t : ℝ) (q r : Pt) : LW (mix t q r) = t * LW q + (1 - t) * LW r := by
  simp only [LW, mix_fst, mix_snd]; ring

lemma LB_mix (t : ℝ) (q r : Pt) : LB (mix t q r) = t * LB q + (1 - t) * LB r := by
  simp only [LB, mix_fst, mix_snd]; ring

lemma continuous_LW : Continuous LW := by
  unfold LW; fun_prop

lemma continuous_LB : Continuous LB := by
  unfold LB; fun_prop

lemma LW_nonneg {q : Pt} (hq : q ∈ Tri) : 0 ≤ LW q := by
  obtain ⟨h1, h2, h3⟩ := hq
  unfold LW; linarith

lemma LB_nonpos {q : Pt} (hq : q ∈ Tri) : LB q ≤ 0 := by
  obtain ⟨h1, h2, h3⟩ := hq
  unfold LB; linarith

/-! ## 6.1 Slopes -/

lemma arc_mem_tri {β : ℝ} (h0 : 0 ≤ β) (h1 : β ≤ 1) : arc β ∈ Tri := by
  unfold arc Tri
  split_ifs <;> simp only [Set.mem_ofPred_eq] <;> refine ⟨?_, ?_, ?_⟩ <;> linarith

lemma NE_hyp_arc {α β : ℝ} (hb : band (α, β)) (hα : α ∈ Ioo (0 : ℝ) 1) :
    NE (hyp α) (arc β) := by
  have hx := dirX_pos hb hα
  have hy := dirY_pos hb hα
  rw [arc_eq α β]
  simp only [NE, hyp]
  constructor <;> linarith

lemma slope_hyp_arc (α β : ℝ) : slope (hyp α) (arc β) = dirY α β / dirX α β := by
  rw [arc_eq α β]
  simp only [slope, hyp]
  congr 1 <;> ring

/-- 6.1: the slope of `ℓ(α,β)` is positive, strictly decreasing in `β` and strictly
increasing in `α` (within the band). -/
theorem line_slope_pos {α β : ℝ} (hb : band (α, β)) (hα : α ∈ Ioo (0 : ℝ) 1) :
    0 < slope (hyp α) (arc β) := by
  rw [slope_hyp_arc]
  exact div_pos (dirY_pos hb hα) (dirX_pos hb hα)

theorem line_slope_anti_beta {α β β' : ℝ} (hb : band (α, β)) (hb' : band (α, β'))
    (hα : α ∈ Ioo (0 : ℝ) 1) (h : β < β') : slope (hyp α) (arc β') < slope (hyp α) (arc β) := by
  have hx := dirX_pos hb hα
  have hx' := dirX_pos hb' hα
  rw [slope_hyp_arc, slope_hyp_arc, div_lt_div_iff₀ hx' hx]
  obtain ⟨h1, h2⟩ := hb
  obtain ⟨h1', h2'⟩ := hb'
  obtain ⟨h3, h4⟩ := hα
  simp only at h1 h2 h1' h2'
  unfold dirX dirY at *
  split_ifs at * with hβ' hβ hβ <;> nlinarith

theorem line_slope_mono_alpha {α α' β : ℝ} (hb : band (α, β)) (hb' : band (α', β))
    (hα : α ∈ Ioo (0 : ℝ) 1) (hα' : α' ∈ Ioo (0 : ℝ) 1) (h : α < α') :
    slope (hyp α) (arc β) < slope (hyp α') (arc β) := by
  have hx := dirX_pos hb hα
  have hx' := dirX_pos hb' hα'
  rw [slope_hyp_arc, slope_hyp_arc, div_lt_div_iff₀ hx hx']
  obtain ⟨h1, h2⟩ := hb
  obtain ⟨h1', h2'⟩ := hb'
  obtain ⟨h3, h4⟩ := hα
  obtain ⟨h3', h4'⟩ := hα'
  simp only at h1 h2 h1' h2'
  unfold dirX dirY at *
  split_ifs at * with hβ <;> nlinarith

/-! ## 6.2 Nesting -/

/-- Certificate step: `X·L = Y·L' + c₁u + c₂v` with `L' ≥ 0`, nonnegative terms, one strictly
positive, gives `L > 0`. -/
lemma pos_of_cert {L L' X Y c₁ c₂ u v : ℝ} (hX : 0 < X) (hY : 0 ≤ Y) (hL' : 0 ≤ L')
    (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) (hu : 0 ≤ u) (hv : 0 ≤ v) (huv : 0 < u ∨ 0 < v)
    (h : X * L = Y * L' + c₁ * u + c₂ * v) : 0 < L := by
  have h1 := mul_nonneg hY hL'
  have : 0 < X * L := by
    rw [h]
    rcases huv with hu' | hv'
    · have := mul_pos hc₁ hu'; have := mul_nonneg hc₂.le hv; linarith
    · have := mul_nonneg hc₁.le hu; have := mul_pos hc₂ hv'; linarith
  exact pos_of_mul_pos_right this hX.le

/-- 6.2: for `α < α'`, `β < β'`, on `Tri` the closed `B`-side of `ℓ(α',β')` is inside the open
`B`-side of `ℓ(α,β)`. -/
theorem nested {α β α' β' : ℝ} (hb : band (α, β)) (hα : α ∈ Ioo (0 : ℝ) 1)
    (hb' : band (α', β')) (hα' : α' ∈ Ioo (0 : ℝ) 1) (hlt : α < α') (hlt' : β < β')
    {q : Pt} (hq : q ∈ Tri) (hL : 0 ≤ lineFun α' β' q) : 0 < lineFun α β q := by
  obtain ⟨q1, q2⟩ := q
  obtain ⟨hq1, hq2, hq3⟩ := hq
  obtain ⟨h1, h2⟩ := hb
  obtain ⟨h1', h2'⟩ := hb'
  obtain ⟨h3, h4⟩ := hα
  obtain ⟨h3', h4'⟩ := hα'
  simp only at h1 h2 h1' h2' hq1 hq2 hq3
  unfold lineFun dirX dirY at *
  simp only at hL ⊢
  by_cases hβ' : β' ≤ 1/2
  · have hβ : β ≤ 1/2 := by linarith
    simp only [hβ, hβ', ↓reduceIte] at hL ⊢
    have key : (α' * β') * ((2 * β - α) * (q2 - α) - α * (q1 - (1 - α))) =
        (α * β) * ((2 * β' - α') * (q2 - α') - α' * (q1 - (1 - α'))) +
        (α * α' * (β' - β)) * (1 - q1 - q2) + (2 * β * β' * (α' - α)) * q2 := by ring
    by_cases hu : 0 < 1 - q1 - q2
    · exact pos_of_cert (mul_pos h3' (by linarith)) (mul_nonneg h3.le (by linarith)) hL (by nlinarith [mul_pos h3 h3'])
        (by nlinarith [mul_pos (show 0 < β by linarith) (show 0 < β' by linarith)])
        hu.le hq2 (Or.inl hu) key
    by_cases hv : 0 < q2
    · exact pos_of_cert (by nlinarith) (by nlinarith) hL (by nlinarith [mul_pos h3 h3'])
        (by nlinarith [mul_pos (show 0 < β by linarith) (show 0 < β' by linarith)])
        (by linarith) hq2 (Or.inr hv) key
    exfalso
    have e2 : q2 = 0 := by linarith
    have e1 : q1 = 1 := by linarith
    subst e2 e1
    nlinarith
  · have hβ'' : 1/2 < β' := lt_of_not_ge hβ'
    simp only [hβ', ↓reduceIte] at hL
    by_cases hβ : β ≤ 1/2
    · simp only [hβ, ↓reduceIte]
      have key : ((1 - α') * (2 - 2 * β')) * ((2 * β - α) * (q2 - α) - α * (q1 - (1 - α))) =
          ((1 - α) * (2 * β)) * ((1 - α') * (q2 - α') - (1 + α' - 2 * β') * (q1 - (1 - α'))) +
          (2 * β * (2 - 2 * β') * (α' - α)) * q1 +
          ((1 - α') * (α * (2 - 2 * β') * (1 - 2 * β) + 2 * β * (1 - α) * (2 * β' - 1))) *
            (1 - q1 - q2) := by ring
      have hc₂ : 0 < (1 - α') * (α * (2 - 2 * β') * (1 - 2 * β) + 2 * β * (1 - α) * (2 * β' - 1)) := by
        apply mul_pos (by linarith)
        have : 0 ≤ α * (2 - 2 * β') * (1 - 2 * β) :=
          mul_nonneg (mul_nonneg h3.le (by linarith)) (by linarith)
        have : 0 < 2 * β * (1 - α) * (2 * β' - 1) :=
          mul_pos (mul_pos (by linarith) (by linarith)) (by linarith)
        linarith
      have hc₁ : 0 < 2 * β * (2 - 2 * β') * (α' - α) :=
        mul_pos (mul_pos (by linarith) (by linarith)) (by linarith)
      by_cases hu : 0 < q1
      · exact pos_of_cert (mul_pos (by linarith) (by linarith))
          (mul_nonneg (by linarith) (by linarith)) hL hc₁ hc₂ hq1 (by linarith) (Or.inl hu) key
      by_cases hv : 0 < 1 - q1 - q2
      · exact pos_of_cert (mul_pos (by linarith) (by linarith))
          (mul_nonneg (by linarith) (by linarith)) hL hc₁ hc₂ hq1 hv.le (Or.inr hv) key
      have e1 : q1 = 0 := by linarith
      have e2 : q2 = 1 := by linarith
      subst e1 e2
      nlinarith
    · have hβ2 : 1/2 < β := lt_of_not_ge hβ
      simp only [hβ, ↓reduceIte]
      have key : ((1 - α') * (2 - 2 * β')) *
            ((1 - α) * (q2 - α) - (1 + α - 2 * β) * (q1 - (1 - α))) =
          ((1 - α) * (2 - 2 * β)) * ((1 - α') * (q2 - α') - (1 + α' - 2 * β') * (q1 - (1 - α'))) +
          ((2 - 2 * β) * (2 - 2 * β') * (α' - α)) * q1 +
          (2 * (1 - α) * (1 - α') * (β' - β)) * (1 - q1 - q2) := by ring
      have hc₁ : 0 < (2 - 2 * β) * (2 - 2 * β') * (α' - α) :=
        mul_pos (mul_pos (by linarith) (by linarith)) (by linarith)
      have hc₂ : 0 < 2 * (1 - α) * (1 - α') * (β' - β) :=
        mul_pos (mul_pos (mul_pos (by norm_num) (by linarith)) (by linarith)) (by linarith)
      by_cases hu : 0 < q1
      · exact pos_of_cert (mul_pos (by linarith) (by linarith))
          (mul_nonneg (by linarith) (by linarith)) hL hc₁ hc₂ hq1 (by linarith) (Or.inl hu) key
      by_cases hv : 0 < 1 - q1 - q2
      · exact pos_of_cert (mul_pos (by linarith) (by linarith))
          (mul_nonneg (by linarith) (by linarith)) hL hc₁ hc₂ hq1 hv.le (Or.inr hv) key
      have e1 : q1 = 0 := by linarith
      have e2 : q2 = 1 := by linarith
      subst e1 e2
      nlinarith

theorem nested_W {α β : ℝ} (hb : band (α, β)) (hα : α ∈ Ioo (0 : ℝ) 1) {q : Pt} (hq : q ∈ Tri)
    (hL : 0 ≤ lineFun α β q) : 0 < LW q := by
  obtain ⟨q1, q2⟩ := q
  obtain ⟨hq1, hq2, hq3⟩ := hq
  simp only at hq1 hq2 hq3
  unfold LW
  simp only
  by_contra hcon
  have e2 : q2 = 0 := by linarith
  have e1 : q1 = 1 := by linarith
  subst e1 e2
  linarith [lineFun_W_neg hb hα]

theorem nested_B {α β : ℝ} (hb : band (α, β)) (hα : α ∈ Ioo (0 : ℝ) 1) {q : Pt} (hq : q ∈ Tri)
    (hL : 0 ≤ LB q) : 0 < lineFun α β q := by
  obtain ⟨q1, q2⟩ := q
  obtain ⟨hq1, hq2, hq3⟩ := hq
  simp only at hq1 hq2 hq3
  unfold LB at hL
  simp only at hL
  have e1 : q1 = 0 := by linarith
  have e2 : q2 = 1 := by linarith
  subst e1 e2
  exact lineFun_B_pos hb hα

theorem nested_WB {q : Pt} (hq : q ∈ Tri) (hL : 0 ≤ LB q) : 0 < LW q := by
  obtain ⟨hq1, hq2, hq3⟩ := hq
  unfold LB at hL
  unfold LW
  linarith

/-! ## Chord lines are lines `ℓ(α,β)` -/

lemma lineAlpha_mem {a b : Pt} (h : NE a b) (ha : a ∈ Tri) (hb : b ∈ Tri) :
    (lineParams a b).1 ∈ Ioo (0 : ℝ) 1 := by
  obtain ⟨a1, a2⟩ := a
  obtain ⟨b1, b2⟩ := b
  obtain ⟨h1, h2⟩ := h
  obtain ⟨ha1, ha2, ha3⟩ := ha
  obtain ⟨hb1, hb2, hb3⟩ := hb
  simp only at h1 h2 ha1 ha2 ha3 hb1 hb2 hb3
  have hdx : 0 < a1 - b1 := by linarith
  have hdy : 0 < a2 - b2 := by linarith
  have hD : 0 < (a1 - b1) + (a2 - b2) := by linarith
  unfold lineParams lineAlpha
  simp only
  constructor
  · apply div_pos _ hD
    nlinarith [mul_pos (show 0 < a2 by linarith) hdx, mul_nonneg (show 0 ≤ 1 - a1 by linarith) hdy.le]
  · rw [div_lt_one hD]
    nlinarith [mul_pos (show 0 < a1 by linarith) hdy, mul_nonneg (show 0 ≤ 1 - a2 by linarith) hdx.le]

/-- Cross-product transfer: if `H`, `A` lie on line `ab`, the cross product w.r.t. `H, A` is
a multiple of the one w.r.t. `a, b`. -/
lemma cross_transfer {a b H A y : Pt} (hH : OnLine a b H) (hA : OnLine a b A) :
    (a.1 - b.1) * ((y.1 - H.1) * (A.2 - H.2) - (y.2 - H.2) * (A.1 - H.1)) =
      (H.1 - A.1) * ((y.1 - a.1) * (b.2 - a.2) - (y.2 - a.2) * (b.1 - a.1)) := by
  unfold OnLine at hH hA
  linear_combination (y.1 - H.1) * hA + (A.1 - y.1) * hH

/-- For a chord `(a,b)`: `lineFun` of its parameters is a positive multiple of the `OnLine`
cross product of `a, b`. -/
theorem lineFun_chord {a b : Pt} (h : NE a b) (ha : a ∈ Tri) (hb : b ∈ Tri) (y : Pt) :
    (a.1 - b.1) * lineFun (lineParams a b).1 (lineParams a b).2 y =
      dirX (lineParams a b).1 (lineParams a b).2 *
        ((y.1 - a.1) * (b.2 - a.2) - (y.2 - a.2) * (b.1 - a.1)) := by
  rw [lineFun_eq_cross, cross_transfer (y := y) (hyp_onLine h) (arc_onLine h ha hb)]
  congr 1
  rw [arc_eq (lineParams a b).1 (lineParams a b).2]
  simp only [hyp]
  ring

/-- For a chord `(a,b)`, `ℓ(lineParams a b)` is the line `ab`. -/
theorem lineFun_chord_eq_zero_iff {a b : Pt} (h : NE a b) (ha : a ∈ Tri) (hb : b ∈ Tri)
    (y : Pt) : lineFun (lineParams a b).1 (lineParams a b).2 y = 0 ↔ OnLine a b y := by
  have hx := dirX_pos (lineParams_band h ha hb) (lineAlpha_mem h ha hb)
  have hd : a.1 - b.1 ≠ 0 := by linarith [h.1]
  have key := lineFun_chord h ha hb y
  unfold OnLine
  constructor
  · intro h0
    rw [h0, mul_zero] at key
    exact (mul_eq_zero.1 key.symm).resolve_left hx.ne'
  · intro h0
    rw [h0, mul_zero] at key
    exact (mul_eq_zero.1 key).resolve_left hd

/-- The chord's slope is the slope of `ℓ(lineParams a b)`. -/
theorem slope_chord {a b : Pt} (h : NE a b) (ha : a ∈ Tri) (hb : b ∈ Tri) :
    slope a b = slope (hyp (lineParams a b).1) (arc (lineParams a b).2) := by
  have hNE : NE (hyp (lineParams a b).1) (arc (lineParams a b).2) :=
    NE_hyp_arc (lineParams_band h ha hb) (lineAlpha_mem h ha hb)
  have hH := hyp_onLine h
  have hA := arc_onLine h ha hb
  unfold OnLine at hH hA
  unfold slope
  rw [div_eq_div_iff (by linarith [h.1]) (by linarith [hNE.1])]
  linear_combination hA - hH

/-! ## 6.3 Crossing of SE-ordered chord lines -/

lemma onLine_mix {c d p r : Pt} (hp : OnLine c d p) (hr : OnLine c d r) (t : ℝ) :
    OnLine c d (mix t p r) := by
  unfold OnLine at *
  simp only [mix_fst, mix_snd]
  linear_combination t * hp + (1 - t) * hr

/-- Equal parameters: the chords are collinear. -/
theorem collinear4_of_lineParams_eq {a b c d : Pt} (hab : NE a b) (ha : a ∈ Tri) (hb : b ∈ Tri)
    (hcd : NE c d) (hc : c ∈ Tri) (hd : d ∈ Tri) (h : lineParams a b = lineParams c d) :
    collinear4 a b c d := by
  have onc : OnLine c d c := by unfold OnLine; ring
  have ond : OnLine c d d := by unfold OnLine; ring
  refine ⟨(lineFun_chord_eq_zero_iff hab ha hb c).1 ?_, (lineFun_chord_eq_zero_iff hab ha hb d).1 ?_⟩
  · rw [h]; exact (lineFun_chord_eq_zero_iff hcd hc hd c).2 onc
  · rw [h]; exact (lineFun_chord_eq_zero_iff hcd hc hd d).2 ond

/-- 6.3: if `c₁ = lineParams a b` and `c₂ = lineParams c d` satisfy `α₁ ≤ α₂`, `β₂ ≤ β₁`,
`c₁ ≠ c₂`, then the chord lines meet in `Tri` and `cd` is strictly steeper. -/
theorem cross_of_SE {a b c d : Pt} (hab : NE a b) (ha : a ∈ Tri) (hb : b ∈ Tri)
    (hcd : NE c d) (hc : c ∈ Tri) (hd : d ∈ Tri)
    (hα : (lineParams a b).1 ≤ (lineParams c d).1) (hβ : (lineParams c d).2 ≤ (lineParams a b).2)
    (hne : lineParams a b ≠ lineParams c d) :
    linesMeetInTri a b c d ∧ slope a b < slope c d := by
  have hb₁ := lineParams_band hab ha hb
  have hb₂ := lineParams_band hcd hc hd
  have hm₁ := lineAlpha_mem hab ha hb
  have hm₂ := lineAlpha_mem hcd hc hd
  set α₁ := (lineParams a b).1 with hα₁
  set β₁ := (lineParams a b).2 with hβ₁
  set α₂ := (lineParams c d).1 with hα₂
  set β₂ := (lineParams c d).2 with hβ₂
  have hb₁' : band (α₁, β₁) := hb₁
  have hb₂' : band (α₂, β₂) := hb₂
  have hb₁₂ : band (α₁, β₂) := by
    obtain ⟨h1, h2⟩ := hb₁'
    obtain ⟨h1', h2'⟩ := hb₂'
    simp only at h1 h2 h1' h2'
    constructor <;> simp only <;> linarith
  constructor
  · -- the meeting point on segment `hyp α₂ – arc β₂`
    set P := lineFun α₁ β₁ (hyp α₂) with hP
    set N := lineFun α₁ β₁ (arc β₂) with hN
    have hP0 : 0 ≤ P := by
      rw [hP, lineFun_hyp]
      exact mul_nonneg (by linarith) (add_pos (dirX_pos hb₁' hm₁) (dirY_pos hb₁' hm₁)).le
    have hN0 : N ≤ 0 := by
      rcases hβ.lt_or_eq with hlt | heq
      · exact (lineFun_arc_neg hb₁' hm₁ hlt).le
      · rw [hN, heq, lineFun_arc_self]
    obtain ⟨t, ht0, ht1, ht⟩ : ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ t * P + (1 - t) * N = 0 := by
      by_cases hNP : N < P
      · refine ⟨-N / (P - N), div_nonneg (by linarith) (by linarith),
          (div_le_one (by linarith)).2 (by linarith), ?_⟩
        field_simp
        ring
      · exact ⟨1, zero_le_one, le_rfl, by linarith⟩
    obtain ⟨h1, h2⟩ := hb₂'
    simp only at h1 h2
    refine ⟨mix t (hyp α₂) (arc β₂),
      mix_mem_tri (hyp_mem_tri hm₂.1.le hm₂.2.le)
        (arc_mem_tri (by linarith [hm₂.1]) (by linarith [hm₂.2])) ht0 ht1, ?_,
      onLine_mix (hyp_onLine hcd) (arc_onLine hcd hc hd) t⟩
    refine (lineFun_chord_eq_zero_iff hab ha hb _).1 ?_
    rw [lineFun_mix]
    exact ht
  · rw [slope_chord hab ha hb, slope_chord hcd hc hd, ← hα₁, ← hβ₁, ← hα₂, ← hβ₂]
    rcases hα.lt_or_eq with hlt | heq
    · have s2 := line_slope_mono_alpha hb₁₂ hb₂' hm₁ hm₂ hlt
      rcases hβ.lt_or_eq with hβlt | hβeq
      · exact (line_slope_anti_beta hb₁₂ hb₁' hm₁ hβlt).trans s2
      · rw [← hβeq]; exact s2
    · have hβlt : β₂ < β₁ := by
        rcases hβ.lt_or_eq with hβlt | hβeq
        · exact hβlt
        · exact absurd (Prod.ext heq hβeq.symm) hne
      rw [← heq]
      exact line_slope_anti_beta hb₁₂ hb₁' hm₁ hβlt

/-! ## 6.4 Knots -/

/-- A strictly increasing chain of knots `(α k, β k)` in the band. -/
structure Knots where
  n : ℕ
  α : Fin n → ℝ
  β : Fin n → ℝ
  α_mono : StrictMono α
  β_mono : StrictMono β
  inBand : ∀ k, band (α k, β k)
  α_mem : ∀ k, α k ∈ Ioo (0 : ℝ) 1

/-! ## 6.5 Up-set realization -/

/-- Lower bound for the knot at `x`: `max (x/2, max {c.β : c ∈ Up, c.α ≤ x})`. -/
noncomputable def lbF (Up : Finset (ℝ × ℝ)) (x : ℝ) : ℝ :=
  (insert (x / 2) ((Up.filter (fun c => c.1 ≤ x)).image Prod.snd)).max'
    (Finset.insert_nonempty _ _)

/-- Upper bound for the knot at `x`: `min ((1+x)/2, min {c.β : c ∈ Dn, x ≤ c.α})`. -/
noncomputable def ubF (Dn : Finset (ℝ × ℝ)) (x : ℝ) : ℝ :=
  (insert ((1 + x) / 2) ((Dn.filter (fun c => x ≤ c.1)).image Prod.snd)).min'
    (Finset.insert_nonempty _ _)

lemma le_lbF_self (Up : Finset (ℝ × ℝ)) (x : ℝ) : x / 2 ≤ lbF Up x :=
  Finset.le_max' _ _ (Finset.mem_insert_self _ _)

lemma le_lbF {Up : Finset (ℝ × ℝ)} {x : ℝ} {c : ℝ × ℝ} (hc : c ∈ Up) (h : c.1 ≤ x) :
    c.2 ≤ lbF Up x :=
  Finset.le_max' _ _
    (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ (Finset.mem_filter.2 ⟨hc, h⟩)))

lemma ubF_le_self (Dn : Finset (ℝ × ℝ)) (x : ℝ) : ubF Dn x ≤ (1 + x) / 2 :=
  Finset.min'_le _ _ (Finset.mem_insert_self _ _)

lemma ubF_le {Dn : Finset (ℝ × ℝ)} {x : ℝ} {c : ℝ × ℝ} (hc : c ∈ Dn) (h : x ≤ c.1) :
    ubF Dn x ≤ c.2 :=
  Finset.min'_le _ _
    (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ (Finset.mem_filter.2 ⟨hc, h⟩)))

lemma lbF_mono (Up : Finset (ℝ × ℝ)) {x y : ℝ} (hxy : x ≤ y) : lbF Up x ≤ lbF Up y := by
  refine Finset.max'_le _ _ _ fun z hz => ?_
  rcases Finset.mem_insert.1 hz with rfl | hz
  · linarith [le_lbF_self Up y]
  · obtain ⟨c, hc, rfl⟩ := Finset.mem_image.1 hz
    obtain ⟨hc, hcx⟩ := Finset.mem_filter.1 hc
    exact le_lbF hc (hcx.trans hxy)

lemma ubF_mono (Dn : Finset (ℝ × ℝ)) {x y : ℝ} (hxy : x ≤ y) : ubF Dn x ≤ ubF Dn y := by
  refine Finset.le_min' _ _ _ fun z hz => ?_
  rcases Finset.mem_insert.1 hz with rfl | hz
  · linarith [ubF_le_self Dn x]
  · obtain ⟨c, hc, rfl⟩ := Finset.mem_image.1 hz
    obtain ⟨hc, hcx⟩ := Finset.mem_filter.1 hc
    exact ubF_le hc (hxy.trans hcx)

lemma lbF_lt_ubF {Up Dn : Finset (ℝ × ℝ)} (hP : ∀ c ∈ Up ∪ Dn, band c ∧ c.1 ∈ Ioo (0 : ℝ) 1)
    (hcons : ¬ ∃ c₁ ∈ Up, ∃ c₂ ∈ Dn, c₁.1 ≤ c₂.1 ∧ c₂.2 ≤ c₁.2) (x : ℝ) :
    lbF Up x < ubF Dn x := by
  refine (Finset.max'_lt_iff _ _).2 fun z hz => (Finset.lt_min'_iff _ _).2 fun w hw => ?_
  rcases Finset.mem_insert.1 hz with rfl | hz <;> rcases Finset.mem_insert.1 hw with rfl | hw
  · linarith
  · obtain ⟨c, hc, rfl⟩ := Finset.mem_image.1 hw
    obtain ⟨hc, hcx⟩ := Finset.mem_filter.1 hc
    have := (hP c (Finset.mem_union_right _ hc)).1.1
    linarith
  · obtain ⟨c, hc, rfl⟩ := Finset.mem_image.1 hz
    obtain ⟨hc, hcx⟩ := Finset.mem_filter.1 hc
    have := (hP c (Finset.mem_union_left _ hc)).1.2
    linarith
  · obtain ⟨c₁, hc₁, rfl⟩ := Finset.mem_image.1 hz
    obtain ⟨hc₁, hc₁x⟩ := Finset.mem_filter.1 hc₁
    obtain ⟨c₂, hc₂, rfl⟩ := Finset.mem_image.1 hw
    obtain ⟨hc₂, hc₂x⟩ := Finset.mem_filter.1 hc₂
    by_contra hcon
    exact hcons ⟨c₁, hc₁, c₂, hc₂, hc₁x.trans hc₂x, le_of_not_gt hcon⟩

/-- 6.5: a consistent finite set of up/down constraints in the band is realized by knots. -/
theorem realize_upset (Up Dn : Finset (ℝ × ℝ))
    (hP : ∀ c ∈ Up ∪ Dn, band c ∧ c.1 ∈ Ioo (0 : ℝ) 1)
    (hcons : ¬ ∃ c₁ ∈ Up, ∃ c₂ ∈ Dn, c₁.1 ≤ c₂.1 ∧ c₂.2 ≤ c₁.2) :
    ∃ K : Knots, (∀ c ∈ Up ∪ Dn, ∃ k, K.α k = c.1) ∧
      (∀ c ∈ Up, ∀ k, K.α k = c.1 → c.2 < K.β k) ∧
      (∀ c ∈ Dn, ∀ k, K.α k = c.1 → K.β k < c.2) := by
  classical
  set A : Finset ℝ := (Up ∪ Dn).image Prod.fst with hA
  set m := A.card with hm
  set e := A.orderEmbOfFin hm.symm with he
  let θ : Fin m → ℝ := fun k => ((k : ℕ) + 1 : ℝ) / ((m : ℝ) + 1)
  have hm1 : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  have hθ0 : ∀ k, 0 < θ k := fun k => by positivity
  have hθ1 : ∀ k : Fin m, θ k < 1 := fun k => by
    have : ((k : ℕ) : ℝ) + 1 ≤ (m : ℝ) := by exact_mod_cast k.isLt
    exact (div_lt_one hm1).2 (by linarith)
  have hθmono : ∀ i j : Fin m, i < j → θ i < θ j := fun i j hij => by
    have : ((i : ℕ) : ℝ) < ((j : ℕ) : ℝ) := by exact_mod_cast hij
    exact div_lt_div_of_pos_right (by linarith) hm1
  let βf : Fin m → ℝ := fun k => (1 - θ k) * lbF Up (e k) + θ k * ubF Dn (e k)
  have hlu : ∀ k, lbF Up (e k) < ubF Dn (e k) := fun k => lbF_lt_ubF hP hcons (e k)
  have hlb : ∀ k, lbF Up (e k) < βf k := fun k => by
    have := mul_pos (hθ0 k) (sub_pos.2 (hlu k))
    simp only [βf]; nlinarith
  have hub : ∀ k, βf k < ubF Dn (e k) := fun k => by
    have := mul_pos (sub_pos.2 (hθ1 k)) (sub_pos.2 (hlu k))
    simp only [βf]; nlinarith
  have hemem : ∀ k, ∃ c ∈ Up ∪ Dn, c.1 = e k := fun k =>
    Finset.mem_image.1 (Finset.orderEmbOfFin_mem A hm.symm k)
  have hβmono : StrictMono βf := by
    intro i j hij
    have hα := e.strictMono hij
    have hl := lbF_mono Up hα.le
    have hu := ubF_mono Dn hα.le
    have hθ := hθmono i j hij
    have k1 := mul_nonneg (sub_pos.2 (hθ1 j)).le (sub_nonneg.2 hl)
    have k2 := mul_nonneg (hθ0 j).le (sub_nonneg.2 hu)
    have k3 := mul_pos (sub_pos.2 hθ) (sub_pos.2 (hlu i))
    simp only [βf]
    nlinarith
  let K : Knots :=
    { n := m
      α := fun k => e k
      β := βf
      α_mono := e.strictMono
      β_mono := hβmono
      inBand := fun k => by
        simp only [band]
        constructor
        · linarith [le_lbF_self Up (e k), hlb k]
        · linarith [ubF_le_self Dn (e k), hub k]
      α_mem := fun k => by
        obtain ⟨c, hc, hce⟩ := hemem k
        rw [← hce]
        exact (hP c hc).2 }
  refine ⟨K, ?_, ?_, ?_⟩
  · intro c hc
    have hcA : c.1 ∈ A := Finset.mem_image_of_mem _ hc
    have hr : c.1 ∈ Set.range e := by
      rw [Finset.range_orderEmbOfFin]; exact hcA
    obtain ⟨k, hk⟩ := hr
    exact ⟨k, hk⟩
  · intro c hc k hk
    exact (le_lbF hc (le_of_eq hk.symm)).trans_lt (hlb k)
  · intro c hc k hk
    exact (hub k).trans_le (ubF_le hc (le_of_eq hk))

/-! ## Concrete tests -/

/-- `(1/4, 1/4)` lies on `ℓ(1/2, 1/2)` (the diagonal through `hyp (1/2)` and `M = arc (1/2)`). -/
example : lineFun (1/2) (1/2) ((1/4 : ℝ), (1/4 : ℝ)) = 0 := by
  norm_num [lineFun, dirX, dirY]

/-- Nesting at an explicit point: `ℓ(1/2,1/2)` below `ℓ(3/4,5/8)`; the point `(0, 3/4)` is on the
`B`-side of the outer line, hence strictly on the `B`-side of the inner one. -/
example : 0 < lineFun (1/2) (1/2) ((0 : ℝ), (3/4 : ℝ)) := by
  refine nested (α' := 3/4) (β' := 5/8) (by norm_num [band]) (by norm_num) (by norm_num [band])
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [Tri]) ?_
  norm_num [lineFun, dirX, dirY]

/-- `realize_upset` on a 2-point constraint set: up `(1/2, 1/2)`, down `(1/2, 3/5)`. -/
example : ∃ K : Knots, ∃ k, K.α k = 1/2 ∧ 1/2 < K.β k ∧ K.β k < 3/5 := by
  obtain ⟨K, hall, hup, hdn⟩ := realize_upset {((1/2 : ℝ), (1/2 : ℝ))} {((1/2 : ℝ), (3/5 : ℝ))}
    (by
      intro c hc
      simp only [Finset.mem_union, Finset.mem_singleton] at hc
      rcases hc with rfl | rfl <;> norm_num [band])
    (by
      rintro ⟨c₁, hc₁, c₂, hc₂, -, h⟩
      simp only [Finset.mem_singleton] at hc₁ hc₂
      subst hc₁ hc₂
      norm_num at h)
  obtain ⟨k, hk⟩ := hall ((1/2 : ℝ), (1/2 : ℝ)) (by simp)
  exact ⟨K, k, hk, hup ((1/2 : ℝ), (1/2 : ℝ)) (by simp) k hk,
    hdn ((1/2 : ℝ), (3/5 : ℝ)) (by simp) k hk⟩

/-- An inconsistent pair (up `(1/2, 3/5)` dominating down `(1/2, 1/2)` in the SE order) is
rejected by the consistency hypothesis. -/
example : ∃ c₁ ∈ ({((1/2 : ℝ), (3/5 : ℝ))} : Finset (ℝ × ℝ)),
    ∃ c₂ ∈ ({((1/2 : ℝ), (1/2 : ℝ))} : Finset (ℝ × ℝ)), c₁.1 ≤ c₂.1 ∧ c₂.2 ≤ c₁.2 :=
  ⟨_, Finset.mem_singleton_self _, _, Finset.mem_singleton_self _, by norm_num⟩

end REU
