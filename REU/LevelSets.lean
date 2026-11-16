/-
# Straight, non-crossing level lines and the chord lemma

For `t ∈ (0,1)` the level set `I_t = {q ∈ Tri : util q = t}` is `ℓ_t ∩ Tri`, where `ℓ_t` is
the line through `hyp t` and a second level point `levelPt t` (on the bottom or left edge)
with slope `tauAt t > 0`. `side t q` is the signed vertical offset of `q` from `ℓ_t`; `util`
is above `t` exactly on the positive side. Key lemma `chord_iff_tau`: for a chord `a` NE of
`b` whose line passes through `y ∈ Tri`, `a ≻ b ↔ tau y < slope a b` (strict pairs).
-/
import REU.Utility
import REU.Sanity

namespace REU

open Set

variable {R : Rel}

/-- A second point of the level set `I_t`: in `Tri`, on the bottom or left edge, and different
from `hyp t` (exists for `t ∈ (0,1)`). -/
noncomputable def levelPt (hR : IsBetweennessPref R) (t : ℝ) : Pt :=
  Classical.epsilon (fun e : Pt => e ∈ Tri ∧ util hR e = t ∧ (e.1 = 0 ∨ e.2 = 0) ∧ e ≠ hyp t)

/-- Slope of the level line `ℓ_t`. -/
noncomputable def tauAt (hR : IsBetweennessPref R) (t : ℝ) : ℝ := slope (hyp t) (levelPt hR t)

/-- Slope of the level line through `y` (meaningful for `y ∈ Tri \ {W, B}`). -/
noncomputable def tau (hR : IsBetweennessPref R) (y : Pt) : ℝ := tauAt hR (util hR y)

/-- Signed vertical offset of `q` above the level line `ℓ_t` (through `hyp t`, slope
`tauAt t`). Positive side contains `B`. -/
noncomputable def side (hR : IsBetweennessPref R) (t : ℝ) (q : Pt) : ℝ :=
  (q.2 - t) - tauAt hR t * (q.1 - (1 - t))

lemma levelPt_spec (hR : IsBetweennessPref R) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    levelPt hR t ∈ Tri ∧ util hR (levelPt hR t) = t ∧
      ((levelPt hR t).1 = 0 ∨ (levelPt hR t).2 = 0) ∧ levelPt hR t ≠ hyp t := by
  have hM : ((0 : ℝ), (0 : ℝ)) ∈ Tri := by refine ⟨?_, ?_, ?_⟩ <;> norm_num
  have hW := hyp_mem_tri le_rfl zero_le_one
  have hB := hyp_mem_tri zero_le_one le_rfl
  have hex : ∃ e : Pt, e ∈ Tri ∧ util hR e = t ∧ (e.1 = 0 ∨ e.2 = 0) ∧ e ≠ hyp t := by
    rcases le_total t (util hR ((0 : ℝ), (0 : ℝ))) with h | h
    · obtain ⟨l, hl, hu⟩ :=
        exists_mix_util_eq hR hM hW (by rw [util_hyp_zero]; exact ht.1.le) h
      refine ⟨_, mix_mem_tri hM hW hl.1 hl.2, hu, Or.inr (by simp [mix_snd, hyp]), fun e => ?_⟩
      have := congrArg Prod.snd e
      simp only [mix_snd, hyp] at this
      linarith [ht.1]
    · obtain ⟨l, hl, hu⟩ :=
        exists_mix_util_eq hR hB hM h (by rw [util_hyp_one]; exact ht.2.le)
      refine ⟨_, mix_mem_tri hB hM hl.1 hl.2, hu, Or.inl (by simp [mix_fst, hyp]), fun e => ?_⟩
      have := congrArg Prod.fst e
      simp only [mix_fst, hyp] at this
      linarith [ht.2]
  exact Classical.epsilon_spec hex

/-- Two points of one level set with the same `u`-coordinate coincide. -/
lemma level_fst_eq (hR : IsBetweennessPref R) {x y : Pt} (hx : x ∈ Tri) (hy : y ∈ Tri)
    (hxy : util hR x = util hR y) (h1 : x.1 = y.1) : x = y := by
  by_contra hne
  rcases le_total x.2 y.2 with h | h
  · have := util_strictFOSD hR hy hx ⟨⟨h1.ge, h⟩, Ne.symm hne⟩; linarith
  · have := util_strictFOSD hR hx hy ⟨⟨h1.le, h⟩, hne⟩; linarith

/-- Points of one level set form a strict NE chain. -/
lemma level_snd_lt (hR : IsBetweennessPref R) {x y : Pt} (hx : x ∈ Tri) (hy : y ∈ Tri)
    (hxy : util hR x = util hR y) (h1 : x.1 < y.1) : x.2 < y.2 := by
  by_contra h
  push Not at h
  have hne : x ≠ y := fun e => by rw [e] at h1; exact lt_irrefl _ h1
  have := util_strictFOSD hR hx hy ⟨⟨h1.le, h⟩, hne⟩
  linarith

lemma levelPt_NE (hR : IsBetweennessPref R) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    NE (hyp t) (levelPt hR t) := by
  obtain ⟨he, hu, _, hne⟩ := levelPt_spec hR ht
  have hp := hyp_mem_tri ht.1.le ht.2.le
  have hup : util hR (hyp t) = t := util_hyp hR ⟨ht.1.le, ht.2.le⟩
  rcases lt_trichotomy (levelPt hR t).1 (hyp t).1 with h | h | h
  · exact ⟨h, level_snd_lt hR he hp (by rw [hu, hup]) h⟩
  · exact absurd (level_fst_eq hR he hp (by rw [hu, hup]) h) hne
  · have := level_snd_lt hR hp he (by rw [hu, hup]) h
    obtain ⟨_, _, h3⟩ := he
    simp only [hyp] at h this
    linarith

lemma tauAt_pos (hR : IsBetweennessPref R) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    0 < tauAt hR t := slope_pos_of_NE (levelPt_NE hR ht)

theorem tau_pos (hR : IsBetweennessPref R) {y : Pt} (hy : y ∈ Tri)
    (hW : y ≠ ((1 : ℝ), (0 : ℝ))) (hB : y ≠ ((0 : ℝ), (1 : ℝ))) : 0 < tau hR y :=
  tauAt_pos hR (util_mem_Ioo hR hy hW hB)

lemma side_mix (hR : IsBetweennessPref R) (t l : ℝ) (x z : Pt) :
    side hR t (mix l x z) = l * side hR t x + (1 - l) * side hR t z := by
  simp only [side, mix_fst, mix_snd]; ring

lemma side_hyp (hR : IsBetweennessPref R) (t : ℝ) : side hR t (hyp t) = 0 := by
  simp only [side, hyp]; ring

lemma side_levelPt (hR : IsBetweennessPref R) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    side hR t (levelPt hR t) = 0 := by
  obtain ⟨h1, _⟩ := levelPt_NE hR ht
  simp only [hyp] at h1
  have hd : (1 - t) - (levelPt hR t).1 ≠ 0 := by linarith
  simp only [side, tauAt, slope, hyp]
  field_simp
  ring

/-- Three points of one level set: the one in the middle (by `u`) is a mixture of the others. -/
lemma level_mid (hR : IsBetweennessPref R) {x y z : Pt} (hx : x ∈ Tri) (hy : y ∈ Tri)
    (hz : z ∈ Tri) (hxy : util hR x = util hR y) (hyz : util hR y = util hR z)
    (h1 : x.1 ≤ y.1) (h2 : y.1 ≤ z.1) : ∃ l ∈ Icc (0 : ℝ) 1, y = mix l z x := by
  rcases (h1.trans h2).eq_or_lt with h | h
  · have hyx : y = x := level_fst_eq hR hy hx hxy.symm (le_antisymm (by linarith) h1)
    exact ⟨0, ⟨le_rfl, zero_le_one⟩, by rw [mix_zero, hyx]⟩
  · have hd : 0 < z.1 - x.1 := by linarith
    have hl : (y.1 - x.1) / (z.1 - x.1) ∈ Icc (0 : ℝ) 1 :=
      ⟨div_nonneg (by linarith) hd.le, (div_le_one hd).2 (by linarith)⟩
    refine ⟨_, hl, ?_⟩
    have hw := mix_mem_tri hz hx hl.1 hl.2
    have hu : util hR (mix ((y.1 - x.1) / (z.1 - x.1)) z x) = util hR y := by
      rw [level_convex hR hz hx (hxy.trans hyz).symm hl]; exact hyz.symm
    have hf : (mix ((y.1 - x.1) / (z.1 - x.1)) z x).1 = y.1 := by
      rw [mix_fst]; field_simp; ring
    exact (level_fst_eq hR hw hy hu hf).symm

/-- `I_t = ℓ_t ∩ Tri`. -/
theorem level_eq_line (hR : IsBetweennessPref R) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) {q : Pt}
    (hq : q ∈ Tri) : util hR q = t ↔ side hR t q = 0 := by
  obtain ⟨he, hu, hedge, _⟩ := levelPt_spec hR ht
  have hp := hyp_mem_tri ht.1.le ht.2.le
  have hup := util_hyp hR ⟨ht.1.le, ht.2.le⟩
  constructor
  · intro hq_eq
    have hqp : q.1 ≤ (hyp t).1 := by
      by_contra h
      push Not at h
      have := level_snd_lt hR hp hq (by rw [hup, hq_eq]) h
      obtain ⟨_, _, h3⟩ := hq
      simp only [hyp] at h this
      linarith
    have heq : (levelPt hR t).1 ≤ q.1 := by
      by_contra h
      push Not at h
      have := level_snd_lt hR hq he (by rw [hq_eq, hu]) h
      obtain ⟨h1, h2, _⟩ := hq
      rcases hedge with h' | h' <;> linarith
    obtain ⟨l, _, hmix⟩ :=
      level_mid hR he hq hp (by rw [hu, hq_eq]) (by rw [hq_eq, hup]) heq hqp
    rw [hmix, side_mix, side_hyp, side_levelPt hR ht]
    ring
  · intro h
    have hτ := tauAt_pos hR ht
    have hse := side_levelPt hR ht
    obtain ⟨n1, _⟩ := levelPt_NE hR ht
    simp only [hyp] at n1
    simp only [side] at h hse
    have hqp : q.1 ≤ 1 - t := by
      by_contra hc
      push Not at hc
      obtain ⟨_, _, h3⟩ := hq
      nlinarith [mul_pos hτ (sub_pos.2 hc)]
    have heq : (levelPt hR t).1 ≤ q.1 := by
      by_contra hc
      push Not at hc
      obtain ⟨h1, h2, _⟩ := hq
      have : q.2 < (levelPt hR t).2 := by nlinarith [mul_pos hτ (sub_pos.2 hc)]
      rcases hedge with h' | h' <;> linarith
    have hd : 0 < (1 - t) - (levelPt hR t).1 := by linarith
    have hl : (q.1 - (levelPt hR t).1) / ((1 - t) - (levelPt hR t).1) ∈ Icc (0 : ℝ) 1 :=
      ⟨div_nonneg (by linarith) hd.le, (div_le_one hd).2 (by linarith)⟩
    have hlm : (q.1 - (levelPt hR t).1) / ((1 - t) - (levelPt hR t).1) *
        ((1 - t) - (levelPt hR t).1) = q.1 - (levelPt hR t).1 := div_mul_cancel₀ _ hd.ne'
    have hqm : q = mix ((q.1 - (levelPt hR t).1) / ((1 - t) - (levelPt hR t).1))
        (hyp t) (levelPt hR t) := by
      ext
      · rw [mix_fst]; simp only [hyp]; linear_combination (-1 : ℝ) * hlm
      · rw [mix_snd]; simp only [hyp]
        linear_combination h - (1 - (q.1 - (levelPt hR t).1) / ((1 - t) - (levelPt hR t).1)) *
          hse - tauAt hR t * hlm
    rw [hqm, level_convex hR hp he (by rw [hup, hu]) hl, hup]

/-- Distinct level lines do not meet in `Tri`. -/
theorem levels_disjoint_lines (hR : IsBetweennessPref R) {t t' : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1)
    (ht' : t' ∈ Ioo (0 : ℝ) 1) {q : Pt} (hq : q ∈ Tri) (h : side hR t q = 0)
    (h' : side hR t' q = 0) : t = t' := by
  rw [← (level_eq_line hR ht hq).2 h, ← (level_eq_line hR ht' hq).2 h']

lemma pos_combo {A B l : ℝ} (hA : 0 < A) (hB : 0 < B) (hl : l ∈ Icc (0 : ℝ) 1) :
    0 < l * A + (1 - l) * B := by
  rcases hl.1.eq_or_lt with h | h
  · rw [← h]; linarith
  · nlinarith [mul_pos h hA, mul_nonneg (sub_nonneg.2 hl.2) hB.le]

/-- Above the level line `ℓ_t`, `util > t`. -/
theorem util_gt_of_side (hR : IsBetweennessPref R) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) {q : Pt}
    (hq : q ∈ Tri) (h : 0 < side hR t q) : t < util hR q := by
  by_contra hle
  push Not at hle
  have hne : util hR q ≠ t := fun e => by
    rw [(level_eq_line hR ht hq).1 e] at h; exact lt_irrefl _ h
  have hlt : util hR q < t := lt_of_le_of_ne hle hne
  have hB := hyp_mem_tri zero_le_one le_rfl
  obtain ⟨l, hl, hu⟩ :=
    exists_mix_util_eq hR hB hq hlt.le (by rw [util_hyp_one]; exact ht.2.le)
  have h0 := (level_eq_line hR ht (mix_mem_tri hB hq hl.1 hl.2)).1 hu
  rw [side_mix] at h0
  have hsB : 0 < side hR t (hyp 1) := by
    simp only [side, hyp]; nlinarith [mul_pos (tauAt_pos hR ht) (sub_pos.2 ht.2), ht.1, ht.2]
  have := pos_combo hsB h hl
  linarith

/-- Below the level line `ℓ_t`, `util < t`. -/
theorem util_lt_of_side (hR : IsBetweennessPref R) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) {q : Pt}
    (hq : q ∈ Tri) (h : side hR t q < 0) : util hR q < t := by
  by_contra hle
  push Not at hle
  have hne : util hR q ≠ t := fun e => by
    rw [(level_eq_line hR ht hq).1 e] at h; exact lt_irrefl _ h
  have hlt : t < util hR q := lt_of_le_of_ne hle (Ne.symm hne)
  have hW := hyp_mem_tri le_rfl zero_le_one
  obtain ⟨l, hl, hu⟩ :=
    exists_mix_util_eq hR hq hW (by rw [util_hyp_zero]; exact ht.1.le) hlt.le
  have h0 := (level_eq_line hR ht (mix_mem_tri hq hW hl.1 hl.2)).1 hu
  rw [side_mix] at h0
  have hsW : side hR t (hyp 0) < 0 := by
    simp only [side, hyp]; nlinarith [mul_pos (tauAt_pos hR ht) ht.1, ht.1, ht.2]
  have := pos_combo (neg_pos.2 h) (neg_pos.2 hsW) hl
  linarith

/-- The level line through `y`, written through `y`: `side (util y) q = (q.2 - y.2) - tau y (q.1 - y.1)`. -/
lemma side_util_eq (hR : IsBetweennessPref R) {y : Pt} (hy : y ∈ Tri)
    (hW : y ≠ ((1 : ℝ), (0 : ℝ))) (hB : y ≠ ((0 : ℝ), (1 : ℝ))) (q : Pt) :
    side hR (util hR y) q = (q.2 - y.2) - tau hR y * (q.1 - y.1) := by
  have h0 := (level_eq_line hR (util_mem_Ioo hR hy hW hB) hy).1 rfl
  unfold tau
  simp only [side] at h0 ⊢
  linear_combination h0

/-- The indifference class of `q ∈ Tri \ {W, B}` is the intersection of `Tri` with the line
through `q` of slope `tau q > 0`. -/
theorem level_is_segment (hR : IsBetweennessPref R) {q : Pt} (hq : q ∈ Tri)
    (hW : q ≠ ((1 : ℝ), (0 : ℝ))) (hB : q ≠ ((0 : ℝ), (1 : ℝ))) :
    0 < tau hR q ∧ ∀ r ∈ Tri, (Indiff R r q ↔ r.2 - q.2 = tau hR q * (r.1 - q.1)) := by
  refine ⟨tau_pos hR hq hW hB, fun r hr => ?_⟩
  rw [indiff_iff_util hR hr hq, level_eq_line hR (util_mem_Ioo hR hq hW hB) hr,
    side_util_eq hR hq hW hB]
  constructor <;> intro h <;> linarith

/-- A chord line (positive slope, through two points of `Tri`) misses `W` and `B`. -/
theorem chord_line_avoids_vertices {a b y : Pt} (ha : a ∈ Tri) (hb : b ∈ Tri) (hab : NE a b)
    (hline : OnLine a b y) : y ≠ ((1 : ℝ), (0 : ℝ)) ∧ y ≠ ((0 : ℝ), (1 : ℝ)) := by
  obtain ⟨h1, h2⟩ := hab
  obtain ⟨a1, a2, a3⟩ := ha
  obtain ⟨b1, b2, b3⟩ := hb
  unfold OnLine at hline
  constructor
  · rintro rfl
    simp only at hline
    nlinarith [mul_nonpos_of_nonneg_of_nonpos (show 0 ≤ 1 - a.1 by linarith)
      (show b.2 - a.2 ≤ 0 by linarith), mul_pos (show 0 < a.2 by linarith)
      (show 0 < a.1 - b.1 by linarith)]
  · rintro rfl
    simp only at hline
    nlinarith [mul_nonneg (show 0 ≤ 1 - a.2 by linarith)
      (show 0 ≤ a.1 - b.1 by linarith), mul_pos (show 0 < a.1 by linarith)
      (show 0 < a.2 - b.2 by linarith)]

lemma onLine_swap {a b y : Pt} (h : OnLine a b y) : OnLine b a y := by
  unfold OnLine at h ⊢; linear_combination (-1 : ℝ) * h

lemma side_cross (hR : IsBetweennessPref R) (t : ℝ) (a b y : Pt) :
    (b.1 - y.1) * side hR t a - (a.1 - y.1) * side hR t b =
      ((y.1 - a.1) * (b.2 - a.2) - (y.2 - a.2) * (b.1 - a.1)) + (b.1 - a.1) * side hR t y := by
  simp only [side]; ring

/-- If `y ∈ ℓ_t` lies on line `ab` and `a ∉ ℓ_t`, then `b = y + (side b / side a)(a - y)`. -/
lemma eq_mix_of_side (hR : IsBetweennessPref R) {t : ℝ} {a b y : Pt} (hline : OnLine a b y)
    (hy0 : side hR t y = 0) (ha0 : side hR t a ≠ 0) :
    b = mix (side hR t b / side hR t a) a y := by
  unfold OnLine at hline
  have hκ : side hR t b / side hR t a * side hR t a = side hR t b := div_mul_cancel₀ _ ha0
  have e1 : (b.1 - y.1) * side hR t a = (side hR t b / side hR t a * (a.1 - y.1)) * side hR t a := by
    linear_combination side_cross hR t a b y + hline + (b.1 - a.1) * hy0 - (a.1 - y.1) * hκ
  have e2 : (b.2 - y.2) * side hR t a = (side hR t b / side hR t a * (a.2 - y.2)) * side hR t a := by
    simp only [side] at hy0 hκ ⊢
    linear_combination (tauAt hR t) * hline + (b.2 - a.2) * hy0 - (a.2 - y.2) * hκ
  have f1 := mul_right_cancel₀ ha0 e1
  have f2 := mul_right_cancel₀ ha0 e2
  ext
  · rw [mix_fst]; linear_combination f1
  · rw [mix_snd]; linear_combination f2

lemma side_eq_zero_of_eq (hR : IsBetweennessPref R) {t : ℝ} {a b y : Pt} (hline : OnLine a b y)
    (hy0 : side hR t y = 0) (hab : side hR t a = side hR t b) (hne : a.1 ≠ b.1) :
    side hR t a = 0 := by
  unfold OnLine at hline
  have : (b.1 - a.1) * side hR t a = 0 := by
    linear_combination side_cross hR t a b y + hline + (b.1 - a.1) * hy0 - (a.1 - y.1) * hab
  rcases mul_eq_zero.1 this with h | h
  · exact absurd (by linarith) hne
  · exact h

/-- Along a line through a point `y` of `ℓ_t`, `util` is weakly ordered as `side t`. -/
lemma util_le_of_side_lt (hR : IsBetweennessPref R) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1)
    {a b y : Pt} (hy : y ∈ Tri) (ha : a ∈ Tri) (hb : b ∈ Tri) (hline : OnLine a b y)
    (hy0 : side hR t y = 0) (hlt : side hR t b < side hR t a) : util hR b ≤ util hR a := by
  have hyt : util hR y = t := (level_eq_line hR ht hy).2 hy0
  have hle0 : ∀ q ∈ Tri, side hR t q ≤ 0 → util hR q ≤ t := fun q hq h => by
    rcases h.lt_or_eq with h | h
    · exact (util_lt_of_side hR ht hq h).le
    · exact ((level_eq_line hR ht hq).2 h).le
  have hge0 : ∀ q ∈ Tri, 0 ≤ side hR t q → t ≤ util hR q := fun q hq h => by
    rcases h.lt_or_eq with h | h
    · exact (util_gt_of_side hR ht hq h).le
    · exact ((level_eq_line hR ht hq).2 h.symm).ge
  by_cases hb0 : side hR t b ≤ 0
  · by_cases ha0 : 0 ≤ side hR t a
    · exact (hle0 b hb hb0).trans (hge0 a ha ha0)
    · push Not at ha0
      have hb0' : side hR t b ≠ 0 := by linarith
      have hmix := eq_mix_of_side hR (onLine_swap hline) hy0 hb0'
      have hκ : side hR t a / side hR t b ∈ Icc (0 : ℝ) 1 :=
        ⟨div_nonneg_of_nonpos ha0.le (by linarith), (div_le_one_of_neg (by linarith)).2 hlt.le⟩
      have hm := util_mix_mem hR hb hy hκ
      rw [← hmix, hyt] at hm
      have hat := util_lt_of_side hR ht ha ha0
      rcases Set.mem_uIcc.1 hm with h | h <;> linarith [h.1, h.2]
  · push Not at hb0
    have ha0' : side hR t a ≠ 0 := by linarith
    have hmix := eq_mix_of_side hR hline hy0 ha0'
    have hκ : side hR t b / side hR t a ∈ Icc (0 : ℝ) 1 :=
      ⟨div_nonneg hb0.le (by linarith), (div_le_one (by linarith)).2 hlt.le⟩
    have hm := util_mix_mem hR ha hy hκ
    rw [← hmix, hyt] at hm
    have hbt := util_gt_of_side hR ht hb hb0
    rcases Set.mem_uIcc.1 hm with h | h <;> linarith [h.1, h.2]

/-- **Key lemma.** For a chord `a` NE of `b` whose line passes through `y ∈ Tri` and a strict
pair (`¬ a ∼ b`): `a ≻ b ↔ tau y < slope a b`. Covers `y` on the boundary, `y = (0,0)`, and `y`
outside the segment `[b, a]`. -/
theorem chord_iff_tau (hR : IsBetweennessPref R) {a b y : Pt} (hy : y ∈ Tri) (ha : a ∈ Tri)
    (hb : b ∈ Tri) (hab : NE a b) (hline : OnLine a b y) (hstrict : ¬ Indiff R a b) :
    SPref R a b ↔ tau hR y < slope a b := by
  obtain ⟨hW, hB⟩ := chord_line_avoids_vertices ha hb hab hline
  have ht := util_mem_Ioo hR hy hW hB
  have hy0 : side hR (util hR y) y = 0 := (level_eq_line hR ht hy).1 rfl
  have hτ : tau hR y = tauAt hR (util hR y) := rfl
  have hd : 0 < a.1 - b.1 := by linarith [hab.1]
  have key : side hR (util hR y) a - side hR (util hR y) b =
      (a.1 - b.1) * (slope a b - tauAt hR (util hR y)) := by
    simp only [side, slope]; field_simp; ring
  rw [hτ]
  constructor
  · intro h
    by_contra hle
    push Not at hle
    rcases hle.lt_or_eq with hlt | heq
    · have hs : side hR (util hR y) a < side hR (util hR y) b := by
        nlinarith [mul_pos hd (sub_pos.2 hlt)]
      have := util_le_of_side_lt hR ht hy hb ha (onLine_swap hline) hy0 hs
      exact h.2 ((pref_iff_util hR hb ha).2 this)
    · have hab' : side hR (util hR y) a = side hR (util hR y) b := by
        rw [heq, sub_self, mul_zero] at key; linarith
      have hza := side_eq_zero_of_eq hR hline hy0 hab' (fun e => by linarith)
      have ua := (level_eq_line hR ht ha).2 hza
      have ub := (level_eq_line hR ht hb).2 (hab' ▸ hza)
      exact hstrict ((indiff_iff_util hR ha hb).2 (by rw [ua, ub]))
  · intro hlt
    have hs : side hR (util hR y) b < side hR (util hR y) a := by
      nlinarith [mul_pos hd (sub_pos.2 hlt)]
    have hle := util_le_of_side_lt hR ht hy ha hb hline hy0 hs
    exact ⟨(pref_iff_util hR ha hb).2 hle,
      fun hba => hstrict ⟨(pref_iff_util hR ha hb).2 hle, hba⟩⟩

/-! ## Test: the EU preference `U(u,v) = v - u` has level lines of slope 1 -/

lemma tau_Rlin {y : Pt} (hy : y ∈ Tri) (hW : y ≠ ((1 : ℝ), (0 : ℝ)))
    (hB : y ≠ ((0 : ℝ), (1 : ℝ))) : tau Sanity.isBetweenness_Rlin y = 1 := by
  have hR := Sanity.isBetweenness_Rlin
  have ht := util_mem_Ioo hR hy hW hB
  obtain ⟨he, hu, _, _⟩ := levelPt_spec hR ht
  obtain ⟨n1, _⟩ := levelPt_NE hR ht
  have hp := hyp_mem_tri ht.1.le ht.2.le
  have hi := (indiff_iff_util hR he hp).2 (by rw [hu, util_hyp hR ⟨ht.1.le, ht.2.le⟩])
  obtain ⟨i1, i2⟩ := hi
  simp only [Sanity.Rlin, hyp] at i1 i2 n1
  unfold tau tauAt slope
  simp only [hyp]
  rw [div_eq_one_iff_eq (by linarith)]
  linarith

/-- `chord_iff_tau` at the vertex `y = (0,0)` (on the boundary, and an endpoint of the chord). -/
example : SPref Sanity.Rlin ((1/4 : ℝ), (1/2 : ℝ)) ((0 : ℝ), (0 : ℝ)) := by
  have hy : ((0 : ℝ), (0 : ℝ)) ∈ Tri := by refine ⟨?_, ?_, ?_⟩ <;> norm_num
  have ha : ((1/4 : ℝ), (1/2 : ℝ)) ∈ Tri := by refine ⟨?_, ?_, ?_⟩ <;> norm_num
  rw [chord_iff_tau Sanity.isBetweenness_Rlin hy ha hy (by unfold NE; norm_num)
    (by unfold OnLine; norm_num) (by simp only [Indiff, Sanity.Rlin]; norm_num),
    tau_Rlin hy (by simp [Prod.ext_iff]) (by simp [Prod.ext_iff])]
  unfold slope; norm_num

/-- `chord_iff_tau` at `y = (1/2, 0)` on the bottom edge, outside the chord segment `[b, a]`. -/
example : SPref Sanity.Rlin ((2/3 : ℝ), (1/3 : ℝ)) ((5/8 : ℝ), (1/4 : ℝ)) := by
  have hy : ((1/2 : ℝ), (0 : ℝ)) ∈ Tri := by refine ⟨?_, ?_, ?_⟩ <;> norm_num
  have ha : ((2/3 : ℝ), (1/3 : ℝ)) ∈ Tri := by refine ⟨?_, ?_, ?_⟩ <;> norm_num
  have hb : ((5/8 : ℝ), (1/4 : ℝ)) ∈ Tri := by refine ⟨?_, ?_, ?_⟩ <;> norm_num
  rw [chord_iff_tau Sanity.isBetweenness_Rlin hy ha hb (by unfold NE; norm_num)
    (by unfold OnLine; norm_num) (by simp only [Indiff, Sanity.Rlin]; norm_num),
    tau_Rlin hy (by simp [Prod.ext_iff]) (by simp [Prod.ext_iff])]
  unfold slope; norm_num

end REU
