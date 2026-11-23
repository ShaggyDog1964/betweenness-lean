import Q2CL.Defs

namespace Q2CL

open K4

private lemma cc_mem {p q : Lot 4} (hp : p ∈ Simplex 4) (hq : q ∈ Simplex 4) {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) : a • p + b • q ∈ Simplex 4 := by
  refine ⟨fun i => ?_, ?_⟩
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    exact add_nonneg (mul_nonneg ha (hp.1 i)) (mul_nonneg hb (hq.1 i))
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hp.2, hq.2]
    linarith

private lemma cc_between {R : Rel 4} (hR : IsBetweennessPref R) {p q : Lot 4}
    (hp : p ∈ Simplex 4) (hq : q ∈ Simplex 4) {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1)
    (hpq : R p q) : R (mix t p q) q ∧ R p (mix t p q) := by
  have hm : mix t p q ∈ Simplex 4 :=
    cc_mem hp hq ht.1.le (by linarith [ht.2]) (by ring)
  by_cases hqp : R q p
  · have h := hR.btw_indiff p hp q hq t ht ⟨hpq, hqp⟩
    exact ⟨hR.trans _ hm _ hp _ hq h.1 hpq, h.2⟩
  · have h := hR.btw_strict p hp q hq t ht ⟨hpq, hqp⟩
    exact ⟨h.2.1, h.1.1⟩

private lemma cc_swap (t : ℝ) (p q : Lot 4) : mix t p q = mix (1 - t) q p := by
  ext i; simp only [mix, Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring

/-- BT contour sets are convex (Lemma 1, inclusion BT ⊆ QC ∩ QV). -/
theorem bt_contour_convex {R : Rel 4} (hR : IsBetweennessPref R) {r : Lot 4}
    (hr : r ∈ Simplex 4) :
    Convex ℝ {p | p ∈ Simplex 4 ∧ R p r} ∧ Convex ℝ {p | p ∈ Simplex 4 ∧ R r p} := by
  constructor
  · rintro p ⟨hp, hpr⟩ q ⟨hq, hqr⟩ a b ha hb hab
    have hm := cc_mem hp hq ha hb hab
    refine ⟨hm, ?_⟩
    rcases ha.eq_or_lt with rfl | ha'
    · have : b = 1 := by linarith
      subst this; simpa using hqr
    rcases hb.eq_or_lt with rfl | hb'
    · have : a = 1 := by linarith
      subst this; simpa using hpr
    have hb1 : b = 1 - a := by linarith
    subst hb1
    have hat : a ∈ Set.Ioo (0 : ℝ) 1 := ⟨ha', by linarith⟩
    have hmix : a • p + (1 - a) • q = mix a p q := rfl
    rw [hmix] at hm ⊢
    rcases hR.complete p hp q hq with hpq | hqp
    · exact hR.trans _ hm _ hq _ hr (cc_between hR hp hq hat hpq).1 hqr
    · have hat' : 1 - a ∈ Set.Ioo (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
      rw [cc_swap] at hm ⊢
      exact hR.trans _ hm _ hp _ hr (cc_between hR hq hp hat' hqp).1 hpr
  · rintro p ⟨hp, hpr⟩ q ⟨hq, hqr⟩ a b ha hb hab
    have hm := cc_mem hp hq ha hb hab
    refine ⟨hm, ?_⟩
    rcases ha.eq_or_lt with rfl | ha'
    · have : b = 1 := by linarith
      subst this; simpa using hqr
    rcases hb.eq_or_lt with rfl | hb'
    · have : a = 1 := by linarith
      subst this; simpa using hpr
    have hb1 : b = 1 - a := by linarith
    subst hb1
    have hat : a ∈ Set.Ioo (0 : ℝ) 1 := ⟨ha', by linarith⟩
    have hmix : a • p + (1 - a) • q = mix a p q := rfl
    rw [hmix] at hm ⊢
    rcases hR.complete p hp q hq with hpq | hqp
    · exact hR.trans _ hr _ hp _ hm hpr (cc_between hR hp hq hat hpq).2
    · have hat' : 1 - a ∈ Set.Ioo (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
      rw [cc_swap] at hm ⊢
      exact hR.trans _ hr _ hq _ hm hqr (cc_between hR hq hp hat' hqp).2

end Q2CL
