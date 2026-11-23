import Q2CL.Defs

namespace Q2CL

open K4

private lemma lineA (H g u δ t : ℝ) :
    (H + g * falpha u δ 0) * (1 - t) + (H + g * falpha u δ 1) * t = H + g * falpha u δ t := by
  unfold falpha; ring

private lemma lineB (H g u δ t : ℝ) :
    (H + g * fbeta u δ 0) * (1 - t) + (H + g * fbeta u δ 1) * t = H + g * fbeta u δ t := by
  unfold fbeta; ring

private lemma alpha_xa (u δ : ℝ) (h : fb u - fa' u δ ≠ 0) :
    falpha u δ (fa' u δ) = feps u δ := by
  unfold falpha fsA
  rw [div_mul_eq_mul_div, div_eq_iff h]; ring

private lemma alpha_ya (u δ : ℝ) : falpha u δ (fb u) = 0 := by
  unfold falpha; ring

private lemma beta_yb (u δ : ℝ) : fbeta u δ (fb' u δ) = -1 := by
  unfold fbeta; ring

private lemma beta_xb (u δ : ℝ) (h : fb' u δ - fa u ≠ 0) :
    fbeta u δ (fa u) = -feps u δ := by
  unfold fbeta fsB
  rw [div_mul_eq_mul_div]
  have : (feps u δ - 1) * (fa u - fb' u δ) / (fb' u δ - fa u) = -(feps u δ - 1) := by
    rw [div_eq_iff h]; ring
  rw [this]; ring

/-- Lemma 73 (normalization): the height step, the next `A` line in the frame of gadget `j`,
and each virtual point lying on its line. -/
theorem normalization (m ns j : ℕ) (hm : 2 ≤ m) :
    Hh m ns (j + 1) = Hh m ns j - gP m ns * dJ m ns j ∧
    (∀ t : ℝ, Hh m ns (j + 1) + gP m ns * alJ m ns (j + 1) t =
      Hh m ns j + gP m ns * falphaN (uOf m ns j) (uOf m ns (j + 1)) (dlt m) t) ∧
    (∀ τ, τ < 2 → ptL m ns j τ = UA m ns j * (1 - ptT m ns j τ) + SA m ns j * ptT m ns j τ) ∧
    (∀ τ, 2 ≤ τ → τ < 4 →
      ptL m ns j τ = UB m ns j * (1 - ptT m ns j τ) + SB m ns j * ptT m ns j τ) := by
  have h1 : Hh m ns (j + 1) = Hh m ns j - gP m ns * dJ m ns j := by
    unfold Hh; rw [Finset.sum_range_succ]; ring
  have hmR : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hδ0 : 0 ≤ dlt m := by unfold dlt; positivity
  have hδ1 : dlt m ≤ 1 / 5 := by
    unfold dlt; rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  have hu0 : 0 ≤ uOf m ns j := by unfold uOf; positivity
  have hA : fb (uOf m ns j) - fa' (uOf m ns j) (dlt m) ≠ 0 := by
    unfold fb fa' fa; intro h; nlinarith
  have hB : fb' (uOf m ns j) (dlt m) - fa (uOf m ns j) ≠ 0 := by
    unfold fb' fb fa; intro h; nlinarith
  refine ⟨h1, ?_, ?_, ?_⟩
  · intro t
    rw [h1]; unfold alJ falphaN falpha dJ; ring
  · intro τ hτ
    have e : UA m ns j * (1 - ptT m ns j τ) + SA m ns j * ptT m ns j τ =
        Hh m ns j + gP m ns * falpha (uOf m ns j) (dlt m) (ptT m ns j τ) := by
      rw [← lineA]; rfl
    rw [e]
    interval_cases τ
    · simp only [ptL, ptT, if_true]; rw [alpha_xa _ _ hA]; rfl
    · simp only [ptL, ptT, one_ne_zero, if_false, if_true]; rw [alpha_ya]; ring
  · intro τ hτ2 hτ4
    have e : UB m ns j * (1 - ptT m ns j τ) + SB m ns j * ptT m ns j τ =
        Hh m ns j + gP m ns * fbeta (uOf m ns j) (dlt m) (ptT m ns j τ) := by
      rw [← lineB]; rfl
    rw [e]
    interval_cases τ
    · simp only [ptL, ptT, OfNat.ofNat_ne_zero, OfNat.ofNat_ne_one, if_false, if_true]
      rw [beta_yb]; ring
    · simp only [ptL, ptT, OfNat.ofNat_ne_zero, OfNat.ofNat_ne_one, if_false,
        show (3:ℕ) ≠ 2 by decide]
      rw [beta_xb _ _ hB]; unfold epsJ; ring

end Q2CL
