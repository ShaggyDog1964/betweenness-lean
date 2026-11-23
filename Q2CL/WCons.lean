import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Q2CL.Defs
import Q2CL.WEnvelope

namespace Q2CL

open K4

private lemma four_rpow_pow : ((4 : ℝ) ^ (17 / 20 : ℝ)) ^ (20 : ℕ) = 4 ^ (17 : ℕ) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
  norm_num

private lemma four_rpow_le : (4 : ℝ) ^ (17 / 20 : ℝ) ≤ 13 / 4 := by
  by_contra h
  rw [not_le] at h
  have := pow_lt_pow_left₀ h (by norm_num) (show (20 : ℕ) ≠ 0 by norm_num)
  rw [four_rpow_pow] at this
  norm_num at this

private lemma four_rpow_ge : 5 / 2 ≤ (4 : ℝ) ^ (17 / 20 : ℝ) := by
  by_contra h
  rw [not_le] at h
  have := pow_lt_pow_left₀ h (by positivity) (show (20 : ℕ) ≠ 0 by norm_num)
  rw [four_rpow_pow] at this
  norm_num at this

/-- `(1 + H)/2 ≤ H^{17/20}` on `[1,4]`, by concavity (chord from 1 to 4). -/
private lemma half_le_rpow {H : ℝ} (h1 : 1 ≤ H) (h4 : H ≤ 4) :
    (1 + H) / 2 ≤ H ^ (17 / 20 : ℝ) := by
  have hcc : ConcaveOn ℝ (Set.Ici 0) fun x : ℝ ↦ x ^ (17 / 20 : ℝ) :=
    Real.concaveOn_rpow (by norm_num) (by norm_num)
  have hc := hcc.2 (show (1 : ℝ) ∈ Set.Ici 0 by norm_num)
    (show (4 : ℝ) ∈ Set.Ici 0 by norm_num)
    (show (0 : ℝ) ≤ (4 - H) / 3 by linarith) (show (0 : ℝ) ≤ (H - 1) / 3 by linarith)
    (by ring)
  simp only [smul_eq_mul, Real.one_rpow] at hc
  have hH : (4 - H) / 3 * 1 + (H - 1) / 3 * 4 = H := by ring
  rw [hH] at hc
  have := four_rpow_ge
  nlinarith

private lemma core {H g o w : ℝ} (h1 : 1 ≤ H) (h4 : H ≤ 4) (hg : 0 < g) (hg1 : g ≤ 1 / 75)
    (ho1 : -1 ≤ o) (hw : w ≤ o0 * (4 / H) ^ (17 / 20 : ℝ)) :
    1 / 11 * w * (1 + H + g * o) ≤ KC * (2 + g * max o 0) := by
  have hH0 : 0 < H := by linarith
  set p := H ^ (17 / 20 : ℝ) with hp
  set y := (4 : ℝ) ^ (17 / 20 : ℝ) with hy
  have hp1 : 1 ≤ p := Real.one_le_rpow h1 (by norm_num)
  have hp2 : (1 + H) / 2 ≤ p := half_le_rpow h1 h4
  have hy1 : y ≤ 13 / 4 := four_rpow_le
  have hy0 : 0 < y := by positivity
  have hx : (4 / H) ^ (17 / 20 : ℝ) = y / p := Real.div_rpow (by norm_num) hH0.le _
  rw [hx] at hw
  have hpos : 0 ≤ 1 + H + g * o := by nlinarith
  have hmo : g * o ≤ g * max o 0 := mul_le_mul_of_nonneg_left (le_max_left _ _) hg.le
  have hmo0 : 0 ≤ g * max o 0 := mul_nonneg hg.le (le_max_right _ _)
  have hp0 : 0 < p := by linarith
  -- y/p * (1 + H + g o) ≤ y * (2 + g o⁺)
  have key : y / p * (1 + H + g * o) ≤ y * (2 + g * max o 0) := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hp0]
    have : 1 + H + g * o ≤ 2 * p + p * (g * max o 0) := by nlinarith
    nlinarith
  have step : w * (1 + H + g * o) ≤ o0 * (y / p) * (1 + H + g * o) :=
    mul_le_mul_of_nonneg_right hw hpos
  have : o0 * (y / p) * (1 + H + g * o) ≤ o0 * (13 / 4 * (2 + g * max o 0)) := by
    rw [mul_assoc]
    apply mul_le_mul_of_nonneg_left _ (by unfold o0; norm_num)
    have : y * (2 + g * max o 0) ≤ 13 / 4 * (2 + g * max o 0) :=
      mul_le_mul_of_nonneg_right hy1 (by linarith)
    linarith
  unfold KC
  unfold o0 at this step
  nlinarith

/-- Consequences of the envelope: `o_1 ≤ 25/4`, and the `K`-bounds used in Lemma 76
for gadget items (height `H_j`, state `w_A(j)`) and transition items (height `H_{j+1}`,
state `w_B(j)`). -/
theorem w_cons {m ns : ℕ} {ds : ℝ} (hA : Adm m ns ds) :
    o1 m ns ≤ 25 / 4 ∧
    (∀ j, j < Jn m ns → ∀ o : ℝ, -1 ≤ o → o ≤ 3 →
      1 / 11 * wA m ns j * (1 + Hh m ns j + gP m ns * o) ≤ KC * (2 + gP m ns * max o 0)) ∧
    (∀ j, j + 1 < Jn m ns → ∀ o : ℝ, -1 ≤ o → o ≤ 3 →
      1 / 11 * wB m ns j * (1 + Hh m ns (j + 1) + gP m ns * o) ≤
        KC * (2 + gP m ns * max o 0)) := by
  obtain ⟨hg0, hg1, -, hJ, hHJ, -⟩ := J_spec hA
  obtain ⟨hE, -⟩ := w_envelope hA
  have hH1 : ∀ j, j < Jn m ns → 1 ≤ Hh m ns j := by
    intro j hj
    have h := (hJ j hj).1
    have : 0 ≤ gP m ns * epsJ m ns j := by
      apply mul_nonneg hg0.le
      unfold epsJ feps fa' fa fb uOf dlt; positivity
    linarith
  refine ⟨?_, ?_, ?_⟩
  · unfold o1
    have h := (hE (Jn m ns) le_rfl).2
    have hHp : 0 < Hh m ns (Jn m ns) := by linarith
    set x := 4 / Hh m ns (Jn m ns) with hx
    have hx0 : 0 ≤ x := by positivity
    have hxle : x ≤ 25 / 6 := by
      rw [hx, div_le_iff₀ hHp]; linarith
    have hr : x ^ (17 / 20 : ℝ) ≤ 25 / 6 := by
      rcases le_total x 1 with hx1 | hx1
      · have := Real.rpow_le_one hx0 hx1 (by norm_num : (0 : ℝ) ≤ 17 / 20)
        linarith
      · have := Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num : (17 / 20 : ℝ) ≤ 1)
        rw [Real.rpow_one] at this
        linarith
    unfold o0 at h
    linarith
  · intro j hj o ho1 _
    exact core (hH1 j hj) (hJ j hj).2 hg0 hg1 ho1 (hE j hj.le).2
  · intro j hj o ho1 _
    have hw : wB m ns j = wA m ns (j + 1) := by
      unfold wB wA; rw [Finset.prod_range_succ]; ring
    rw [hw]
    exact core (hH1 (j + 1) hj) (hJ (j + 1) hj).2 hg0 hg1 ho1 (hE (j + 1) hj.le).2

end Q2CL
