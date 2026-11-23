import Q2CL.Defs

namespace Q2CL

open K4

/-! Proof plan: write `tLR1`, `tP` and (a lower bound for) `tL4` as one fraction over the
positive denominator `4 b (b' - a) b_n (b_n - a'_n)` (exact identities by `field_simp; ring`),
then prove each polynomial numerator positive by `nlinarith` separately for stay, step and wrap.
For `tL4` we use `x ε_n ≤ (1/75)(2/5)`, so `K (2 + x ε_n) ≤ K' := K · 752/375`. -/

/-- `K' = K · 752/375`. -/
private noncomputable def KP : ℝ := 39 / 88 * (752 / 375)

/-- Numerator of `tLR1`. -/
private noncomputable def nLR1 (u un δ : ℝ) : ℝ :=
  ((1 - 2 * KC) * (6/5 * fb u + 3 * fa' u δ) * (fb' u δ - fa u)
      + 3 * fa' u δ * (fb un - fb' u δ) + 4 * fb u * (1 - fb un)
      - 6 * KC * fa' u δ * (1 - fb' u δ)) * (fb un * (fb un - fa' un δ))
    + (-6 * KC * fa' un δ * (1 - fb un)) * (fb u * (fb' u δ - fa u))

/-- Numerator of the lower bound for `tL4`. -/
private noncomputable def nL4 (u un δ : ℝ) : ℝ :=
  ((1 - KP) * (6/5 * fb u + 3 * fa' u δ) * (fb' u δ - fa u)
      + (1 - fa' un δ) * (4 * fb u - 3 * fa' u δ)
      + (1 - KP) * 3 * fa' u δ * (1 - fb' u δ)) * (fb un * (fb un - fa' un δ))
    + (-3 * fa' un δ * (fb un - fa' un δ) - 3 * KP * fa' un δ * (1 - fb un))
        * (fb u * (fb' u δ - fa u))

private lemma lr1_eq (u un δ : ℝ) (hb : 0 < fb u) (hc : 0 < fb' u δ - fa u)
    (hbn : 0 < fb un) (hcn : 0 < fb un - fa' un δ) :
    tLR1 u un δ = nLR1 u un δ
      / (4 * (fb u * (fb' u δ - fa u)) * (fb un * (fb un - fa' un δ))) := by
  have h1 := hb.ne'; have h2 := hc.ne'; have h3 := hbn.ne'; have h4 := hcn.ne'
  unfold tLR1 tP fbeta falphaN fsB fsA fd feps nLR1
  field_simp
  ring

private lemma tp_eq (u un δ : ℝ) (hb : 0 < fb u) (hc : 0 < fb' u δ - fa u)
    (hbn : 0 < fb un) (hcn : 0 < fb un - fa' un δ) :
    tP u un δ =
      ((6/5 * fb u + 3 * fa' u δ) * (fb' u δ - fa u) + 3 * fa' u δ * (1 - fb' u δ))
          / (4 * (fb u * (fb' u δ - fa u)))
        + 3 * fa' un δ * (1 - fb un) / (4 * (fb un * (fb un - fa' un δ))) := by
  have h1 := hb.ne'; have h2 := hc.ne'; have h3 := hbn.ne'; have h4 := hcn.ne'
  unfold tP fbeta falphaN fsB fsA fd feps
  field_simp
  ring

private lemma l4_eq (u un δ x : ℝ) (hb : 0 < fb u) (hc : 0 < fb' u δ - fa u)
    (hbn : 0 < fb un) (hcn : 0 < fb un - fa' un δ) :
    tL4 u un δ x - (KP - KC * (2 + x * feps un δ)) * tP u un δ = nL4 u un δ
      / (4 * (fb u * (fb' u δ - fa u)) * (fb un * (fb un - fa' un δ))) := by
  have h1 := hb.ne'; have h2 := hc.ne'; have h3 := hbn.ne'; have h4 := hcn.ne'
  unfold tL4 tP fbeta falphaN fsB fsA fd feps nL4
  field_simp
  ring

/-- Reduction to the two numerators. -/
private lemma core (u un δ x : ℝ) (h0 : 0 ≤ δ) (hu : 0 ≤ u) (hu1 : u + δ ≤ 1)
    (hn : 0 ≤ un) (hn1 : un + δ ≤ 1) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 75)
    (N4 : 0 < nL4 u un δ) (N1 : 0 < nLR1 u un δ) :
    0 < tL4 u un δ x ∧ 0 < tLR1 u un δ := by
  have hb : 0 < fb u := by unfold fb; linarith
  have hbn : 0 < fb un := by unfold fb; linarith
  have hc : 0 < fb' u δ - fa u := by unfold fb' fb fa; linarith
  have hcn : 0 < fb un - fa' un δ := by unfold fb fa' fa; linarith
  have hden : 0 < 4 * (fb u * (fb' u δ - fa u)) * (fb un * (fb un - fa' un δ)) := by
    positivity
  constructor
  · have hP : 0 < tP u un δ := by
      rw [tp_eq u un δ hb hc hbn hcn]
      have t1 : 0 < (6/5 * fb u + 3 * fa' u δ) * (fb' u δ - fa u)
          + 3 * fa' u δ * (1 - fb' u δ) := by
        have : 0 ≤ 3 * fa' u δ * (1 - fb' u δ) := by
          apply mul_nonneg
          · unfold fa' fa; linarith
          · unfold fb' fb; linarith
        have : 0 < (6/5 * fb u + 3 * fa' u δ) * (fb' u δ - fa u) := by
          apply mul_pos _ hc; unfold fa' fa; linarith
        linarith
      have t2 : 0 ≤ 3 * fa' un δ * (1 - fb un) := by
        apply mul_nonneg
        · unfold fa' fa; linarith
        · unfold fb; linarith
      have := div_pos t1 (by positivity : (0:ℝ) < 4 * (fb u * (fb' u δ - fa u)))
      have := div_nonneg t2 (by positivity : (0:ℝ) ≤ 4 * (fb un * (fb un - fa' un δ)))
      linarith
    have he0 : 0 ≤ feps un δ := by
      unfold feps; apply div_nonneg _ hbn.le; unfold fa' fa; linarith
    have he1 : feps un δ ≤ 2 / 5 := by
      unfold feps; rw [div_le_iff₀ hbn]; unfold fa' fa fb; linarith
    have hk : 0 ≤ KP - KC * (2 + x * feps un δ) := by
      have : x * feps un δ ≤ 1 / 75 * (2 / 5) := mul_le_mul hx1 he1 he0 (by norm_num)
      unfold KP KC; nlinarith
    have e := l4_eq u un δ x hb hc hbn hcn
    have := div_pos N4 hden
    have := mul_nonneg hk hP.le
    linarith
  · rw [lr1_eq u un δ hb hc hbn hcn]
    exact div_pos N1 hden

/-- Lemma 83(1), transitions: L4 and LR1. -/
theorem trans_L4 (u un δ x : ℝ) (h : TransDom u un δ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 75) :
    0 < tL4 u un δ x ∧ 0 < tLR1 u un δ := by
  obtain ⟨h0, h1, hc⟩ := h
  have h1' : 0 ≤ 1 / 5 - δ := by linarith
  rcases hc with ⟨hu, hu1, rfl⟩ | ⟨hu, hu1, rfl⟩ | ⟨rfl, rfl⟩
  · have hv : 0 ≤ 1 - δ - un := by linarith
    apply core un un δ x h0 hu (by linarith) hu (by linarith) hx0 hx1
    · unfold nL4 KP fb' fb fa' fa
      nlinarith [mul_nonneg h0 hu, mul_nonneg h0 hv, mul_nonneg hu hv, mul_nonneg h0 h0,
        mul_nonneg (mul_nonneg h0 hu) hv, mul_nonneg (mul_nonneg hu hu) hv,
        mul_nonneg (mul_nonneg h0 h0) hv, mul_nonneg (mul_nonneg hv hv) hu,
        mul_nonneg (mul_nonneg hv hv) h0, mul_nonneg hv hv, mul_nonneg hu hu]
    · unfold nLR1 KC fb' fb fa' fa
      nlinarith [mul_nonneg h0 hu, mul_nonneg h0 hv, mul_nonneg hu hv, mul_nonneg h0 h0,
        mul_nonneg (mul_nonneg h0 hu) hv, mul_nonneg (mul_nonneg hu hu) hv,
        mul_nonneg (mul_nonneg h0 h0) hv, mul_nonneg (mul_nonneg hv hv) hu,
        mul_nonneg (mul_nonneg hv hv) h0, mul_nonneg hv hv, mul_nonneg hu hu]
  · have hv : 0 ≤ 1 - 3 * δ - u := by linarith
    apply core u (u + 2 * δ) δ x h0 hu (by linarith) (by linarith) (by linarith) hx0 hx1
    · unfold nL4 KP fb' fb fa' fa
      nlinarith [mul_nonneg h0 hu, mul_nonneg h0 hv, mul_nonneg hu hv, mul_nonneg h0 h0,
        mul_nonneg (mul_nonneg h0 hu) hv, mul_nonneg (mul_nonneg hu hu) hv,
        mul_nonneg (mul_nonneg h0 h0) hv, mul_nonneg (mul_nonneg hv hv) hu,
        mul_nonneg (mul_nonneg hv hv) h0, mul_nonneg hv hv, mul_nonneg hu hu]
    · unfold nLR1 KC fb' fb fa' fa
      nlinarith [mul_nonneg h0 hu, mul_nonneg h0 hv, mul_nonneg hu hv, mul_nonneg h0 h0,
        mul_nonneg (mul_nonneg h0 hu) hv, mul_nonneg (mul_nonneg hu hu) hv,
        mul_nonneg (mul_nonneg h0 h0) hv, mul_nonneg (mul_nonneg hv hv) hu,
        mul_nonneg (mul_nonneg hv hv) h0, mul_nonneg hv hv, mul_nonneg hu hu]
  · apply core (1 - δ) 0 δ x h0 (by linarith) (by linarith) le_rfl (by linarith) hx0 hx1
    · unfold nL4 KP fb' fb fa' fa
      nlinarith [mul_nonneg h0 h1', mul_nonneg h0 h0, mul_nonneg h1' h1',
        mul_nonneg (mul_nonneg h0 h0) h1', mul_nonneg (mul_nonneg h0 h1') h1',
        mul_nonneg (mul_nonneg h0 h0) h0, mul_nonneg (mul_nonneg h1' h1') h1']
    · unfold nLR1 KC fb' fb fa' fa
      nlinarith [mul_nonneg h0 h1', mul_nonneg h0 h0, mul_nonneg h1' h1',
        mul_nonneg (mul_nonneg h0 h0) h1', mul_nonneg (mul_nonneg h0 h1') h1',
        mul_nonneg (mul_nonneg h0 h0) h0, mul_nonneg (mul_nonneg h1' h1') h1']

end Q2CL
