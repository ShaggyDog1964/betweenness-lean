import Q2CL.Defs
import Q2CL.CwBound
import Q2CL.WEnvelope
import Q2CL.Normalization
import Q2CL.FaceBasic

namespace Q2CL

open K4

private lemma ss_poly (y g : ℝ) (hy1 : 1 ≤ y) (hy4 : y ≤ 4) (hg0 : 0 < g) (hg : g ≤ 1 / 80) :
    3 / 100 * (1 + y + g) ^ 2 * (y - 3 * g) ≤ (y - 3 * g) - 1 / 12 * ((y - 3 * g) + 6 * (1 + 3 * g)) := by
  have h1 : (1 + y + g) ^ 2 ≤ (y + 81 / 80) ^ 2 := by
    apply pow_le_pow_left₀ (by linarith); linarith
  have h2 : 0 < y - 3 * g := by linarith
  have h3 : 3 / 100 * (1 + y + g) ^ 2 * (y - 3 * g) ≤ 3 / 100 * (y + 81 / 80) ^ 2 * y := by
    have := mul_le_mul h1 (show y - 3 * g ≤ y by linarith) h2.le (by positivity)
    nlinarith
  have h4 : 3 / 100 * (y + 81 / 80) ^ 2 * y ≤ 11 / 12 * (y - 3 / 80) - 1 / 2 * (83 / 80) := by
    nlinarith [mul_nonneg (sub_nonneg.2 hy1) (sub_nonneg.2 hy4),
      mul_nonneg (mul_nonneg (sub_nonneg.2 hy1) (sub_nonneg.2 hy4)) (by linarith : (0:ℝ) ≤ y)]
  nlinarith

/-- Core inequality for the coordinate-2 gap. -/
private lemma ss_core (s y g L1 L2 S1 S2 w1 w2 : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 12)
    (hg0 : 0 < g) (hg : g ≤ 1 / 80) (hy1 : 1 ≤ y) (hy4 : y ≤ 4) (hL1 : L1 ≤ y + g)
    (hL2 : 0 < 1 + L2) (hΔ : L2 < L1) (hS : S1 - L1 = S2 - L2) (he : -3 * g ≤ S1 - L1)
    (hS2 : 0 < S2) (hw1 : 0 < w1) (hw12 : w1 ≤ w2) (hwe : w1 * (y - 3 * g) ≤ 6) :
    3 / 100 * (L1 - L2) ≤
      ((1 - s) * L1 - s * (w1 * S1)) / (1 + L1) - ((1 - s) * L2 - s * (w2 * S2)) / (1 + L2) := by
  have hL1' : 0 < 1 + L1 := by linarith
  rw [div_sub_div _ _ hL1'.ne' hL2.ne', le_div_iff₀ (mul_pos hL1' hL2)]
  set Δ := L1 - L2 with hΔdef
  have hΔ0 : 0 < Δ := by linarith
  have hN : ((1 - s) * L1 - s * (w1 * S1)) * (1 + L2) - (1 + L1) * ((1 - s) * L2 - s * (w2 * S2))
      = (1 - s) * Δ + s * (w2 * S2 * (1 + L1) - w1 * S1 * (1 + L2)) := by
    rw [hΔdef]; ring
  have hV : w2 * S2 * (1 + L1) - w1 * S1 * (1 + L2) ≥ -(w1 * Δ * (1 + 3 * g)) := by
    have a1 : w1 * (S2 * (1 + L1)) ≤ w2 * (S2 * (1 + L1)) :=
      mul_le_mul_of_nonneg_right hw12 (by positivity)
    have a2 : S2 * (1 + L1) - S1 * (1 + L2) = -(Δ * (1 - (S1 - L1))) := by
      have : S2 = S1 - L1 + L2 := by linarith
      rw [this, hΔdef]; ring
    have a3 : Δ * (1 - (S1 - L1)) ≤ Δ * (1 + 3 * g) :=
      mul_le_mul_of_nonneg_left (by linarith) hΔ0.le
    have a4 := mul_le_mul_of_nonneg_left a3 hw1.le
    nlinarith
  have hy3 : 0 < y - 3 * g := by linarith
  have hP := ss_poly y g hy1 hy4 hg0 hg
  -- B := 1 - (1/12)(1 + w1 (1+3g)) ≥ 3/100 (1+y+g)^2
  have hB : 3 / 100 * (1 + y + g) ^ 2 ≤ 1 - 1 / 12 * (1 + w1 * (1 + 3 * g)) := by
    have k : w1 * (1 + 3 * g) * (y - 3 * g) ≤ 6 * (1 + 3 * g) := by
      have := mul_le_mul_of_nonneg_left hwe (by linarith : (0:ℝ) ≤ 1 + 3 * g); linarith
    have : (3 / 100 * (1 + y + g) ^ 2) * (y - 3 * g) ≤
        (1 - 1 / 12 * (1 + w1 * (1 + 3 * g))) * (y - 3 * g) := by nlinarith
    exact le_of_mul_le_mul_right this hy3
  have hD : (1 + L1) * (1 + L2) ≤ (1 + y + g) ^ 2 := by
    have : (1 + L1) * (1 + L2) ≤ (1 + L1) * (1 + L1) :=
      mul_le_mul_of_nonneg_left (by linarith) hL1'.le
    nlinarith
  have hsB : 1 - 1 / 12 * (1 + w1 * (1 + 3 * g)) ≤ 1 - s * (1 + w1 * (1 + 3 * g)) := by
    have : 0 ≤ 1 + w1 * (1 + 3 * g) := by positivity
    nlinarith
  rw [hN]
  have e1 : 3 / 100 * Δ * ((1 + L1) * (1 + L2)) ≤ 3 / 100 * Δ * (1 + y + g) ^ 2 :=
    mul_le_mul_of_nonneg_left hD (by positivity)
  have e2 : 3 / 100 * Δ * (1 + y + g) ^ 2 ≤ Δ * (1 - s * (1 + w1 * (1 + 3 * g))) := by
    have := mul_le_mul_of_nonneg_left (le_trans hB hsB) hΔ0.le; linarith
  have e3 : s * (w2 * S2 * (1 + L1) - w1 * S1 * (1 + L2)) ≥ s * (-(w1 * Δ * (1 + 3 * g))) :=
    mul_le_mul_of_nonneg_left hV hs0
  nlinarith

private lemma ss_coord2 (m ns : ℕ) (ds : ℝ) (j τ : ℕ) :
    gpt m ns ds j τ 2 = (1 - sig ns ds j) *
      (hLift (sig ns ds j) (ptL m ns j τ) (ptV m ns j τ) /
        (1 + hLift (sig ns ds j) (ptL m ns j τ) (ptV m ns j τ))) := rfl

private lemma ss_lift (s L V : ℝ) (hs : s < 1) (hc : 0 < 1 + cOf s * V)
    (hh : 0 < hLift s L V) :
    (1 - s) * (hLift s L V / (1 + hLift s L V)) = ((1 - s) * L - s * V) / (1 + L) := by
  have hs' : 0 < 1 - s := by linarith
  have hL : 0 < 1 + L := by
    unfold hLift at hh
    have := (div_pos_iff.mp hh)
    rcases this with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · linarith
    · linarith
  have e : 1 + hLift s L V = (1 + L) / (1 + cOf s * V) := by
    unfold hLift; field_simp; ring
  have hcs : (1 - s) * cOf s = s := by unfold cOf; field_simp
  have e2 : hLift s L V / ((1 + L) / (1 + cOf s * V)) = (L - cOf s * V) / (1 + L) := by
    unfold hLift
    rw [div_div_div_cancel_right₀ hc.ne']
  rw [e, e2, ← mul_div_assoc]
  congr 1
  linear_combination (-V) * hcs

private lemma ss_drop {m ns : ℕ} {ds : ℝ} (hA : Adm m ns ds) (j : ℕ) :
    ∀ n : ℕ, 3 / 2 * gP m ns * n ≤ Hh m ns j - Hh m ns (j + n) := by
  obtain ⟨hg0, -, -, -, -, -⟩ := J_spec hA
  have hm : 2 ≤ m := hA.1
  have hns : 1 ≤ ns := by
    rcases Nat.eq_zero_or_pos ns with h | h
    · have := hA.2.1; subst h; simp at this
    · exact h
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    have hs := (normalization m ns (j + n) hm).1
    have hd := (face_basic _ _ (class_trans m ns (j + n) hm hns).1).2.2.2.2.2.2.2.2.2.1
    have : 3 / 2 * gP m ns ≤ gP m ns * dJ m ns (j + n) := by
      unfold dJ; nlinarith
    rw [← add_assoc, hs]; push_cast; linarith

private lemma ss_wmono {m ns : ℕ} {ds : ℝ} (hA : Adm m ns ds) (j : ℕ) :
    ∀ d, j + d ≤ Jn m ns → wA m ns j ≤ wA m ns (j + d) := by
  have hmono := (w_envelope hA).2
  intro d
  induction d with
  | zero => intro _; simp
  | succ d ih =>
    intro hd
    have h1 := ih (by omega)
    have h2 := hmono (j + d) (by omega)
    rw [← add_assoc]; linarith

private lemma ss_env {m ns : ℕ} {ds : ℝ} (hA : Adm m ns ds) (k : ℕ) (hk : k < Jn m ns)
    (z : ℝ) (hz : 0 < z) (hzk : z ≤ Hh m ns k) : wA m ns k * z ≤ 6 := by
  obtain ⟨-, -, -, hJ, -, -⟩ := J_spec hA
  have hE := ((w_envelope hA).1 k hk.le).2
  have hH4 := (hJ k hk).2
  have hH : 0 < Hh m ns k := lt_of_lt_of_le hz hzk
  have h1 : 1 ≤ 4 / Hh m ns k := by rw [le_div_iff₀ hH]; linarith
  have h2 : (4 / Hh m ns k) ^ (17 / 20 : ℝ) ≤ 4 / Hh m ns k := by
    calc (4 / Hh m ns k) ^ (17 / 20 : ℝ) ≤ (4 / Hh m ns k) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le h1 (by norm_num)
      _ = _ := Real.rpow_one _
  have h3 : wA m ns k ≤ 6 / Hh m ns k := by
    unfold o0 at hE
    have : 3 / 2 * (4 / Hh m ns k) = 6 / Hh m ns k := by ring
    nlinarith
  have hw0 : 0 ≤ wA m ns k := by
    have := ((w_envelope hA).1 k hk.le).1; unfold o0 at this; linarith
  calc wA m ns k * z ≤ wA m ns k * Hh m ns k := mul_le_mul_of_nonneg_left hzk hw0
    _ ≤ 6 / Hh m ns k * Hh m ns k := mul_le_mul_of_nonneg_right h3 hH.le
    _ = 6 := by field_simp

/-- Equal `t` forces equal type and class. -/
private lemma ss_slot (m ns j j' τ τ' : ℕ) (hm : 2 ≤ m) (hns : 1 ≤ ns) (hτ : τ < 4)
    (hτ' : τ' < 4) (h : ptT m ns j τ = ptT m ns j' τ') : τ = τ' ∧ cls m ns j = cls m ns j' := by
  have hG := (class_trans m ns j hm hns).1
  have hG' := (class_trans m ns j' hm hns).1
  obtain ⟨hd0, hd5, hu0, hu1⟩ := hG
  obtain ⟨-, -, hu0', hu1'⟩ := hG'
  have hd : 0 < dlt m := by unfold dlt; positivity
  have key : ∀ a b : ℕ, (a : ℝ) * dlt m = (b : ℝ) * dlt m → a = b := by
    intro a b hab
    have := mul_right_cancel₀ hd.ne' hab
    exact_mod_cast this
  have eu : uOf m ns j = 2 * (cls m ns j : ℝ) * dlt m := rfl
  have eu' : uOf m ns j' = 2 * (cls m ns j' : ℝ) * dlt m := rfl
  unfold ptT at h
  interval_cases τ <;> interval_cases τ' <;> simp only [fa', fa, fb', fb] at h <;>
    norm_num at h ⊢
  all_goals first
    | (exfalso; nlinarith)
    | (have := key (2 * cls m ns j + 1) (2 * cls m ns j') (by push_cast; nlinarith); omega)
    | (have := key (2 * cls m ns j) (2 * cls m ns j' + 1) (by push_cast; nlinarith); omega)
    | (have := key (2 * cls m ns j) (2 * cls m ns j') (by push_cast; nlinarith); omega)

private lemma ss_ebound {m ns : ℕ} {ds : ℝ} (hA : Adm m ns ds) (j τ : ℕ) :
    -3 * gP m ns ≤ (if τ < 2 then SA m ns j else SB m ns j) - ptL m ns j τ := by
  have hm : 2 ≤ m := hA.1
  have hns : 1 ≤ ns := by
    rcases Nat.eq_zero_or_pos ns with h | h
    · have := hA.2.1; subst h; simp at this
    · exact h
  obtain ⟨hg0, -, -, -, -, -⟩ := J_spec hA
  obtain ⟨he0, he1, -, -, -, -, ha1, hb1, -, -, -, -, -⟩ :=
    face_basic _ _ (class_trans m ns j hm hns).1
  have eps1 : epsJ m ns j = feps (uOf m ns j) (dlt m) := rfl
  have al1 : alJ m ns j 1 = falpha (uOf m ns j) (dlt m) 1 := rfl
  have be1 : beJ m ns j 1 = fbeta (uOf m ns j) (dlt m) 1 := rfl
  have p1 : -2 * gP m ns ≤ gP m ns * alJ m ns j 1 := by rw [al1]; nlinarith
  have p2 : -2 * gP m ns ≤ gP m ns * beJ m ns j 1 := by rw [be1]; nlinarith
  have p3 : gP m ns * epsJ m ns j ≤ gP m ns := by rw [eps1]; nlinarith
  have p4 : 0 ≤ gP m ns * epsJ m ns j := by rw [eps1]; positivity
  unfold SA SB ptL
  split_ifs <;> linarith

private lemma ss_ordered {m ns : ℕ} {ds : ℝ} (hA : Adm m ns ds) (h32 : 32 ≤ m ^ 2 * ns)
    (j1 j2 τ : ℕ) (hj2 : j2 < Jn m ns) (hτ : τ < 4) (hlt : j1 + ns * (m + 1) ≤ j2)
    (hcls : cls m ns j1 = cls m ns j2) (hmod : j1 % ns = j2 % ns) :
    9 / 500 * ((m : ℝ) + 1) / (m : ℝ) ^ 2 ≤ gpt m ns ds j1 τ 2 - gpt m ns ds j2 τ 2 := by
  have hm : 2 ≤ m := hA.1
  have hns : 1 ≤ ns := by
    rcases Nat.eq_zero_or_pos ns with h | h
    · have := hA.2.1; subst h; simp at this
    · exact h
  have hlt' : j1 < j2 := by
    have : 1 ≤ ns * (m + 1) := Nat.one_le_iff_ne_zero.mpr (by positivity)
    omega
  have hj1 : j1 < Jn m ns := by omega
  obtain ⟨hg0, -, -, hJ, -, -⟩ := J_spec hA
  have hmR : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hnsR : (1 : ℝ) ≤ ns := by exact_mod_cast hns
  have h32R : (32 : ℝ) ≤ (m : ℝ) ^ 2 * ns := by exact_mod_cast h32
  have hg : gP m ns ≤ 1 / 80 := by
    unfold gP; rw [div_le_iff₀ (by positivity)]; nlinarith
  have hsig : sig ns ds j2 = sig ns ds j1 := by unfold sig; rw [hmod]
  have hu : uOf m ns j1 = uOf m ns j2 := by unfold uOf; rw [hcls]
  obtain ⟨hs0, hs1, hcA1, hcB1, hVA1, hVB1, hh1⟩ := cw_bound hA j1 hj1
  obtain ⟨-, -, hcA2, hcB2, hVA2, hVB2, hh2⟩ := cw_bound hA j2 hj2
  rw [hsig] at hcA2 hcB2 hh2
  have hc0 : 0 ≤ cOf (sig ns ds j1) := by unfold cOf; apply div_nonneg hs0; linarith
  have hV1 : 1 < ptV m ns j1 τ := by unfold ptV; split_ifs <;> assumption
  have hV2 : 1 < ptV m ns j2 τ := by unfold ptV; split_ifs <;> assumption
  rw [ss_coord2, ss_coord2, hsig,
    ss_lift _ _ _ (by linarith) (by positivity) (hh1 τ hτ),
    ss_lift _ _ _ (by linarith) (by positivity) (hh2 τ hτ)]
  -- face data for the common class
  obtain ⟨he0, he1, -, -, -, -, ha1, hb1, -, -, hd21, -, -⟩ :=
    face_basic _ _ (class_trans m ns j1 hm hns).1
  have eps1 : epsJ m ns j1 = feps (uOf m ns j1) (dlt m) := rfl
  -- heights
  obtain ⟨hH1a, hH1b⟩ := hJ j1 hj1
  obtain ⟨hH2a, -⟩ := hJ j2 hj2
  have hge1 : 0 ≤ gP m ns * epsJ m ns j1 := mul_nonneg hg0.le (by rw [eps1]; exact he0.le)
  have hge1' : gP m ns * epsJ m ns j1 ≤ gP m ns := by
    rw [eps1]; nlinarith
  have hge2 : 0 ≤ gP m ns * epsJ m ns j2 := by
    rw [show epsJ m ns j2 = epsJ m ns j1 by unfold epsJ; rw [hu]]; exact hge1
  have hy1 : 1 ≤ Hh m ns j1 := by linarith
  have hH2 : 1 ≤ Hh m ns j2 := by linarith
  have hLd : ptL m ns j1 τ - Hh m ns j1 = ptL m ns j2 τ - Hh m ns j2 := by
    unfold ptL epsJ; rw [hu]; split_ifs <;> ring
  have hSd : (if τ < 2 then SA m ns j1 else SB m ns j1) - ptL m ns j1 τ =
      (if τ < 2 then SA m ns j2 else SB m ns j2) - ptL m ns j2 τ := by
    unfold SA SB alJ beJ ptL epsJ; rw [hu]; split_ifs <;> ring
  have hdrop := ss_drop hA j1 (j2 - j1)
  rw [show j1 + (j2 - j1) = j2 by omega] at hdrop
  have hcast : ((ns * (m + 1) : ℕ) : ℝ) ≤ ((j2 - j1 : ℕ) : ℝ) := by
    exact_mod_cast (by omega : ns * (m + 1) ≤ j2 - j1)
  push_cast at hcast
  have hΔ : 3 / 2 * gP m ns * ((ns : ℝ) * ((m : ℝ) + 1)) ≤ Hh m ns j1 - Hh m ns j2 := by
    have := mul_le_mul_of_nonneg_left hcast (by positivity : (0:ℝ) ≤ 3 / 2 * gP m ns)
    linarith
  have hval : 3 / 100 * (3 / 2 * gP m ns * ((ns : ℝ) * ((m : ℝ) + 1))) =
      9 / 500 * ((m : ℝ) + 1) / (m : ℝ) ^ 2 := by
    unfold gP; field_simp; ring
  have hΔpos : 0 < 3 / 2 * gP m ns * ((ns : ℝ) * ((m : ℝ) + 1)) := by positivity
  -- states
  have hwB : ∀ j, wB m ns j = wA m ns (j + 1) := by
    intro j; unfold wB wA; rw [Finset.prod_range_succ]; ring
  have hwpos : ∀ j, j ≤ Jn m ns → 0 < wA m ns j := by
    intro j hj; have := ((w_envelope hA).1 j hj).1; unfold o0 at this; linarith
  have hVe1 : ptV m ns j1 τ = (if τ < 2 then wA m ns j1 else wB m ns j1) *
      (if τ < 2 then SA m ns j1 else SB m ns j1) := by
    unfold ptV VA VB; split_ifs <;> rfl
  have hVe2 : ptV m ns j2 τ = (if τ < 2 then wA m ns j2 else wB m ns j2) *
      (if τ < 2 then SA m ns j2 else SB m ns j2) := by
    unfold ptV VA VB; split_ifs <;> rfl
  rw [hVe1, hVe2]
  have hGL := (gadget_lines hA).1 j2 hj2
  have key := ss_core (sig ns ds j1) (Hh m ns j1) (gP m ns) (ptL m ns j1 τ) (ptL m ns j2 τ)
    (if τ < 2 then SA m ns j1 else SB m ns j1) (if τ < 2 then SA m ns j2 else SB m ns j2)
    (if τ < 2 then wA m ns j1 else wB m ns j1) (if τ < 2 then wA m ns j2 else wB m ns j2)
    hs0 hs1 hg0 hg hy1 hH1b
    (by unfold ptL; split_ifs <;> linarith)
    (by unfold ptL; split_ifs <;> linarith)
    (by linarith) hSd
    (ss_ebound hA j1 τ)
    (by split_ifs <;> linarith)
    (by split_ifs
        · exact hwpos j1 hj1.le
        · rw [hwB]; exact hwpos (j1 + 1) hj1)
    (by
      split_ifs
      · have := ss_wmono hA j1 (j2 - j1) (by omega)
        rwa [show j1 + (j2 - j1) = j2 by omega] at this
      · rw [hwB, hwB]
        have := ss_wmono hA (j1 + 1) (j2 - j1) (by omega)
        rwa [show j1 + 1 + (j2 - j1) = j2 + 1 by omega] at this)
    (by
      split_ifs
      · have := ss_env hA j1 hj1 (Hh m ns j1 - 3 * gP m ns) (by linarith) (by linarith)
        exact this
      · rw [hwB]
        have hstep := (normalization m ns j1 hm).1
        have hdJ : dJ m ns j1 < 21 / 10 := hd21
        have := ss_env hA (j1 + 1) (by omega) (Hh m ns j1 - 3 * gP m ns) (by linarith)
          (by
            rw [hstep]
            have := mul_le_mul_of_nonneg_left (show dJ m ns j1 ≤ 3 by linarith) hg0.le
            linarith)
        exact this)
  have hLL : ptL m ns j1 τ - ptL m ns j2 τ = Hh m ns j1 - Hh m ns j2 := by linarith
  rw [hLL] at key
  rw [← hval]
  have := mul_le_mul_of_nonneg_left hΔ (by norm_num : (0:ℝ) ≤ 3 / 100)
  linarith

/-- Same slice and same class, `j < j'`: the gadgets are at least `ns (m+1)` apart. -/
private lemma ss_gap (m ns j j' : ℕ) (hlt : j < j') (hmod : j % ns = j' % ns)
    (hcls : cls m ns j = cls m ns j') : j + ns * (m + 1) ≤ j' := by
  unfold cls at hcls
  have e1 := Nat.div_add_mod j ns
  have e2 := Nat.div_add_mod j' ns
  set q := j / ns
  set q' := j' / ns
  have hq : q < q' := by
    by_contra h
    push Not at h
    have := Nat.mul_le_mul_left ns h
    omega
  have hd : (m + 1) ∣ q' - q := by
    apply Nat.dvd_of_mod_eq_zero
    exact Nat.sub_mod_eq_zero_of_mod_eq hcls.symm
  have hle : m + 1 ≤ q' - q := Nat.le_of_dvd (by omega) hd
  have : ns * (q + (m + 1)) ≤ ns * q' := Nat.mul_le_mul_left ns (by omega)
  rw [mul_add] at this
  omega

/-- Separation, same slice and same `t`: the two gadgets are `≥ ns(m+1)` apart, so their
heights differ by `≥ ns(m+1) g (3/2)`, and the coordinate-2 gap is `≥ (3/100)` times that,
i.e. `≥ (9/500)(m+1)/m²`. -/
theorem sep_same_slot {m ns : ℕ} {ds : ℝ} (hA : Adm m ns ds) (h32 : 32 ≤ m ^ 2 * ns) :
    ∀ j j' τ τ', j < Jn m ns → j' < Jn m ns → τ < 4 → τ' < 4 → (j ≠ j' ∨ τ ≠ τ') →
      sig ns ds j = sig ns ds j' → ptT m ns j τ = ptT m ns j' τ' →
      ∃ k : Fin 4, 9 / 500 * ((m : ℝ) + 1) / (m : ℝ) ^ 2 ≤
        |gpt m ns ds j τ k - gpt m ns ds j' τ' k| := by
  intro j j' τ τ' hj hj' hτ hτ' hne hs ht
  have hm : 2 ≤ m := hA.1
  have hns : 1 ≤ ns := by
    rcases Nat.eq_zero_or_pos ns with h | h
    · have := hA.2.1; subst h; simp at this
    · exact h
  obtain ⟨hττ, hcls⟩ := ss_slot m ns j j' τ τ' hm hns hτ hτ' ht
  subst hττ
  have hjj : j ≠ j' := by
    rcases hne with h | h
    · exact h
    · exact absurd rfl h
  have hmod : j % ns = j' % ns := by
    unfold sig at hs
    have := mul_right_cancel₀ hA.2.2.1.ne' hs
    exact_mod_cast this
  refine ⟨2, ?_⟩
  rcases lt_or_gt_of_ne hjj with h | h
  · have := ss_ordered hA h32 j j' τ hj' hτ (ss_gap m ns j j' h hmod hcls) hcls hmod
    exact le_trans this (le_abs_self _)
  · have := ss_ordered hA h32 j' j τ hj hτ (ss_gap m ns j' j h hmod.symm hcls.symm)
      hcls.symm hmod.symm
    rw [abs_sub_comm]
    exact le_trans this (le_abs_self _)

end Q2CL
