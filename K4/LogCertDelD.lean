import K4.Defs

namespace K4

/-! Explicit tilts indexed by the erased separator `i = 4t + r` (clamped at `4J - 1`).
Three regimes: `t < b` (standard tilts `std (4t+r)`), `t = b` (the frozen block, with the
special separators), `t > b` (`std (4t+r+1)`, `v` lagging one block). Here
`H = 4J+8`, `G = 4J+4`, `d_t = J H + 1 + t (G + 2)`, `V_0 = v0 + 1`. -/

private def dd (J t : ℕ) : ℤ := (J : ℤ) * (4 * J + 8) + 1 + t * (4 * J + 6)

private def vz (J : ℕ) : ℤ := (J : ℤ) * (4 * J + 8) + 1 + J * (4 * J + 6) + 4 * J + 2

private def fu (J b t r : ℕ) : ℤ :=
  if t < b then
    (t : ℤ) * (4 * J + 8) +
      (if r = 0 then 5 - (4 * (J : ℤ) + 8) else if r = 1 then (1 : ℤ)
        else if r = 2 then (2 : ℤ) else (3 : ℤ))
  else if t = b then
    (t : ℤ) * (4 * J + 8) +
      (if r = 0 then 5 - (4 * (J : ℤ) + 8) else if r = 1 then (1 : ℤ)
        else if r = 2 then (3 : ℤ) else (5 : ℤ))
  else
    (t : ℤ) * (4 * J + 8) +
      (if r = 0 then (1 : ℤ) else if r = 1 then (2 : ℤ) else if r = 2 then (3 : ℤ) else (5 : ℤ))

private def fs (J b t r : ℕ) : ℤ :=
  if t < b then
    dd J t + (if r = 0 then (-1 : ℤ) else if r = 1 then (-1 : ℤ)
      else if r = 2 then 2 * (J : ℤ) + 2 else 4 * (J : ℤ) + 5)
  else if t = b then
    dd J t + (if r = 0 then (-1 : ℤ) else if r = 1 then 4 * (J : ℤ) + 3
      else 4 * (J : ℤ) + 5)
  else
    dd J t + (if r = 0 then (-1 : ℤ) else if r = 1 then 2 * (J : ℤ) + 2
      else 4 * (J : ℤ) + 5)

private def fv (J b t r : ℕ) : ℤ :=
  if t < b then
    vz J + t * (4 * J + 4) + (if r = 0 then (0 : ℤ) else if r = 1 then (0 : ℤ)
      else if r = 2 then 2 * (J : ℤ) + 2 else 4 * (J : ℤ) + 4)
  else if t = b then
    vz J + t * (4 * J + 4)
  else
    vz J + ((t : ℤ) - 1) * (4 * J + 4) + (if r = 0 then (0 : ℤ)
      else if r = 1 then 2 * (J : ℤ) + 2 else 4 * (J : ℤ) + 4)

private def qi (J i : ℕ) : ℕ := min i (4 * J - 1)

private lemma mono_of (J : ℕ) (F : ℕ → ℕ → ℤ) (h1 : ∀ t r, r < 3 → F t r ≤ F t (r + 1))
    (h2 : ∀ t, F t 3 ≤ F (t + 1) 0) :
    Monotone (fun i => F (qi J i / 4) (qi J i % 4)) := by
  apply monotone_nat_of_le_succ
  intro n
  by_cases hn : n < 4 * J - 1
  · have e1 : qi J n = n := by unfold qi; omega
    have e2 : qi J (n + 1) = n + 1 := by unfold qi; omega
    simp only [e1, e2]
    by_cases hr : n % 4 < 3
    · have a1 : (n + 1) / 4 = n / 4 := by omega
      have a2 : (n + 1) % 4 = n % 4 + 1 := by omega
      rw [a1, a2]; exact h1 _ _ hr
    · have a1 : (n + 1) / 4 = n / 4 + 1 := by omega
      have a2 : (n + 1) % 4 = 0 := by omega
      have a3 : n % 4 = 3 := by omega
      rw [a1, a2, a3]; exact h2 _
  · have e1 : qi J n = 4 * J - 1 := by unfold qi; omega
    have e2 : qi J (n + 1) = 4 * J - 1 := by unfold qi; omega
    simp only [e1, e2]; exact le_refl _

/-- Regime trichotomy, packaged for unfolding the `if`s. -/
private lemma regime (t b : ℕ) :
    (t < b ∧ ¬ t = b ∧ t + 1 ≤ b) ∨ (¬ t < b ∧ t = b ∧ t = b) ∨
      (¬ t < b ∧ ¬ t = b ∧ b < t) := by omega

private lemma mono_u (J b : ℕ) : Monotone (fun i => fu J b (qi J i / 4) (qi J i % 4)) := by
  apply mono_of J (fu J b)
  · intro t r hr
    rcases regime t b with ⟨h, h', h''⟩ | ⟨h, h', h''⟩ | ⟨h, h', h''⟩ <;>
      rcases (by omega : r = 0 ∨ r = 1 ∨ r = 2) with rfl | rfl | rfl <;>
      simp only [fu, h, h', ite_true, ite_false] <;> norm_num <;> nlinarith
  · intro t
    rcases regime t b with ⟨h, h', h''⟩ | ⟨h, h', h''⟩ | ⟨h, h', h''⟩
    · rcases regime (t + 1) b with ⟨g, g', g''⟩ | ⟨g, g', g''⟩ | ⟨g, g', g''⟩
      · simp only [fu, h, g, ite_true]; norm_num; push_cast; nlinarith
      · simp only [fu, h, g, g', ite_true, ite_false]; norm_num; push_cast; nlinarith
      · omega
    · have g : ¬ t + 1 < b := by omega
      have g' : ¬ t + 1 = b := by omega
      simp only [fu, h, h', g, g', ite_true, ite_false]; norm_num; push_cast; nlinarith
    · have g : ¬ t + 1 < b := by omega
      have g' : ¬ t + 1 = b := by omega
      simp only [fu, h, h', g, g', ite_true, ite_false]; norm_num; push_cast; nlinarith

private lemma mono_s (J b : ℕ) : Monotone (fun i => fs J b (qi J i / 4) (qi J i % 4)) := by
  apply mono_of J (fs J b)
  · intro t r hr
    rcases regime t b with ⟨h, h', h''⟩ | ⟨h, h', h''⟩ | ⟨h, h', h''⟩ <;>
      rcases (by omega : r = 0 ∨ r = 1 ∨ r = 2) with rfl | rfl | rfl <;>
      simp only [fs, h, h', ite_true, ite_false] <;> norm_num <;> nlinarith
  · intro t
    rcases regime t b with ⟨h, h', h''⟩ | ⟨h, h', h''⟩ | ⟨h, h', h''⟩
    · rcases regime (t + 1) b with ⟨g, g', g''⟩ | ⟨g, g', g''⟩ | ⟨g, g', g''⟩
      · simp only [fs, dd, h, g, ite_true]; norm_num; push_cast; nlinarith
      · simp only [fs, dd, h, g, g', ite_true, ite_false]; norm_num; push_cast; nlinarith
      · omega
    · have g : ¬ t + 1 < b := by omega
      have g' : ¬ t + 1 = b := by omega
      simp only [fs, dd, h, h', g, g', ite_true, ite_false]; norm_num; push_cast; nlinarith
    · have g : ¬ t + 1 < b := by omega
      have g' : ¬ t + 1 = b := by omega
      simp only [fs, dd, h, h', g, g', ite_true, ite_false]; norm_num; push_cast; nlinarith

private lemma mono_v (J b : ℕ) : Monotone (fun i => fv J b (qi J i / 4) (qi J i % 4)) := by
  apply mono_of J (fv J b)
  · intro t r hr
    rcases regime t b with ⟨h, h', h''⟩ | ⟨h, h', h''⟩ | ⟨h, h', h''⟩ <;>
      rcases (by omega : r = 0 ∨ r = 1 ∨ r = 2) with rfl | rfl | rfl <;>
      simp only [fv, h, h', ite_true, ite_false] <;> norm_num <;> nlinarith
  · intro t
    rcases regime t b with ⟨h, h', h''⟩ | ⟨h, h', h''⟩ | ⟨h, h', h''⟩
    · rcases regime (t + 1) b with ⟨g, g', g''⟩ | ⟨g, g', g''⟩ | ⟨g, g', g''⟩
      · simp only [fv, h, g, ite_true]; norm_num; push_cast; nlinarith
      · simp only [fv, h, g, g', ite_true, ite_false]; norm_num; push_cast; nlinarith
      · omega
    · have g : ¬ t + 1 < b := by omega
      have g' : ¬ t + 1 = b := by omega
      subst h'
      simp only [fv, h, g, g', ite_true, ite_false]; norm_num
    · have g : ¬ t + 1 < b := by omega
      have g' : ¬ t + 1 = b := by omega
      simp only [fv, h, h', g, g', ite_true, ite_false]; norm_num; push_cast; nlinarith

private lemma mono_w (J b : ℕ) : Monotone (fun i =>
    fu J b (qi J i / 4) (qi J i % 4) + fv J b (qi J i / 4) (qi J i % 4) -
      fs J b (qi J i / 4) (qi J i % 4)) := by
  apply mono_of J (fun t r => fu J b t r + fv J b t r - fs J b t r)
  · intro t r hr
    rcases regime t b with ⟨h, h', h''⟩ | ⟨h, h', h''⟩ | ⟨h, h', h''⟩ <;>
      rcases (by omega : r = 0 ∨ r = 1 ∨ r = 2) with rfl | rfl | rfl <;>
      simp only [fu, fs, fv, h, h', ite_true, ite_false] <;> norm_num <;> nlinarith
  · intro t
    rcases regime t b with ⟨h, h', h''⟩ | ⟨h, h', h''⟩ | ⟨h, h', h''⟩
    · rcases regime (t + 1) b with ⟨g, g', g''⟩ | ⟨g, g', g''⟩ | ⟨g, g', g''⟩
      · simp only [fu, fs, fv, dd, h, g, ite_true]; norm_num; push_cast; nlinarith
      · simp only [fu, fs, fv, dd, h, g, g', ite_true, ite_false]; norm_num; push_cast; nlinarith
      · omega
    · have g : ¬ t + 1 < b := by omega
      have g' : ¬ t + 1 = b := by omega
      simp only [fu, fs, fv, dd, h, h', g, g', ite_true, ite_false]; norm_num; push_cast
      subst h'; nlinarith
    · have g : ¬ t + 1 < b := by omega
      have g' : ¬ t + 1 = b := by omega
      simp only [fu, fs, fv, dd, h, h', g, g', ite_true, ite_false]; norm_num; push_cast; nlinarith

private lemma bounds (J b t r : ℕ) (hJ : 1 ≤ J) (hr : r < 4) (ht : 4 * t + r ≤ 4 * J - 1) :
    fu J b t r < fs J b t r ∧ fs J b t r < fv J b t r := by
  have htJ : (t : ℤ) + 1 ≤ J := by omega
  have hJ1 : (1 : ℤ) ≤ J := by exact_mod_cast hJ
  have ht0 : (0 : ℤ) ≤ t := by positivity
  have hm : (t : ℤ) * J + J ≤ (J : ℤ) * J := by nlinarith
  rcases regime t b with ⟨h, h', h''⟩ | ⟨h, h', h''⟩ | ⟨h, h', h''⟩ <;>
    rcases (by omega : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3) with rfl | rfl | rfl | rfl <;>
    simp only [fu, fs, fv, dd, vz, h, h', ite_true, ite_false] <;> norm_num <;>
    constructor <;> nlinarith

/-! Kinds and exponents of the original list. -/

private lemma e0 (J : ℕ) :
    rtKind J 0 = EK.R ∧ (rtExp J 0 : ℤ) = vz J - 1 := by
  refine ⟨?_, ?_⟩
  · rw [rtKind, if_pos rfl]
  · rw [rtExp, if_pos rfl]
    simp only [vz, parV0, parD, parH, parG]; push_cast; ring

private lemma e1 (J t : ℕ) (ht : t < J) :
    rtKind J (4 * t + 1) = EK.P ∧ (rtExp J (4 * t + 1) : ℤ) = t * (4 * J + 8) := by
  have h0 : ¬ (4 * t + 1 = 0) := by omega
  have h1 : ¬ (4 * t + 1 = 4 * J + 1) := by omega
  have hm : (4 * t + 1 - 1) % 4 = 0 := by omega
  have hd : (4 * t + 1 - 1) / 4 = t := by omega
  refine ⟨?_, ?_⟩
  · rw [rtKind, if_neg h0, if_neg h1, if_pos hm]
  · rw [rtExp, if_neg h0, if_neg h1, if_pos hm, hd]
    simp only [expA, parH]; push_cast; ring

private lemma e2 (J t : ℕ) (ht : t < J) :
    rtKind J (4 * t + 2) = EK.Q ∧ (rtExp J (4 * t + 2) : ℤ) = dd J t := by
  have h0 : ¬ (4 * t + 2 = 0) := by omega
  have h1 : ¬ (4 * t + 2 = 4 * J + 1) := by omega
  have m0 : ¬ ((4 * t + 2 - 1) % 4 = 0) := by omega
  have m3 : ¬ ((4 * t + 2 - 1) % 4 = 3) := by omega
  have hm : (4 * t + 2 - 1) % 4 = 1 := by omega
  have hd : (4 * t + 2 - 1) / 4 = t := by omega
  refine ⟨?_, ?_⟩
  · rw [rtKind, if_neg h0, if_neg h1, if_neg m0, if_neg m3]
  · rw [rtExp, if_neg h0, if_neg h1, if_neg m0, if_pos hm, hd]
    simp only [dd, expD, parD, parH, parG]; push_cast; ring

private lemma e3 (J t : ℕ) (ht : t < J) :
    rtKind J (4 * t + 3) = EK.Q ∧ (rtExp J (4 * t + 3) : ℤ) = dd J t + (4 * J + 4) := by
  have h0 : ¬ (4 * t + 3 = 0) := by omega
  have h1 : ¬ (4 * t + 3 = 4 * J + 1) := by omega
  have m0 : ¬ ((4 * t + 3 - 1) % 4 = 0) := by omega
  have m1 : ¬ ((4 * t + 3 - 1) % 4 = 1) := by omega
  have m3 : ¬ ((4 * t + 3 - 1) % 4 = 3) := by omega
  have hm : (4 * t + 3 - 1) % 4 = 2 := by omega
  have hd : (4 * t + 3 - 1) / 4 = t := by omega
  refine ⟨?_, ?_⟩
  · rw [rtKind, if_neg h0, if_neg h1, if_neg m0, if_neg m3]
  · rw [rtExp, if_neg h0, if_neg h1, if_neg m0, if_neg m1, if_pos hm, hd]
    simp only [dd, expD, parD, parH, parG]; push_cast; ring

private lemma e4 (J t : ℕ) (ht : t < J) :
    rtKind J (4 * t + 4) = EK.P ∧ (rtExp J (4 * t + 4) : ℤ) = t * (4 * J + 8) + 4 := by
  have h0 : ¬ (4 * t + 4 = 0) := by omega
  have h1 : ¬ (4 * t + 4 = 4 * J + 1) := by omega
  have m0 : ¬ ((4 * t + 4 - 1) % 4 = 0) := by omega
  have m1 : ¬ ((4 * t + 4 - 1) % 4 = 1) := by omega
  have m2 : ¬ ((4 * t + 4 - 1) % 4 = 2) := by omega
  have hm : (4 * t + 4 - 1) % 4 = 3 := by omega
  have hd : (4 * t + 4 - 1) / 4 = t := by omega
  refine ⟨?_, ?_⟩
  · rw [rtKind, if_neg h0, if_neg h1, if_neg m0, if_pos hm]
  · rw [rtExp, if_neg h0, if_neg h1, if_neg m0, if_neg m1, if_neg m2, hd]
    simp only [expA, parH, parG_small]; push_cast; ring

private lemma e5 (J t : ℕ) (ht : t + 1 = J) :
    rtKind J (4 * t + 5) = EK.R ∧
      (rtExp J (4 * t + 5) : ℤ) = vz J - 1 + J * (4 * J) := by
  have h0 : ¬ (4 * t + 5 = 0) := by omega
  have h1 : 4 * t + 5 = 4 * J + 1 := by omega
  refine ⟨?_, ?_⟩
  · rw [rtKind, if_neg h0, if_pos h1]
  · rw [rtExp, if_neg h0, if_pos h1]
    simp only [vz, parV0, parD, parH, parG, parBeta]; push_cast; ring

/-- Original index `4t` (the gap before block `t`, `t < J`): above side of separator `4t`. -/
private lemma gapAbove (J t : ℕ) (ht : t < J) (u s v : ℤ)
    (h0 : t = 0 → vz J - 1 < v) (h1 : 0 < t → (t : ℤ) * (4 * J + 8) - (4 * J + 8) + 4 < u) :
    (rtExp J (4 * t) : ℤ) < ekSel (rtKind J (4 * t)) u s v := by
  rcases Nat.eq_zero_or_pos t with rfl | hpos
  · obtain ⟨k, x⟩ := e0 J
    simp only [Nat.mul_zero]; rw [k, x]; exact h0 rfl
  · obtain ⟨k, x⟩ := e4 J (t - 1) (by omega)
    rw [show 4 * (t - 1) + 4 = 4 * t by omega] at k x
    rw [k, x]; simp only [ekSel]
    have := h1 hpos
    push_cast [Nat.cast_sub (show 1 ≤ t by omega)] at this ⊢
    nlinarith

/-- Original index `4t + 5` (next block start or final `R`), below side. -/
private lemma nextBelow (J t : ℕ) (ht : t < J) (u s v : ℤ)
    (h0 : t + 1 = J → v < vz J - 1 + J * (4 * J))
    (h1 : t + 1 < J → u < ((t : ℤ) + 1) * (4 * J + 8)) :
    ekSel (rtKind J (4 * t + 5)) u s v < (rtExp J (4 * t + 5) : ℤ) := by
  by_cases hl : t + 1 = J
  · obtain ⟨k, x⟩ := e5 J t hl
    rw [k, x]; exact h0 hl
  · obtain ⟨k, x⟩ := e1 J (t + 1) (by omega)
    rw [show 4 * (t + 1) + 1 = 4 * t + 5 by ring] at k x
    rw [k, x]; simp only [ekSel]; push_cast; exact h1 (by omega)

private lemma sep (J b t r : ℕ) (hb : b < J) (hr : r < 4) (ht : t < J) :
    ((rtExp J (skipIdx (4 * b + 2) (4 * t + r)) : ℤ) <
        ekSel (rtKind J (skipIdx (4 * b + 2) (4 * t + r))) (fu J b t r) (fs J b t r)
          (fv J b t r)) ∧
      (ekSel (rtKind J (skipIdx (4 * b + 2) (4 * t + r + 1))) (fu J b t r) (fs J b t r)
          (fv J b t r) < (rtExp J (skipIdx (4 * b + 2) (4 * t + r + 1)) : ℤ)) := by
  have hJ1 : (1 : ℤ) ≤ J := by omega
  have htJ : (t : ℤ) + 1 ≤ J := by omega
  have ht0 : (0 : ℤ) ≤ t := by positivity
  rcases regime t b with ⟨h, h', h''⟩ | ⟨h, h', h''⟩ | ⟨h, h', h''⟩
  · -- standard regime
    rcases (by omega : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3) with rfl | rfl | rfl | rfl
    · rw [show skipIdx (4 * b + 2) (4 * t + 0) = 4 * t by unfold skipIdx; split_ifs <;> omega,
        show skipIdx (4 * b + 2) (4 * t + 0 + 1) = 4 * t + 1 by
          unfold skipIdx; split_ifs <;> omega]
      obtain ⟨k2, x2⟩ := e1 J t ht
      refine ⟨gapAbove J t ht _ _ _ ?_ ?_, ?_⟩
      · intro _; simp only [fv, h, ite_true]; norm_num; nlinarith
      · intro _; simp only [fu, h, ite_true]; norm_num; nlinarith
      · rw [k2, x2]; simp only [ekSel, fu, h, ite_true]; norm_num; nlinarith
    · rw [show skipIdx (4 * b + 2) (4 * t + 1) = 4 * t + 1 by unfold skipIdx; split_ifs <;> omega,
        show skipIdx (4 * b + 2) (4 * t + 1 + 1) = 4 * t + 2 by
          unfold skipIdx; split_ifs <;> omega]
      obtain ⟨k1, x1⟩ := e1 J t ht
      obtain ⟨k2, x2⟩ := e2 J t ht
      rw [k1, x1, k2, x2]; simp only [ekSel, fu, fs, h, ite_true]; norm_num
    · rw [show skipIdx (4 * b + 2) (4 * t + 2) = 4 * t + 2 by unfold skipIdx; split_ifs <;> omega,
        show skipIdx (4 * b + 2) (4 * t + 2 + 1) = 4 * t + 3 by
          unfold skipIdx; split_ifs <;> omega]
      obtain ⟨k1, x1⟩ := e2 J t ht
      obtain ⟨k2, x2⟩ := e3 J t ht
      rw [k1, x1, k2, x2]; simp only [ekSel, fs, h, ite_true]; norm_num
      constructor <;> nlinarith
    · rw [show skipIdx (4 * b + 2) (4 * t + 3) = 4 * t + 3 by unfold skipIdx; split_ifs <;> omega,
        show skipIdx (4 * b + 2) (4 * t + 3 + 1) = 4 * t + 4 by
          unfold skipIdx; split_ifs <;> omega]
      obtain ⟨k1, x1⟩ := e3 J t ht
      obtain ⟨k2, x2⟩ := e4 J t ht
      rw [k1, x1, k2, x2]; simp only [ekSel, fu, fs, h, ite_true]; norm_num
  · -- frozen block
    subst h'
    rcases (by omega : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3) with rfl | rfl | rfl | rfl
    · rw [show skipIdx (4 * t + 2) (4 * t + 0) = 4 * t by unfold skipIdx; split_ifs <;> omega,
        show skipIdx (4 * t + 2) (4 * t + 0 + 1) = 4 * t + 1 by
          unfold skipIdx; split_ifs <;> omega]
      obtain ⟨k2, x2⟩ := e1 J t ht
      refine ⟨gapAbove J t ht _ _ _ ?_ ?_, ?_⟩
      · intro _; simp only [fv, h, ite_true, ite_false]; norm_num; nlinarith
      · intro _; simp only [fu, h, ite_true, ite_false]; norm_num; nlinarith
      · rw [k2, x2]; simp only [ekSel, fu, h, ite_true, ite_false]; norm_num; nlinarith
    · rw [show skipIdx (4 * t + 2) (4 * t + 1) = 4 * t + 1 by unfold skipIdx; split_ifs <;> omega,
        show skipIdx (4 * t + 2) (4 * t + 1 + 1) = 4 * t + 3 by
          unfold skipIdx; split_ifs <;> omega]
      obtain ⟨k1, x1⟩ := e1 J t ht
      obtain ⟨k2, x2⟩ := e3 J t ht
      rw [k1, x1, k2, x2]; simp only [ekSel, fu, fs, h, ite_true, ite_false]; norm_num
    · rw [show skipIdx (4 * t + 2) (4 * t + 2) = 4 * t + 3 by unfold skipIdx; split_ifs <;> omega,
        show skipIdx (4 * t + 2) (4 * t + 2 + 1) = 4 * t + 4 by
          unfold skipIdx; split_ifs <;> omega]
      obtain ⟨k1, x1⟩ := e3 J t ht
      obtain ⟨k2, x2⟩ := e4 J t ht
      rw [k1, x1, k2, x2]; simp only [ekSel, fu, fs, h, ite_true, ite_false]; norm_num
    · rw [show skipIdx (4 * t + 2) (4 * t + 3) = 4 * t + 4 by unfold skipIdx; split_ifs <;> omega,
        show skipIdx (4 * t + 2) (4 * t + 3 + 1) = 4 * t + 5 by
          unfold skipIdx; split_ifs <;> omega]
      obtain ⟨k1, x1⟩ := e4 J t ht
      refine ⟨?_, nextBelow J t ht _ _ _ ?_ ?_⟩
      · rw [k1, x1]; simp only [ekSel, fu, h, ite_true, ite_false]; norm_num
      · intro hl
        have : (t : ℤ) + 1 = J := by exact_mod_cast hl
        simp only [fv, h, ite_true, ite_false]; nlinarith
      · intro _; simp only [fu, h, ite_true, ite_false]; norm_num; nlinarith
  · -- after the frozen block
    rcases (by omega : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3) with rfl | rfl | rfl | rfl
    · rw [show skipIdx (4 * b + 2) (4 * t + 0) = 4 * t + 1 by unfold skipIdx; split_ifs <;> omega,
        show skipIdx (4 * b + 2) (4 * t + 0 + 1) = 4 * t + 2 by
          unfold skipIdx; split_ifs <;> omega]
      obtain ⟨k1, x1⟩ := e1 J t ht
      obtain ⟨k2, x2⟩ := e2 J t ht
      rw [k1, x1, k2, x2]; simp only [ekSel, fu, fs, h, h', ite_true, ite_false]; norm_num
    · rw [show skipIdx (4 * b + 2) (4 * t + 1) = 4 * t + 2 by unfold skipIdx; split_ifs <;> omega,
        show skipIdx (4 * b + 2) (4 * t + 1 + 1) = 4 * t + 3 by
          unfold skipIdx; split_ifs <;> omega]
      obtain ⟨k1, x1⟩ := e2 J t ht
      obtain ⟨k2, x2⟩ := e3 J t ht
      rw [k1, x1, k2, x2]; simp only [ekSel, fs, h, h', ite_true, ite_false]; norm_num
      constructor <;> nlinarith
    · rw [show skipIdx (4 * b + 2) (4 * t + 2) = 4 * t + 3 by unfold skipIdx; split_ifs <;> omega,
        show skipIdx (4 * b + 2) (4 * t + 2 + 1) = 4 * t + 4 by
          unfold skipIdx; split_ifs <;> omega]
      obtain ⟨k1, x1⟩ := e3 J t ht
      obtain ⟨k2, x2⟩ := e4 J t ht
      rw [k1, x1, k2, x2]; simp only [ekSel, fu, fs, h, h', ite_true, ite_false]; norm_num
    · rw [show skipIdx (4 * b + 2) (4 * t + 3) = 4 * t + 4 by unfold skipIdx; split_ifs <;> omega,
        show skipIdx (4 * b + 2) (4 * t + 3 + 1) = 4 * t + 5 by
          unfold skipIdx; split_ifs <;> omega]
      obtain ⟨k1, x1⟩ := e4 J t ht
      refine ⟨?_, nextBelow J t ht _ _ _ ?_ ?_⟩
      · rw [k1, x1]; simp only [ekSel, fu, h, h', ite_true, ite_false]; norm_num
      · intro hl
        have : (t : ℤ) + 1 = J := by exact_mod_cast hl
        simp only [fv, h, h', ite_true, ite_false]; norm_num; nlinarith
      · intro _; simp only [fu, h, h', ite_true, ite_false]; norm_num; nlinarith

/-- Deletion of `D_b = Q[d_b]` (position `4b+2`).
Notation and `V_t` (block `b` frozen, `V_0 = v0 + 1`) as in `logCert_delA`.
Erased separators: `i ≤ 4b ↦ std i`; `i = 4b+1 ↦ (a_b + 1, d_b + G - 1, V_b)` (separates
`A_b` from `D'_b`); `i = 4b+2 ↦ (a_b + 3, d_b + G + 1, V_b)`; `i ≥ 4b+3 ↦ std (i + 1)`;
clamp `i ≥ 4J` to `4J - 1`.
Checks: `i = 4b+1`: `u > a_b`, `s < d_b + G`. `i = 4b+2`: `s > d_b + G`, `u < a_b + 4`.
Steps: from `std (4b) = (a_{b-1} + 5, d_b - 1, V_b)` (for `b = 0`: `(5 - h, D - 1, V_0)`):
`(h - 4, G, 0) = (G, G, 0)`; then `(2, 2, 0)`; then `(2, 0, 0)` into `std (4b+4)`.
Final `v = v0 + 4J² - 3 < V1`. -/
theorem logCert_delD (J b : ℕ) (hb : b < J) :
    ∃ u s v w : ℕ → ℤ, LogCert J (4 * b + 2) u s v w := by
  have hJ : 1 ≤ J := by omega
  refine ⟨fun i => fu J b (qi J i / 4) (qi J i % 4), fun i => fs J b (qi J i / 4) (qi J i % 4),
    fun i => fv J b (qi J i / 4) (qi J i % 4),
    fun i => fu J b (qi J i / 4) (qi J i % 4) + fv J b (qi J i / 4) (qi J i % 4) -
      fs J b (qi J i / 4) (qi J i % 4),
    mono_u J b, mono_s J b, mono_v J b, mono_w J b, ?_, ?_, ?_⟩
  · intro i; ring
  · intro i
    exact bounds J b _ _ hJ (Nat.mod_lt _ (by norm_num)) (by unfold qi; omega)
  · intro i hi
    have hq : qi J i = i := by unfold qi; omega
    simp only [hq]
    have key := sep J b (i / 4) (i % 4) hb (Nat.mod_lt _ (by norm_num)) (by omega)
    rw [show 4 * (i / 4) + i % 4 = i by omega] at key
    exact key

end K4
