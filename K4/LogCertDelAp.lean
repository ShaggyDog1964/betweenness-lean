import K4.Defs

namespace K4

/-! Standard tilts at original separator `p = 4t + r`, `V_t = v0 + 1 + t G`
(same as in `K4.LogCertDelA`). -/

private def su (J t r : ℕ) : ℤ :=
  (t : ℤ) * (4 * J + 8) +
    (if r = 0 then -(4 * (J : ℤ) + 3) else if r = 1 then (1 : ℤ) else if r = 2 then (2 : ℤ)
      else (3 : ℤ))

private def ss (J t r : ℕ) : ℤ :=
  (J : ℤ) * (4 * J + 8) + 1 + t * (4 * J + 6) +
    (if r = 0 then (-1 : ℤ) else if r = 1 then (-1 : ℤ) else if r = 2 then 2 * (J : ℤ) + 2
      else 4 * (J : ℤ) + 5)

private def sv (J t r : ℕ) : ℤ :=
  (J : ℤ) * (4 * J + 8) + 1 + J * (4 * J + 6) + 4 * J + 2 + t * (4 * J + 4) +
    (if r = 0 then (0 : ℤ) else if r = 1 then (0 : ℤ) else if r = 2 then 2 * (J : ℤ) + 2
      else 4 * (J : ℤ) + 4)

/-! Frozen tilts at erased index `q`. -/

private def fu (J b q : ℕ) : ℤ :=
  if q ≤ 4 * b + 1 then su J (q / 4) (q % 4)
  else if q = 4 * b + 2 then (b : ℤ) * (4 * J + 8) + (2 * J + 4)
  else if q = 4 * b + 3 then (b : ℤ) * (4 * J + 8) + (4 * J + 7)
  else su J ((q + 1) / 4) ((q + 1) % 4)

private def fs (J b q : ℕ) : ℤ :=
  if q ≤ 4 * b + 1 then ss J (q / 4) (q % 4)
  else if q = 4 * b + 2 then (J : ℤ) * (4 * J + 8) + 1 + b * (4 * J + 6) + (2 * J + 2)
  else if q = 4 * b + 3 then (J : ℤ) * (4 * J + 8) + 1 + b * (4 * J + 6) + (4 * J + 5)
  else ss J ((q + 1) / 4) ((q + 1) % 4)

private def fv (J b q : ℕ) : ℤ :=
  if q ≤ 4 * b + 1 then sv J (q / 4) (q % 4)
  else if q = 4 * b + 2 then sv J b 0
  else if q = 4 * b + 3 then sv J b 0
  else sv J ((q + 1) / 4) ((q + 1) % 4) - (4 * J + 4)

private def qi (J i : ℕ) : ℕ := min i (4 * J - 1)

private lemma std_step (J p : ℕ) :
    su J (p / 4) (p % 4) ≤ su J ((p + 1) / 4) ((p + 1) % 4) ∧
    ss J (p / 4) (p % 4) ≤ ss J ((p + 1) / 4) ((p + 1) % 4) ∧
    sv J (p / 4) (p % 4) ≤ sv J ((p + 1) / 4) ((p + 1) % 4) ∧
    su J (p / 4) (p % 4) + sv J (p / 4) (p % 4) - ss J (p / 4) (p % 4) ≤
      su J ((p + 1) / 4) ((p + 1) % 4) + sv J ((p + 1) / 4) ((p + 1) % 4) -
        ss J ((p + 1) / 4) ((p + 1) % 4) := by
  have hJ : (0 : ℤ) ≤ J := by positivity
  rcases (by omega : p % 4 = 0 ∨ p % 4 = 1 ∨ p % 4 = 2 ∨ p % 4 = 3) with h | h | h | h
  · have a1 : (p + 1) / 4 = p / 4 := by omega
    have a2 : (p + 1) % 4 = 1 := by omega
    rw [a1, a2, h]
    refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [su, ss, sv] <;> norm_num <;> linarith
  · have a1 : (p + 1) / 4 = p / 4 := by omega
    have a2 : (p + 1) % 4 = 2 := by omega
    rw [a1, a2, h]
    refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [su, ss, sv] <;> norm_num <;> linarith
  · have a1 : (p + 1) / 4 = p / 4 := by omega
    have a2 : (p + 1) % 4 = 3 := by omega
    rw [a1, a2, h]
    refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [su, ss, sv] <;> norm_num <;> linarith
  · have a1 : (p + 1) / 4 = p / 4 + 1 := by omega
    have a2 : (p + 1) % 4 = 0 := by omega
    rw [a1, a2, h]
    refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [su, ss, sv] <;> push_cast <;> norm_num <;> linarith

private lemma f_step (J b n : ℕ) :
    fu J b n ≤ fu J b (n + 1) ∧ fs J b n ≤ fs J b (n + 1) ∧ fv J b n ≤ fv J b (n + 1) ∧
    fu J b n + fv J b n - fs J b n ≤ fu J b (n + 1) + fv J b (n + 1) - fs J b (n + 1) := by
  have hJ : (0 : ℤ) ≤ J := by positivity
  have hb0 : (0 : ℤ) ≤ b := by positivity
  by_cases h1 : n + 1 ≤ 4 * b + 1
  · have c1 : n ≤ 4 * b + 1 := by omega
    simp only [fu, fs, fv, if_pos h1, if_pos c1]
    exact std_step J n
  by_cases h2 : n = 4 * b + 1
  · subst h2
    have c1 : ¬ (4 * b + 1 + 1 ≤ 4 * b + 1) := by omega
    have c2 : 4 * b + 1 + 1 = 4 * b + 2 := by omega
    have d1 : (4 * b + 1) / 4 = b := by omega
    have d2 : (4 * b + 1) % 4 = 1 := by omega
    simp only [fu, fs, fv, if_pos (le_refl (4 * b + 1)), if_neg c1, c2, d1, d2, if_true]
    refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [su, ss, sv] <;> norm_num <;> linarith
  by_cases h3 : n = 4 * b + 2
  · subst h3
    have c1 : ¬ (4 * b + 2 ≤ 4 * b + 1) := by omega
    have c2 : ¬ (4 * b + 2 + 1 ≤ 4 * b + 1) := by omega
    have c3 : ¬ (4 * b + 2 + 1 = 4 * b + 2) := by omega
    have c4 : 4 * b + 2 + 1 = 4 * b + 3 := by omega
    simp only [fu, fs, fv, if_neg c1, if_neg c2, if_neg c3, c4, if_true]
    refine ⟨?_, ?_, ?_, ?_⟩ <;> norm_num <;> linarith
  by_cases h4 : n = 4 * b + 3
  · subst h4
    have c1 : ¬ (4 * b + 3 ≤ 4 * b + 1) := by omega
    have c2 : ¬ (4 * b + 3 = 4 * b + 2) := by omega
    have c3 : ¬ (4 * b + 3 + 1 ≤ 4 * b + 1) := by omega
    have c4 : ¬ (4 * b + 3 + 1 = 4 * b + 2) := by omega
    have c5 : ¬ (4 * b + 3 + 1 = 4 * b + 3) := by omega
    have d1 : (4 * b + 3 + 1 + 1) / 4 = b + 1 := by omega
    have d2 : (4 * b + 3 + 1 + 1) % 4 = 1 := by omega
    simp only [fu, fs, fv, if_neg c1, if_neg c2, if_neg c3, if_neg c4, if_neg c5, d1, d2,
      if_true]
    refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [su, ss, sv] <;> push_cast <;> norm_num <;> linarith
  · have c1 : ¬ (n ≤ 4 * b + 1) := by omega
    have c2 : ¬ (n + 1 ≤ 4 * b + 1) := by omega
    have c3 : ¬ (n + 1 = 4 * b + 2) := by omega
    have c4 : ¬ (n + 1 = 4 * b + 3) := by omega
    simp only [fu, fs, fv, if_neg c1, if_neg c2, if_neg c3, if_neg c4, if_neg h3, if_neg h4]
    obtain ⟨k1, k2, k3, k4⟩ := std_step J (n + 1)
    exact ⟨k1, k2, by linarith, by linarith⟩

private lemma f_mono (J b : ℕ) (F : ℕ → ℤ) (hF : ∀ n, F n ≤ F (n + 1)) :
    Monotone (fun i => F (qi J i)) := by
  have hm : Monotone F := monotone_nat_of_le_succ hF
  intro x y hxy
  exact hm (by unfold qi; omega)

private lemma std_bounds (J p : ℕ) (hJ : 1 ≤ J) (hp : p ≤ 4 * J) :
    su J (p / 4) (p % 4) < ss J (p / 4) (p % 4) ∧
      ss J (p / 4) (p % 4) + (4 * J + 4) < sv J (p / 4) (p % 4) := by
  have hJ1 : (1 : ℤ) ≤ J := by exact_mod_cast hJ
  have hpt : p / 4 ≤ J := by omega
  have ht : ((p / 4 : ℕ) : ℤ) ≤ J := by exact_mod_cast hpt
  have ht0 : (0 : ℤ) ≤ ((p / 4 : ℕ) : ℤ) := by positivity
  have hm : ((p / 4 : ℕ) : ℤ) * J ≤ (J : ℤ) * J := by nlinarith
  rcases (by omega : p % 4 = 0 ∨ p % 4 = 1 ∨ p % 4 = 2 ∨ p % 4 = 3) with h | h | h | h
  · rw [h]; simp only [su, ss, sv]; norm_num; constructor <;> nlinarith
  · have hpt' : p / 4 + 1 ≤ J := by omega
    have ht' : ((p / 4 : ℕ) : ℤ) + 1 ≤ J := by exact_mod_cast hpt'
    have hm' : ((p / 4 : ℕ) : ℤ) * J + J ≤ (J : ℤ) * J := by nlinarith
    rw [h]; simp only [su, ss, sv]; norm_num; constructor <;> nlinarith
  · have hpt' : p / 4 + 1 ≤ J := by omega
    have ht' : ((p / 4 : ℕ) : ℤ) + 1 ≤ J := by exact_mod_cast hpt'
    have hm' : ((p / 4 : ℕ) : ℤ) * J + J ≤ (J : ℤ) * J := by nlinarith
    rw [h]; simp only [su, ss, sv]; norm_num; constructor <;> nlinarith
  · have hpt' : p / 4 + 1 ≤ J := by omega
    have ht' : ((p / 4 : ℕ) : ℤ) + 1 ≤ J := by exact_mod_cast hpt'
    have hm' : ((p / 4 : ℕ) : ℤ) * J + J ≤ (J : ℤ) * J := by nlinarith
    rw [h]; simp only [su, ss, sv]; norm_num; constructor <;> nlinarith

private lemma f_bounds (J b q : ℕ) (hb : b < J) (hq : q ≤ 4 * J - 1) :
    fu J b q < fs J b q ∧ fs J b q < fv J b q := by
  have hJ : 1 ≤ J := by omega
  have hJ1 : (1 : ℤ) ≤ J := by exact_mod_cast hJ
  have hbz : (b : ℤ) + 1 ≤ J := by exact_mod_cast hb
  have hb0 : (0 : ℤ) ≤ b := by positivity
  have hm : (b : ℤ) * J + J ≤ (J : ℤ) * J := by nlinarith
  by_cases h1 : q ≤ 4 * b + 1
  · simp only [fu, fs, fv, if_pos h1]
    obtain ⟨k1, k2⟩ := std_bounds J q hJ (by omega)
    exact ⟨k1, by linarith⟩
  by_cases h2 : q = 4 * b + 2
  · simp only [fu, fs, fv, if_neg h1, if_pos h2]
    simp only [sv]; norm_num; constructor <;> nlinarith
  by_cases h3 : q = 4 * b + 3
  · simp only [fu, fs, fv, if_neg h1, if_neg h2, if_pos h3]
    simp only [sv]; norm_num; constructor <;> nlinarith
  · simp only [fu, fs, fv, if_neg h1, if_neg h2, if_neg h3]
    obtain ⟨k1, k2⟩ := std_bounds J (q + 1) hJ (by omega)
    exact ⟨k1, by linarith⟩

/-! Kinds and exponents of the original entries. -/

private lemma v0_eq (J : ℕ) :
    (parV0 J : ℤ) = (J : ℤ) * (4 * J + 8) + 1 + J * (4 * J + 6) + 4 * J + 1 := by
  simp only [parV0, parD, parH, parG]; push_cast; ring

private lemma e0 (J : ℕ) : rtKind J 0 = EK.R ∧ rtExp J 0 = parV0 J := by
  simp [rtKind, rtExp]

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
    rtKind J (4 * t + 2) = EK.Q ∧
      (rtExp J (4 * t + 2) : ℤ) = (J : ℤ) * (4 * J + 8) + 1 + t * (4 * J + 6) := by
  have h0 : ¬ (4 * t + 2 = 0) := by omega
  have h1 : ¬ (4 * t + 2 = 4 * J + 1) := by omega
  have m0 : ¬ ((4 * t + 2 - 1) % 4 = 0) := by omega
  have m3 : ¬ ((4 * t + 2 - 1) % 4 = 3) := by omega
  have hm : (4 * t + 2 - 1) % 4 = 1 := by omega
  have hd : (4 * t + 2 - 1) / 4 = t := by omega
  refine ⟨?_, ?_⟩
  · rw [rtKind, if_neg h0, if_neg h1, if_neg m0, if_neg m3]
  · rw [rtExp, if_neg h0, if_neg h1, if_neg m0, if_pos hm, hd]
    simp only [expD, parD, parH, parG]; push_cast; ring

private lemma e3 (J t : ℕ) (ht : t < J) :
    rtKind J (4 * t + 3) = EK.Q ∧
      (rtExp J (4 * t + 3) : ℤ) = (J : ℤ) * (4 * J + 8) + 1 + t * (4 * J + 6) + (4 * J + 4) := by
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
    simp only [expD, parD, parH, parG]; push_cast; ring

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

private lemma e5 (J : ℕ) :
    rtKind J (4 * J + 1) = EK.R ∧
      (rtExp J (4 * J + 1) : ℤ) = (parV0 J : ℤ) + J * (4 * J) := by
  have h0 : ¬ (4 * J + 1 = 0) := by omega
  refine ⟨?_, ?_⟩
  · rw [rtKind, if_neg h0, if_pos rfl]
  · rw [rtExp, if_neg h0, if_pos rfl]
    simp only [parBeta]; push_cast; ring

/-- The standard tilt at original separator `p < 4J` separates entries `p` and `p + 1`
(the `v` value `x` only matters at `p = 0`). -/
private lemma std_sep (J p : ℕ) (hp : p < 4 * J) (x : ℤ) (hx : p = 0 → (parV0 J : ℤ) < x) :
    (rtExp J p : ℤ) < ekSel (rtKind J p) (su J (p / 4) (p % 4)) (ss J (p / 4) (p % 4)) x ∧
      ekSel (rtKind J (p + 1)) (su J (p / 4) (p % 4)) (ss J (p / 4) (p % 4)) x <
        (rtExp J (p + 1) : ℤ) := by
  obtain ⟨t, r, hr, rfl⟩ : ∃ t r, r < 4 ∧ p = 4 * t + r :=
    ⟨p / 4, p % 4, Nat.mod_lt _ (by norm_num), by omega⟩
  have d1 : (4 * t + r) / 4 = t := by omega
  have d2 : (4 * t + r) % 4 = r := by omega
  rw [d1, d2]
  have htJ : t < J := by omega
  have ht0 : (0 : ℤ) ≤ t := by positivity
  rcases (by omega : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3) with rfl | rfl | rfl | rfl
  · rcases t with _ | t
    · obtain ⟨k0, x0⟩ := e0 J
      obtain ⟨k1, x1⟩ := e1 J 0 htJ
      rw [show 4 * 0 + 0 = 0 from rfl, k0, x0]
      rw [show 4 * 0 + 1 = 0 + 1 from rfl] at k1 x1
      rw [k1, x1]
      exact ⟨by simpa [ekSel] using hx rfl, by simp only [ekSel, su]; norm_num; linarith⟩
    · obtain ⟨k0, x0⟩ := e4 J t (by omega)
      obtain ⟨k1, x1⟩ := e1 J (t + 1) htJ
      rw [show 4 * (t + 1) + 0 = 4 * t + 4 by ring, k0, x0]
      rw [show 4 * (t + 1) + 1 = 4 * t + 4 + 1 by ring] at k1 x1
      rw [k1, x1]
      simp only [ekSel, su]; push_cast; norm_num; constructor <;> linarith
  · obtain ⟨k0, x0⟩ := e1 J t htJ
    obtain ⟨k1, x1⟩ := e2 J t htJ
    rw [show 4 * t + 1 + 1 = 4 * t + 2 from rfl, k0, x0, k1, x1]
    simp only [ekSel, su, ss]; norm_num
  · obtain ⟨k0, x0⟩ := e2 J t htJ
    obtain ⟨k1, x1⟩ := e3 J t htJ
    rw [show 4 * t + 2 + 1 = 4 * t + 3 from rfl, k0, x0, k1, x1]
    simp only [ekSel, ss]; norm_num; constructor <;> linarith
  · obtain ⟨k0, x0⟩ := e3 J t htJ
    obtain ⟨k1, x1⟩ := e4 J t htJ
    rw [show 4 * t + 3 + 1 = 4 * t + 4 from rfl, k0, x0, k1, x1]
    simp only [ekSel, su, ss]; norm_num

/-- Deletion of `A'_b = P[a_b + 4]` (position `4b+4`).
Notation and `V_t` (block `b` frozen, `V_0 = v0 + 1`) as in `logCert_delA`.
Erased separators: `i ≤ 4b+1 ↦ std i`; `i = 4b+2 ↦ (a_b + h/2, d_b + G/2, V_b)`;
`i = 4b+3 ↦ (a_b + h - 1, d_b + G + 1, V_b)` (separates `D'_b` from `A_{b+1}`, or from
`R[V1]` if `b = J - 1`); `i ≥ 4b+4 ↦ std (i + 1)`; clamp `i ≥ 4J` to `4J - 1`.
Checks: `i = 4b+2`: `d_b < s < d_b + G`. `i = 4b+3`: `s > d_b + G` and `u = a_{b+1} - 1 <
a_{b+1}` (or, if `b = J - 1`, `v = V_b = v0 + 4J² - 3 < V1`); `u = a_b + h - 1 ≤ Jh - 1 < s`.
Steps: `(h/2 - 1, G/2 + 1, 0)`, `(h/2 - 1, G/2 + 1, 0)` (`h/2 - 1 = G/2 + 1 = 2J + 3`), then
into `std (4b+5) = (a_{b+1} + 1, d_b + G + 1, V_b)`: `(2, 0, 0)`. -/
theorem logCert_delAp (J b : ℕ) (hb : b < J) :
    ∃ u s v w : ℕ → ℤ, LogCert J (4 * b + 4) u s v w := by
  have hJ : 1 ≤ J := by omega
  have hJ1 : (1 : ℤ) ≤ J := by exact_mod_cast hJ
  have hbz : (b : ℤ) + 1 ≤ J := by exact_mod_cast hb
  have hb0 : (0 : ℤ) ≤ b := by positivity
  refine ⟨fun i => fu J b (qi J i), fun i => fs J b (qi J i), fun i => fv J b (qi J i),
    fun i => fu J b (qi J i) + fv J b (qi J i) - fs J b (qi J i), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact f_mono J b (fu J b) (fun n => (f_step J b n).1)
  · exact f_mono J b (fs J b) (fun n => (f_step J b n).2.1)
  · exact f_mono J b (fv J b) (fun n => (f_step J b n).2.2.1)
  · exact f_mono J b (fun q => fu J b q + fv J b q - fs J b q)
      (fun n => (f_step J b n).2.2.2)
  · intro i; ring
  · intro i
    exact f_bounds J b _ hb (by unfold qi; omega)
  · intro i hi
    have hq : qi J i = i := by unfold qi; omega
    simp only [hq]
    by_cases h1 : i ≤ 4 * b + 1
    · have s1 : skipIdx (4 * b + 4) i = i := by rw [skipIdx, if_pos (by omega)]
      have s2 : skipIdx (4 * b + 4) (i + 1) = i + 1 := by rw [skipIdx, if_pos (by omega)]
      simp only [s1, s2, fu, fs, fv, if_pos h1]
      apply std_sep J i (by omega)
      intro h0
      subst h0
      rw [v0_eq]; simp only [Nat.zero_div, Nat.zero_mod, sv]; norm_num
    by_cases h3 : i = 4 * b + 2
    · subst h3
      have s1 : skipIdx (4 * b + 4) (4 * b + 2) = 4 * b + 2 := by
        rw [skipIdx, if_pos (by omega)]
      have s2 : skipIdx (4 * b + 4) (4 * b + 2 + 1) = 4 * b + 3 := by
        rw [skipIdx, if_pos (by omega)]
      have c1 : ¬ (4 * b + 2 ≤ 4 * b + 1) := by omega
      simp only [s1, s2, fu, fs, fv, if_neg c1, if_true]
      obtain ⟨k0, x0⟩ := e2 J b hb
      obtain ⟨k1, x1⟩ := e3 J b hb
      rw [k0, x0, k1, x1]
      simp only [ekSel]; constructor <;> linarith
    by_cases h4 : i = 4 * b + 3
    · subst h4
      have s1 : skipIdx (4 * b + 4) (4 * b + 3) = 4 * b + 3 := by
        rw [skipIdx, if_pos (by omega)]
      have s2 : skipIdx (4 * b + 4) (4 * b + 3 + 1) = 4 * b + 5 := by
        rw [skipIdx, if_neg (by omega)]
      have c1 : ¬ (4 * b + 3 ≤ 4 * b + 1) := by omega
      have c2 : ¬ (4 * b + 3 = 4 * b + 2) := by omega
      simp only [s1, s2, fu, fs, fv, if_neg c1, if_neg c2, if_true]
      obtain ⟨k0, x0⟩ := e3 J b hb
      rw [k0, x0]
      refine ⟨by simp only [ekSel]; linarith, ?_⟩
      by_cases hl : b + 1 < J
      · obtain ⟨k1, x1⟩ := e1 J (b + 1) hl
        rw [show 4 * (b + 1) + 1 = 4 * b + 5 by ring] at k1 x1
        rw [k1, x1]
        simp only [ekSel]; push_cast; linarith
      · have hbJ : 4 * b + 5 = 4 * J + 1 := by omega
        obtain ⟨k1, x1⟩ := e5 J
        rw [hbJ, k1, x1, v0_eq]
        have hc : (J : ℤ) = b + 1 := by omega
        simp only [ekSel, sv]; norm_num; rw [hc]; nlinarith
    · have s1 : skipIdx (4 * b + 4) i = i + 1 := by rw [skipIdx, if_neg (by omega)]
      have s2 : skipIdx (4 * b + 4) (i + 1) = i + 1 + 1 := by rw [skipIdx, if_neg (by omega)]
      simp only [s1, s2, fu, fs, fv, if_neg h1, if_neg h3, if_neg h4]
      by_cases hl : i + 1 < 4 * J
      · exact std_sep J (i + 1) hl _ (fun h => absurd h (by omega))
      · have hi1 : i + 1 = 4 * J := by omega
        rw [hi1]
        have d1 : 4 * J / 4 = J := by omega
        have d2 : 4 * J % 4 = 0 := by omega
        rw [d1, d2]
        obtain ⟨k0, x0⟩ := e4 J (J - 1) (by omega)
        obtain ⟨k1, x1⟩ := e5 J
        have hJJ : 4 * (J - 1) + 4 = 4 * J := by omega
        rw [hJJ] at k0 x0
        rw [k0, x0, k1, x1, v0_eq]
        have hc : (((J - 1 : ℕ)) : ℤ) = (J : ℤ) - 1 := by omega
        rw [hc]
        simp only [ekSel, su, sv]; norm_num; constructor <;> nlinarith

end K4
