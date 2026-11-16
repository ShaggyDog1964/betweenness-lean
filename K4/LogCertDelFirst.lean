import K4.Defs

namespace K4

/-! Explicit tilts. `t` is the block index and `r = 0..3` the position within the block. -/

private def cu (J t r : ℕ) : ℤ :=
  (t : ℤ) * (4 * J + 8) +
    (if r = 0 then (1 : ℤ) else if r = 1 then (2 : ℤ) else if r = 2 then (3 : ℤ) else (5 : ℤ))

private def cs (J t r : ℕ) : ℤ :=
  (J : ℤ) * (4 * J + 8) + 1 + t * (4 * J + 6) +
    (if r = 0 then (-1 : ℤ) else if r = 1 then 2 * (J : ℤ) + 2 else 4 * (J : ℤ) + 5)

private def cv (J t r : ℕ) : ℤ :=
  (J : ℤ) * (4 * J + 8) + 1 + J * (4 * J + 6) + t * (4 * J + 4) +
    (if r = 0 then (0 : ℤ) else if r = 1 then 2 * (J : ℤ) + 2 else 4 * (J : ℤ) + 4)

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

private lemma bounds (J t r : ℕ) (hJ : 1 ≤ J) (hr : r < 4) (ht : 4 * t + r ≤ 4 * J - 1) :
    cu J t r < cs J t r ∧ cs J t r < cv J t r := by
  have htJ : (t : ℤ) + 1 ≤ J := by omega
  have hJ1 : (1 : ℤ) ≤ J := by exact_mod_cast hJ
  have ht0 : (0 : ℤ) ≤ t := by positivity
  have hm : (t : ℤ) * J + J ≤ (J : ℤ) * J := by nlinarith
  rcases (by omega : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3) with rfl | rfl | rfl | rfl <;>
    simp only [cu, cs, cv] <;> norm_num <;> constructor <;> nlinarith

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

private lemma e5 (J t : ℕ) (ht : t + 1 = J) :
    rtKind J (4 * t + 5) = EK.R ∧
      (rtExp J (4 * t + 5) : ℤ) = (J : ℤ) * (4 * J + 8) + 1 + J * (4 * J + 6) + 4 * J + 1
        + J * (4 * J) := by
  have h0 : ¬ (4 * t + 5 = 0) := by omega
  have h1 : 4 * t + 5 = 4 * J + 1 := by omega
  refine ⟨?_, ?_⟩
  · rw [rtKind, if_neg h0, if_pos h1]
  · rw [rtExp, if_neg h0, if_pos h1]
    simp only [parV0, parD, parH, parG, parBeta]; push_cast; ring

private lemma sep (J t r : ℕ) (hJ : 1 ≤ J) (hr : r < 4) (ht : 4 * t + r < 4 * J) :
    ((rtExp J (4 * t + r + 1) : ℤ) <
        ekSel (rtKind J (4 * t + r + 1)) (cu J t r) (cs J t r) (cv J t r)) ∧
      (ekSel (rtKind J (4 * t + r + 1 + 1)) (cu J t r) (cs J t r) (cv J t r) <
        (rtExp J (4 * t + r + 1 + 1) : ℤ)) := by
  have htJ : t < J := by omega
  have htJz : (t : ℤ) + 1 ≤ J := by exact_mod_cast htJ
  have hJ1 : (1 : ℤ) ≤ J := by exact_mod_cast hJ
  have ht0 : (0 : ℤ) ≤ t := by positivity
  rcases (by omega : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3) with rfl | rfl | rfl | rfl
  · rw [show 4 * t + 0 + 1 = 4 * t + 1 from rfl, show 4 * t + 0 + 1 + 1 = 4 * t + 2 from rfl]
    obtain ⟨k1, x1⟩ := e1 J t htJ
    obtain ⟨k2, x2⟩ := e2 J t htJ
    rw [k1, k2, x1, x2]
    simp only [ekSel, cu, cs]; norm_num
  · rw [show 4 * t + 1 + 1 = 4 * t + 2 from rfl, show 4 * t + 1 + 1 + 1 = 4 * t + 3 from rfl]
    obtain ⟨k1, x1⟩ := e2 J t htJ
    obtain ⟨k2, x2⟩ := e3 J t htJ
    rw [k1, k2, x1, x2]
    simp only [ekSel, cs]; norm_num; constructor <;> linarith
  · rw [show 4 * t + 2 + 1 = 4 * t + 3 from rfl, show 4 * t + 2 + 1 + 1 = 4 * t + 4 from rfl]
    obtain ⟨k1, x1⟩ := e3 J t htJ
    obtain ⟨k2, x2⟩ := e4 J t htJ
    rw [k1, k2, x1, x2]
    simp only [ekSel, cu, cs]; norm_num
  · rw [show 4 * t + 3 + 1 = 4 * t + 4 from rfl, show 4 * t + 3 + 1 + 1 = 4 * t + 5 from rfl]
    obtain ⟨k1, x1⟩ := e4 J t htJ
    rw [k1, x1]
    refine ⟨by simp only [ekSel, cu]; norm_num, ?_⟩
    by_cases hlast : t + 1 = J
    · obtain ⟨k2, x2⟩ := e5 J t hlast
      rw [k2, x2]
      have : (t : ℤ) + 1 = J := by exact_mod_cast hlast
      simp only [ekSel, cv]; norm_num; nlinarith
    · obtain ⟨k2, x2⟩ := e1 J (t + 1) (by omega)
      rw [show 4 * t + 5 = 4 * (t + 1) + 1 by ring, k2, x2]
      simp only [ekSel, cu]; push_cast; norm_num; nlinarith

theorem logCert_delFirst (J : ℕ) (hJ : 1 ≤ J) : ∃ u s v w : ℕ → ℤ, LogCert J 0 u s v w := by
  refine ⟨fun i => cu J (qi J i / 4) (qi J i % 4), fun i => cs J (qi J i / 4) (qi J i % 4),
    fun i => cv J (qi J i / 4) (qi J i % 4),
    fun i => cu J (qi J i / 4) (qi J i % 4) + cv J (qi J i / 4) (qi J i % 4) -
      cs J (qi J i / 4) (qi J i % 4), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · apply mono_of J (cu J)
    · intro t r hr
      rcases (by omega : r = 0 ∨ r = 1 ∨ r = 2) with rfl | rfl | rfl <;> simp [cu]
    · intro t; simp only [cu]; push_cast; norm_num; linarith
  · apply mono_of J (cs J)
    · intro t r hr
      rcases (by omega : r = 0 ∨ r = 1 ∨ r = 2) with rfl | rfl | rfl <;> simp [cs] <;> linarith
    · intro t; simp only [cs]; push_cast; linarith
  · apply mono_of J (cv J)
    · intro t r hr
      rcases (by omega : r = 0 ∨ r = 1 ∨ r = 2) with rfl | rfl | rfl <;> simp [cv] <;> linarith
    · intro t; simp only [cv]; push_cast; norm_num; linarith
  · apply mono_of J (fun t r => cu J t r + cv J t r - cs J t r)
    · intro t r hr
      rcases (by omega : r = 0 ∨ r = 1 ∨ r = 2) with rfl | rfl | rfl <;>
        simp [cu, cs, cv] <;> linarith
    · intro t; simp only [cu, cs, cv]; push_cast; norm_num; linarith
  · intro i; ring
  · intro i
    exact bounds J _ _ hJ (Nat.mod_lt _ (by norm_num)) (by unfold qi; omega)
  · intro i hi
    have hq : qi J i = i := by unfold qi; omega
    have hs1 : skipIdx 0 i = i + 1 := by simp [skipIdx]
    have hs2 : skipIdx 0 (i + 1) = i + 1 + 1 := by simp [skipIdx]
    simp only [hq, hs1, hs2]
    have key := sep J (i / 4) (i % 4) hJ (Nat.mod_lt _ (by norm_num)) (by omega)
    rw [show 4 * (i / 4) + i % 4 = i by omega] at key
    exact key

end K4
