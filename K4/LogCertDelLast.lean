import K4.Defs

namespace K4

/-! Explicit tilts, as in `logCert_delFirst`, with `v` shifted up by `4J + 2`
(so `V_t = v0 + 1 + t G`), and an extra first tilt for the separator `(R[v0], A_0)`. -/

private def cu (J t r : ℕ) : ℤ :=
  (t : ℤ) * (4 * J + 8) +
    (if r = 0 then (1 : ℤ) else if r = 1 then (2 : ℤ) else if r = 2 then (3 : ℤ) else (5 : ℤ))

private def cs (J t r : ℕ) : ℤ :=
  (J : ℤ) * (4 * J + 8) + 1 + t * (4 * J + 6) +
    (if r = 0 then (-1 : ℤ) else if r = 1 then 2 * (J : ℤ) + 2 else 4 * (J : ℤ) + 5)

private def cv (J t r : ℕ) : ℤ :=
  (J : ℤ) * (4 * J + 8) + 1 + J * (4 * J + 6) + t * (4 * J + 4) + (4 * J + 2) +
    (if r = 0 then (0 : ℤ) else if r = 1 then 2 * (J : ℤ) + 2 else 4 * (J : ℤ) + 4)

private def qi (J i : ℕ) : ℕ := min i (4 * J - 1)

private def ext (a : ℤ) (f : ℕ → ℤ) : ℕ → ℤ := fun i => if i = 0 then a else f (i - 1)

private lemma ext_zero (a : ℤ) (f : ℕ → ℤ) : ext a f 0 = a := rfl
private lemma ext_succ (a : ℤ) (f : ℕ → ℤ) (n : ℕ) : ext a f (n + 1) = f n := rfl

private lemma ext_mono (a : ℤ) (f : ℕ → ℤ) (hf : Monotone f) (ha : a ≤ f 0) :
    Monotone (ext a f) := by
  apply monotone_nat_of_le_succ
  intro n
  rcases n with _ | n
  · rw [ext_zero, ext_succ]; exact ha
  · rw [ext_succ, ext_succ]; exact hf (Nat.le_succ n)

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

/-- Separators strictly inside the blocks (never touching an `R` entry). -/
private lemma sep (J t r : ℕ) (hJ : 1 ≤ J) (hr : r < 4) (ht : 4 * t + r + 1 < 4 * J) :
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
    obtain ⟨k2, x2⟩ := e1 J (t + 1) (by omega)
    rw [show 4 * t + 5 = 4 * (t + 1) + 1 by ring, k2, x2]
    simp only [ekSel, cu]; push_cast; norm_num; nlinarith

private def fu (J : ℕ) : ℕ → ℤ := fun i => cu J (qi J i / 4) (qi J i % 4)
private def fs (J : ℕ) : ℕ → ℤ := fun i => cs J (qi J i / 4) (qi J i % 4)
private def fv (J : ℕ) : ℕ → ℤ := fun i => cv J (qi J i / 4) (qi J i % 4)
private def fw (J : ℕ) : ℕ → ℤ := fun i => fu J i + fv J i - fs J i

private def a0u (J : ℕ) : ℤ := 5 - (4 * J + 8)
private def a0s (J : ℕ) : ℤ := (J : ℤ) * (4 * J + 8)
private def a0v (J : ℕ) : ℤ := (parV0 J : ℤ) + 1

private lemma qi0 (J : ℕ) (hJ : 1 ≤ J) : qi J 0 = 0 := by unfold qi; omega

private lemma a0v_eq (J : ℕ) :
    a0v J = (J : ℤ) * (4 * J + 8) + 1 + J * (4 * J + 6) + (4 * J + 2) := by
  simp only [a0v, parV0, parD, parH, parG]; push_cast; ring

theorem logCert_delLast (J : ℕ) (hJ : 1 ≤ J) :
    ∃ u s v w : ℕ → ℤ, LogCert J (4 * J + 1) u s v w := by
  have hq0 := qi0 J hJ
  have hJ1 : (1 : ℤ) ≤ J := by exact_mod_cast hJ
  refine ⟨ext (a0u J) (fu J), ext (a0s J) (fs J), ext (a0v J) (fv J),
    ext (a0u J + a0v J - a0s J) (fw J), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · apply ext_mono
    · apply mono_of J (cu J)
      · intro t r hr
        rcases (by omega : r = 0 ∨ r = 1 ∨ r = 2) with rfl | rfl | rfl <;> simp [cu]
      · intro t; simp only [cu]; push_cast; norm_num; linarith
    · simp only [fu, hq0, a0u, cu]; norm_num; linarith
  · apply ext_mono
    · apply mono_of J (cs J)
      · intro t r hr
        rcases (by omega : r = 0 ∨ r = 1 ∨ r = 2) with rfl | rfl | rfl <;> simp [cs] <;> linarith
      · intro t; simp only [cs]; push_cast; linarith
    · simp only [fs, hq0, a0s, cs]; norm_num
  · apply ext_mono
    · apply mono_of J (cv J)
      · intro t r hr
        rcases (by omega : r = 0 ∨ r = 1 ∨ r = 2) with rfl | rfl | rfl <;> simp [cv] <;> linarith
      · intro t; simp only [cv]; push_cast; norm_num; linarith
    · simp only [fv, hq0, a0v_eq, cv]; norm_num
  · apply ext_mono
    · apply mono_of J (fun t r => cu J t r + cv J t r - cs J t r)
      · intro t r hr
        rcases (by omega : r = 0 ∨ r = 1 ∨ r = 2) with rfl | rfl | rfl <;>
          simp [cu, cs, cv] <;> linarith
      · intro t; simp only [cu, cs, cv]; push_cast; norm_num; linarith
    · simp only [fw, fu, fv, fs, hq0, a0u, a0s, a0v_eq, cu, cs, cv]; norm_num; linarith
  · intro i
    rcases i with _ | i
    · simp only [ext_zero]; ring
    · simp only [ext_succ, fw]; ring
  · intro i
    rcases i with _ | i
    · simp only [ext_zero, a0u, a0s, a0v_eq]
      constructor <;> nlinarith
    · simp only [ext_succ, fu, fs, fv]
      exact bounds J _ _ hJ (Nat.mod_lt _ (by norm_num)) (by unfold qi; omega)
  · intro i hi
    have hs1 : skipIdx (4 * J + 1) i = i := by simp [skipIdx]; omega
    have hs2 : skipIdx (4 * J + 1) (i + 1) = i + 1 := by simp [skipIdx]; omega
    simp only [hs1, hs2]
    rcases i with _ | j
    · have k0 : rtKind J 0 = EK.R := by simp [rtKind]
      have x0 : rtExp J 0 = parV0 J := by simp [rtExp]
      obtain ⟨k1, x1⟩ := e1 J 0 (by omega)
      simp only [Nat.mul_zero, Nat.zero_add] at k1 x1
      simp only [ext_zero, Nat.zero_add, k0, x0, k1, x1, ekSel, a0u, a0v]
      push_cast; constructor <;> linarith
    · have hq : qi J j = j := by unfold qi; omega
      simp only [ext_succ, fu, fs, fv, hq]
      have key := sep J (j / 4) (j % 4) hJ (Nat.mod_lt _ (by norm_num)) (by omega)
      rw [show 4 * (j / 4) + j % 4 = j by omega] at key
      exact key

end K4
