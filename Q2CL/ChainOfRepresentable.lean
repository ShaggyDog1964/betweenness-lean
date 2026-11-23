import Q2CL.Defs
import Q2CL.LevelHyperplane
import Q2CL.FarkasStep
import K4.PairwiseMapRange
import K4.SprefTrans
import K4.MixMem

namespace Q2CL

open K4

private lemma cor_dot_smul (c : ℝ) (V p : Lot 4) : dot (c • V) p = c * dot V p := by
  simp [dot, Finset.mul_sum, mul_assoc]

private lemma cor_dot_smul_right (c : ℝ) (V p : Lot 4) : dot V (c • p) = c * dot V p := by
  simp only [dot, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ => by ring

/-- Normalization of a nonzero nonnegative vector into the simplex. -/
private lemma cor_normalize (q : Lot 4) (hq : ∀ k, 0 ≤ q k) (hne : q ≠ 0) :
    ∃ s : ℝ, 0 < s ∧ (s • q) ∈ Simplex 4 := by
  have hsum : 0 < ∑ k, q k := by
    rcases (Finset.sum_nonneg (fun k (_ : k ∈ Finset.univ) => hq k)).lt_or_eq with h | h
    · exact h
    · exfalso
      apply hne
      funext k
      have := (Finset.sum_eq_zero_iff_of_nonneg (fun k (_ : k ∈ Finset.univ) => hq k)).1
        h.symm k (Finset.mem_univ k)
      simpa using this
  refine ⟨1 / ∑ k, q k, by positivity, fun k => ?_, ?_⟩
  · simp only [Pi.smul_apply, smul_eq_mul]
    exact mul_nonneg (by positivity) (hq k)
  · simp only [Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum]
    field_simp

/-- "Only if" of Theorem 33: a representable ranking has a chain. -/
theorem chain_of_representable (n : ℕ) (p : ℕ → Lot 4) (hp : ∀ i, i < n → p i ∈ Simplex 4)
    (h : Representable ((List.range n).map p)) : ∃ W, IsChainFn n p W := by
  obtain ⟨R, hR, hpair⟩ := h
  have hS := (pairwise_map_range_iff (SPref R) p n).1 hpair
  set r : ℕ → Lot 4 := fun i => mix (1 / 2) (p i) (p (i + 1)) with hr_def
  have hrmem : ∀ i, i + 1 < n → r i ∈ Simplex 4 := fun i hi =>
    mix_mem_simplex (hp i (by omega)) (hp (i + 1) hi) (by norm_num) (by norm_num)
  have hbtw : ∀ i, i + 1 < n → SPref R (p i) (r i) ∧ SPref R (r i) (p (i + 1)) := fun i hi =>
    hR.btw_strict _ (hp i (by omega)) _ (hp (i + 1) hi) (1 / 2) ⟨by norm_num, by norm_num⟩
      (hS i (i + 1) (by omega) hi)
  have hV : ∀ i, ∃ V : Lot 4, i + 1 < n → StrictMono V ∧
      ∀ q ∈ Simplex 4, (SPref R q (r i) ↔ 0 < dot V q) ∧ (SPref R (r i) q ↔ dot V q < 0) := by
    intro i
    by_cases hi : i + 1 < n
    · obtain ⟨V, hV⟩ := level_hyperplane hR (hp i (by omega)) (hrmem i hi) (hp (i + 1) hi)
        (hbtw i hi).1 (hbtw i hi).2
      exact ⟨V, fun _ => hV⟩
    · exact ⟨0, fun h => absurd h hi⟩
  choose V hVspec using hV
  have ha : ∀ i, ∃ a : ℝ, 0 < a ∧ (i + 2 < n → ∀ k, a * V i k ≤ V (i + 1) k) := by
    intro i
    by_cases hi : i + 2 < n
    · have hi1 : i + 1 < n := by omega
      obtain ⟨_, hVi⟩ := hVspec i hi1
      obtain ⟨_, hVi1⟩ := hVspec (i + 1) hi
      have hrr : SPref R (r i) (r (i + 1)) :=
        spref_trans hR (hrmem i hi1) (hp (i + 1) hi1) (hrmem (i + 1) hi) (hbtw i hi1).2
          (hbtw (i + 1) hi).1
      obtain ⟨a, ha0, hak⟩ := farkas_step (V i) (V (i + 1)) (fun q hq hq0 => by
          by_cases hz : q = 0
          · subst hz; simp [dot]
          obtain ⟨s, hs0, hsm⟩ := cor_normalize q hq hz
          have h1 : 0 ≤ dot (V i) (s • q) := by
            rw [cor_dot_smul_right]; exact mul_nonneg hs0.le hq0
          have h2 : R (s • q) (r i) := by
            rcases hR.complete _ hsm _ (hrmem i hi1) with h | h
            · exact h
            · by_contra hn
              have := ((hVi _ hsm).2.1 ⟨h, hn⟩)
              linarith
          have h3 : SPref R (s • q) (r (i + 1)) :=
            ⟨hR.trans _ hsm _ (hrmem i hi1) _ (hrmem (i + 1) hi) h2 hrr.1,
              fun h' => hrr.2 (hR.trans _ (hrmem (i + 1) hi) _ hsm _ (hrmem i hi1) h' h2)⟩
          have h4 := (hVi1 _ hsm).1.1 h3
          rw [cor_dot_smul_right] at h4
          by_contra hn
          push Not at hn
          nlinarith)
        ⟨p (i + 2), (hp (i + 2) hi).1,
          (hVi1 _ (hp (i + 2) hi)).2.1 (hbtw (i + 1) hi).2⟩
      exact ⟨a, ha0, fun _ => hak⟩
    · exact ⟨1, one_pos, fun h => absurd h hi⟩
  choose a ha0 hak using ha
  let lam : ℕ → ℝ := fun i => Nat.rec 1 (fun j l => l / a j) i
  have hlam0 : ∀ i, 0 < lam i := by
    intro i
    induction i with
    | zero => show (0 : ℝ) < 1; norm_num
    | succ j ih => show 0 < lam j / a j; exact div_pos ih (ha0 j)
  have hlamS : ∀ i, lam (i + 1) = lam i / a i := fun i => rfl
  refine ⟨fun i => lam i • V i, fun i hi => ?_, fun i hi => ?_⟩
  · obtain ⟨hmono, hVi⟩ := hVspec i hi
    obtain ⟨hb1, hb2⟩ := hbtw i hi
    refine ⟨fun k j hkj => ?_, ?_, ?_⟩
    · simp only [Pi.smul_apply, smul_eq_mul]
      exact mul_lt_mul_of_pos_left (hmono hkj) (hlam0 i)
    · rw [cor_dot_smul]
      exact mul_pos (hlam0 i) ((hVi _ (hp i (by omega))).1.1 hb1)
    · rw [cor_dot_smul]
      exact mul_neg_of_pos_of_neg (hlam0 i) ((hVi _ (hp (i + 1) hi)).2.1 hb2)
  · intro k
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [hlamS]
    have h1 := hak i hi k
    have hl := hlam0 i
    have ha' := ha0 i
    rw [div_mul_eq_mul_div, le_div_iff₀ ha']
    nlinarith
end Q2CL
