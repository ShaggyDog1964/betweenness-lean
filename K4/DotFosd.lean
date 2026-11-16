import K4.Defs

namespace K4

open Finset

private lemma abel_range (W d : ℕ → ℝ) : ∀ N : ℕ,
    ∑ n ∈ range N, W n * d n = W 0 * ∑ n ∈ range N, d n +
      ∑ j ∈ range N, (W (j+1) - W j) * ∑ n ∈ range N, (if j+1 ≤ n then d n else 0)
  | 0 => by simp
  | N+1 => by
    have ih := abel_range W d N
    have h1 : ∀ j ∈ range (N+1), (W (j+1) - W j) * ∑ n ∈ range (N+1),
        (if j+1 ≤ n then d n else 0) = (W (j+1) - W j) * (∑ n ∈ range N,
        (if j+1 ≤ n then d n else 0) + if j + 1 ≤ N then d N else 0) :=
      fun j _ => by rw [sum_range_succ]
    rw [sum_congr rfl h1, sum_range_succ (fun j => (W (j+1) - W j) * (∑ n ∈ range N,
        (if j+1 ≤ n then d n else 0) + if j + 1 ≤ N then d N else 0))]
    have h2 : ∑ n ∈ range N, (if N+1 ≤ n then d n else 0) = 0 :=
      sum_eq_zero (fun n hn => by
        rw [mem_range] at hn; rw [if_neg (by omega)])
    have h3 : ∑ j ∈ range N, (W (j+1) - W j) * (∑ n ∈ range N,
        (if j+1 ≤ n then d n else 0) + if j+1 ≤ N then d N else 0) =
        ∑ j ∈ range N, (W (j+1) - W j) * ∑ n ∈ range N, (if j+1 ≤ n then d n else 0)
          + (W N - W 0) * d N := by
      rw [← sum_range_sub W N, sum_mul, ← sum_add_distrib]
      apply sum_congr rfl
      intro j hj
      rw [mem_range] at hj
      rw [if_pos (by omega)]
      ring
    rw [h3, h2, sum_range_succ, sum_range_succ, ih]
    simp only [if_neg (show ¬ N + 1 ≤ N by omega), add_zero, mul_zero]
    ring

/-- Strictly increasing utility weights strictly reward strict FOSD on the simplex.
Sketch (Abel summation): put `T k = tail q k - tail r k ≥ 0`; `T 0 = 1 - 1 = 0` on the
simplex. Then `dot w q - dot w r = ∑_{k ≥ 1} (w k - w (k-1)) * T k`. All coefficients are
`> 0` (`hw`), all `T k ≥ 0`, and some `T k > 0` with `k ≥ 1` (if all tails agree then
`q = r`, since `q k = tail q k - tail q (k+1)`). -/
theorem dot_lt_of_strictFOSD {K : ℕ} {w q r : Lot K} (hw : StrictMono w)
    (hq : q ∈ Simplex K) (hr : r ∈ Simplex K) (h : StrictFOSD q r) :
    dot w r < dot w q := by
  let e : Lot K → ℕ → ℝ := fun p n => if hn : n < K then p ⟨n, hn⟩ else 0
  have he : ∀ (p : Lot K) (i : Fin K), e p i = p i := by
    intro p i; simp [e, i.isLt]
  have hdot : ∀ p, dot w p = ∑ n ∈ range K, e w n * e p n := by
    intro p; unfold dot
    rw [← Fin.sum_univ_eq_sum_range (fun n => e w n * e p n)]
    simp only [he]
  have hmass : ∀ p : Lot K, p ∈ Simplex K → ∑ n ∈ range K, e p n = 1 := by
    intro p hp
    rw [← Fin.sum_univ_eq_sum_range (fun n => e p n)]
    simp only [he]; exact hp.2
  have htail : ∀ (p : Lot K) (k : Fin K),
      tail p k = ∑ n ∈ range K, if k.val ≤ n then e p n else 0 := by
    intro p k; unfold tail
    rw [Finset.sum_filter,
      ← Fin.sum_univ_eq_sum_range (fun n => if k.val ≤ n then e p n else 0)]
    simp only [he, Fin.le_iff_val_le_val]
  let d : ℕ → ℝ := fun n => e q n - e r n
  let T' : ℕ → ℝ := fun m => ∑ n ∈ range K, if m ≤ n then d n else 0
  have hT'eq : ∀ m, T' m = (∑ n ∈ range K, if m ≤ n then e q n else 0) -
      ∑ n ∈ range K, if m ≤ n then e r n else 0 := by
    intro m
    simp only [T']
    rw [← sum_sub_distrib]
    apply sum_congr rfl
    intro n _
    split_ifs <;> simp [d]
  have hsum : ∑ n ∈ range K, d n = 0 := by
    simp only [d]; rw [sum_sub_distrib, hmass q hq, hmass r hr]; ring
  have hdiff : dot w q - dot w r = ∑ j ∈ range K, (e w (j+1) - e w j) * T' (j+1) := by
    rw [hdot, hdot, ← sum_sub_distrib]
    have : ∑ n ∈ range K, (e w n * e q n - e w n * e r n) = ∑ n ∈ range K, e w n * d n :=
      sum_congr rfl (fun n _ => by simp only [d]; ring)
    rw [this, abel_range, hsum, mul_zero, zero_add]
  have hTbig : ∀ m, K ≤ m → T' m = 0 := by
    intro m hm
    exact sum_eq_zero (fun n hn => by rw [mem_range] at hn; rw [if_neg (by omega)])
  have hTnn : ∀ m, 0 ≤ T' m := by
    intro m
    by_cases hm : m < K
    · rw [hT'eq]
      have := h.1 ⟨m, hm⟩
      rw [htail, htail] at this
      simpa using this
    · rw [hTbig m (by omega)]
  have hc : ∀ j, j + 1 < K → 0 < e w (j+1) - e w j := by
    intro j hj
    have h1 : e w (j+1) = w ⟨j+1, hj⟩ := by simp [e, hj]
    have h2 : e w j = w ⟨j, by omega⟩ := by simp [e, show j < K by omega]
    rw [h1, h2, sub_pos]
    exact hw (Fin.mk_lt_mk.2 (by omega))
  have hterm : ∀ j ∈ range K, 0 ≤ (e w (j+1) - e w j) * T' (j+1) := by
    intro j _
    by_cases hj : j + 1 < K
    · exact mul_nonneg (hc j hj).le (hTnn _)
    · rw [hTbig (j+1) (by omega), mul_zero]
  by_contra hlt
  push_neg at hlt
  have hz : ∑ j ∈ range K, (e w (j+1) - e w j) * T' (j+1) = 0 := by
    apply le_antisymm
    · rw [← hdiff]; linarith
    · exact sum_nonneg hterm
  rw [sum_eq_zero_iff_of_nonneg hterm] at hz
  have hT0 : ∀ m, T' m = 0 := by
    intro m
    rcases m with _ | j
    · simp only [T', zero_le, if_true]; exact hsum
    · by_cases hj : j + 1 < K
      · have := hz j (mem_range.2 (by omega))
        rcases mul_eq_zero.1 this with h0 | h0
        · exact absurd h0 (hc j hj).ne'
        · exact h0
      · exact hTbig _ (by omega)
  have hd : ∀ n, n < K → d n = 0 := by
    intro n hn
    have hdiffT : T' n - T' (n+1) = d n := by
      simp only [T']
      rw [← sum_sub_distrib]
      have : ∀ i ∈ range K, ((if n ≤ i then d i else 0) - if n + 1 ≤ i then d i else 0)
          = if n = i then d i else 0 := by
        intro i _
        by_cases h1 : n = i
        · subst h1; simp
        · by_cases h2 : n + 1 ≤ i
          · rw [if_pos (by omega), if_pos h2, if_neg h1, sub_self]
          · rw [if_neg (by omega), if_neg h2, if_neg h1, sub_self]
      rw [sum_congr rfl this, sum_ite_eq]
      rw [if_pos (mem_range.2 hn)]
    rw [← hdiffT, hT0, hT0, sub_self]
  apply h.2
  funext i
  have := hd i i.isLt
  simp only [d, he] at this
  linarith

end K4
