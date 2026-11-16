import K4.Defs

namespace K4

private noncomputable def pcCl (x : ℝ) : ℝ := max 0 (min 1 x)

private lemma pcCl_of_le_zero {x : ℝ} (h : x ≤ 0) : pcCl x = 0 := by
  unfold pcCl; rw [min_eq_right (by linarith)]; exact max_eq_left h

private lemma pcCl_of_one_le {x : ℝ} (h : 1 ≤ x) : pcCl x = 1 := by
  unfold pcCl; rw [min_eq_left h]; exact max_eq_right zero_le_one

private lemma pcCl_of_mem {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1) : pcCl x = x := by
  unfold pcCl; rw [min_eq_right h1]; exact max_eq_right h0

private lemma pcCl_mono {x y : ℝ} (h : x ≤ y) : pcCl x ≤ pcCl y := by
  unfold pcCl; exact max_le_max le_rfl (min_le_min le_rfl h)

private lemma pcCl_cont : Continuous pcCl := by
  unfold pcCl; fun_prop

private noncomputable def pcS {K : ℕ} (W : ℕ → Lot K) (τ : ℝ) (n : ℕ) (k : Fin K) : ℝ :=
  ∑ i ∈ Finset.range n, pcCl (τ - i) * (W (i + 1) k - W i k)

private noncomputable def pcPhi {K : ℕ} (W : ℕ → Lot K) (N : ℕ) (τ : ℝ) : Lot K := fun k =>
  W 0 k + pcS W τ N k + (min τ 0 + max (τ - N) 0)

private lemma pcS_low {K : ℕ} (W : ℕ → Lot K) {τ : ℝ} (hτ : τ ≤ 0) (n : ℕ) (k : Fin K) :
    pcS W τ n k = 0 := by
  unfold pcS
  apply Finset.sum_eq_zero
  intro i _
  have : (0 : ℝ) ≤ i := Nat.cast_nonneg i
  rw [pcCl_of_le_zero (by linarith), zero_mul]

private lemma pcS_full {K : ℕ} (W : ℕ → Lot K) {τ : ℝ} (k : Fin K) :
    ∀ n : ℕ, (n : ℝ) ≤ τ → pcS W τ n k = W n k - W 0 k := by
  intro n
  induction n with
  | zero => intro _; simp [pcS]
  | succ n ih =>
    intro hn
    push_cast at hn
    have h1 := ih (by linarith)
    unfold pcS at h1 ⊢
    rw [Finset.sum_range_succ, h1, pcCl_of_one_le (by linarith)]
    ring

private lemma pcS_mid {K : ℕ} (W : ℕ → Lot K) {τ : ℝ} (j : ℕ) (hj : (j : ℝ) ≤ τ)
    (hj1 : τ ≤ j + 1) (k : Fin K) :
    ∀ m : ℕ, pcS W τ (j + 1 + m) k = W j k - W 0 k + (τ - j) * (W (j + 1) k - W j k) := by
  intro m
  induction m with
  | zero =>
    have h1 := pcS_full W k j hj
    unfold pcS at h1 ⊢
    rw [Nat.add_zero, Finset.sum_range_succ, h1, pcCl_of_mem (by linarith) (by linarith)]
  | succ m ih =>
    unfold pcS at ih ⊢
    rw [← Nat.add_assoc, Finset.sum_range_succ, ih]
    have : pcCl (τ - ((j + 1 + m : ℕ) : ℝ)) = 0 := by
      apply pcCl_of_le_zero
      push_cast
      have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      linarith
    rw [this, zero_mul, add_zero]

private lemma pcPhi_low {K : ℕ} (W : ℕ → Lot K) (N : ℕ) {τ : ℝ} (hτ : τ ≤ 0) (k : Fin K) :
    pcPhi W N τ k = W 0 k + τ := by
  unfold pcPhi
  rw [pcS_low W hτ, min_eq_left hτ]
  have : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  rw [max_eq_right (by linarith)]
  ring

private lemma pcPhi_high {K : ℕ} (W : ℕ → Lot K) (N : ℕ) {τ : ℝ} (hτ : (N : ℝ) ≤ τ)
    (k : Fin K) : pcPhi W N τ k = W N k + (τ - N) := by
  unfold pcPhi
  have : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  rw [pcS_full W k N hτ, min_eq_right (by linarith), max_eq_left (by linarith)]
  ring

private lemma pcPhi_mid {K : ℕ} (W : ℕ → Lot K) (N j : ℕ) (hjN : j < N) {τ : ℝ}
    (hj : (j : ℝ) ≤ τ) (hj1 : τ ≤ j + 1) (k : Fin K) :
    pcPhi W N τ k = W j k + (τ - j) * (W (j + 1) k - W j k) := by
  unfold pcPhi
  obtain ⟨m, rfl⟩ : ∃ m, N = j + 1 + m := ⟨N - (j + 1), by omega⟩
  have h0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  rw [pcS_mid W j hj hj1 k m, min_eq_right (by linarith), max_eq_right (by push_cast; linarith)]
  ring

private lemma pcPhi_dot_low {K : ℕ} (W : ℕ → Lot K) (N : ℕ) {τ : ℝ} (hτ : τ ≤ 0)
    {p : Lot K} (hp : p ∈ Simplex K) : dot (pcPhi W N τ) p = dot (W 0) p + τ := by
  unfold dot
  simp_rw [pcPhi_low W N hτ, add_mul, Finset.sum_add_distrib, ← Finset.mul_sum, hp.2, mul_one]

private lemma pcPhi_dot_high {K : ℕ} (W : ℕ → Lot K) (N : ℕ) {τ : ℝ} (hτ : (N : ℝ) ≤ τ)
    {p : Lot K} (hp : p ∈ Simplex K) : dot (pcPhi W N τ) p = dot (W N) p + (τ - N) := by
  unfold dot
  simp_rw [pcPhi_high W N hτ, add_mul, Finset.sum_add_distrib, ← Finset.mul_sum, hp.2, mul_one]

theorem path_of_strict_chain {K : ℕ} (W : ℕ → Lot K) (N : ℕ)
    (hW : ∀ i, StrictMono (W i)) (hstep : ∀ i k, W i k < W (i + 1) k) :
    ∃ Φ : ℝ → Lot K, Continuous Φ ∧ (∀ τ, StrictMono (Φ τ)) ∧
      (∀ τ τ' : ℝ, τ < τ' → ∀ k, Φ τ k < Φ τ' k) ∧
      (∀ p ∈ Simplex K, ∃ τ, dot (Φ τ) p < 0) ∧
      (∀ p ∈ Simplex K, ∃ τ, 0 < dot (Φ τ) p) ∧
      ∀ i : ℕ, i ≤ N → Φ (i : ℝ) = W i := by
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  refine ⟨pcPhi W N, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- continuity
    apply continuous_pi
    intro k
    unfold pcPhi pcS
    have hc : ∀ i : ℕ, Continuous fun τ : ℝ => pcCl (τ - i) := fun i =>
      pcCl_cont.comp (continuous_id.sub continuous_const)
    have hs : Continuous fun τ : ℝ =>
        ∑ i ∈ Finset.range N, pcCl (τ - i) * (W (i + 1) k - W i k) :=
      continuous_finsetSum _ fun i _ => (hc i).mul continuous_const
    exact (continuous_const.add hs).add
      ((continuous_id.min continuous_const).add
        ((continuous_id.sub continuous_const).max continuous_const))
  · -- strict monotonicity in the prize index
    intro τ k k' hkk'
    rcases le_or_gt τ 0 with hτ | hτ
    · rw [pcPhi_low W N hτ, pcPhi_low W N hτ]
      linarith [hW 0 hkk']
    rcases le_or_gt (N : ℝ) τ with hτN | hτN
    · rw [pcPhi_high W N hτN, pcPhi_high W N hτN]
      linarith [hW N hkk']
    set j := ⌊τ⌋₊ with hjdef
    have hj : (j : ℝ) ≤ τ := Nat.floor_le hτ.le
    have hj1 : τ < j + 1 := Nat.lt_floor_add_one τ
    have hjN : j < N := by
      have : (j : ℝ) < N := lt_of_le_of_lt hj hτN
      exact_mod_cast this
    rw [pcPhi_mid W N j hjN hj hj1.le, pcPhi_mid W N j hjN hj hj1.le]
    have ha := hW j hkk'
    have hb := hW (j + 1) hkk'
    have hθ0 : 0 ≤ τ - j := by linarith
    have hθ1 : 0 ≤ 1 - (τ - j) := by linarith
    nlinarith [mul_nonneg hθ0 (sub_nonneg.2 hb.le), mul_nonneg hθ1 (sub_nonneg.2 ha.le)]
  · -- strict increase in τ
    intro τ τ' hlt k
    unfold pcPhi
    have hmono : pcS W τ N k ≤ pcS W τ' N k := by
      unfold pcS
      apply Finset.sum_le_sum
      intro i _
      exact mul_le_mul_of_nonneg_right (pcCl_mono (by linarith))
        (sub_nonneg.2 (hstep i k).le)
    have hmin : min τ 0 ≤ min τ' 0 := min_le_min hlt.le le_rfl
    have hmax : max (τ - N) 0 ≤ max (τ' - N) 0 := max_le_max (by linarith) le_rfl
    rcases lt_or_ge τ 0 with hτ | hτ
    · have : min τ 0 < min τ' 0 := by
        rw [min_eq_left hτ.le]; exact lt_min hlt hτ
      linarith
    rcases lt_or_ge (N : ℝ) τ' with hτ' | hτ'
    · have : max (τ - N) 0 < max (τ' - N) 0 := by
        rw [max_eq_left (by linarith : (0:ℝ) ≤ τ' - N)]
        exact max_lt (by linarith) (by linarith)
      linarith
    -- 0 ≤ τ < τ' ≤ N
    set j := ⌊τ⌋₊ with hjdef
    have hj : (j : ℝ) ≤ τ := Nat.floor_le hτ
    have hj1 : τ < j + 1 := Nat.lt_floor_add_one τ
    have hjN : j < N := by
      have : (j : ℝ) < N := lt_of_le_of_lt hj (lt_of_lt_of_le hlt hτ')
      exact_mod_cast this
    have hstrict : pcS W τ N k < pcS W τ' N k := by
      unfold pcS
      apply Finset.sum_lt_sum
      · intro i _
        exact mul_le_mul_of_nonneg_right (pcCl_mono (by linarith))
          (sub_nonneg.2 (hstep i k).le)
      · refine ⟨j, Finset.mem_range.2 hjN, ?_⟩
        apply mul_lt_mul_of_pos_right _ (sub_pos.2 (hstep j k))
        rw [pcCl_of_mem (by linarith) (by linarith)]
        unfold pcCl
        exact lt_max_of_lt_right (lt_min (by linarith) (by linarith))
    linarith
  · -- low
    intro p hp
    refine ⟨-|dot (W 0) p| - 1, ?_⟩
    have hle : -|dot (W 0) p| - 1 ≤ 0 := by linarith [abs_nonneg (dot (W 0) p)]
    rw [pcPhi_dot_low W N hle hp]
    linarith [le_abs_self (dot (W 0) p)]
  · -- high
    intro p hp
    refine ⟨N + |dot (W N) p| + 1, ?_⟩
    have hle : (N : ℝ) ≤ N + |dot (W N) p| + 1 := by linarith [abs_nonneg (dot (W N) p)]
    rw [pcPhi_dot_high W N hle hp]
    linarith [neg_abs_le (dot (W N) p)]
  · -- interpolation
    intro i hi
    funext k
    rcases lt_or_eq_of_le hi with hi | rfl
    · rw [pcPhi_mid W N i hi le_rfl (by linarith) k]
      ring
    · rw [pcPhi_high W i le_rfl k]
      ring

end K4
