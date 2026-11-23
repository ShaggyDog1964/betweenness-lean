import Q2CL.Defs
import Q2CL.CwBound
import Q2CL.SliceEval
import Q2CL.TMemSimplex
import Q2CL.JSpec
import Q2CL.WEnvelope

namespace Q2CL

open K4

private lemma dot4 (w p : Lot 4) : dot w p = w 0 * p 0 + w 1 * p 1 + w 2 * p 2 + w 3 * p 3 := by
  unfold dot; rw [Fin.sum_univ_four]

private lemma dot_Rlot (w : Lot 4) (o : ℝ) (ho : 0 < o) :
    dot w (Rlot o) = (o * w 1 + w 3) / (1 + o) := by
  have h1 : (1 + o) ≠ 0 := by linarith
  rw [dot4]
  simp only [Rlot, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Matrix.cons_val_three]
  field_simp
  ring

/-- Normal form of a chain of `T(m, ns, ds)` (proof of Proposition 71, non-representability):
for `1 ≤ i ≤ 4J`,
`W i = λ (-U, -S, 1, V)` with `λ > 0`, `U > S > 0`, `V > 1`; `ω = V/S = W i 3 / (-W i 1)` and
`ω/r = V/U = W i 3 / (-W i 0)` are nondecreasing; `ω_1 > o_0` and `ω_{4J} < o_1`. -/
theorem chain_normal {m ns : ℕ} {ds : ℝ} (hA : Adm m ns ds) (W : ℕ → Lot 4)
    (hW : IsChainFn (4 * Jn m ns + 2) (Tpt m ns ds) W) :
    (∀ i, 1 ≤ i → i ≤ 4 * Jn m ns →
      0 < W i 2 ∧ W i 1 < 0 ∧ W i 0 < W i 1 ∧ W i 2 < W i 3) ∧
    (∀ i, 1 ≤ i → i < 4 * Jn m ns →
      W i 3 / -W i 1 ≤ W (i + 1) 3 / -W (i + 1) 1 ∧
      W i 3 / -W i 0 ≤ W (i + 1) 3 / -W (i + 1) 0) ∧
    o0 < W 1 3 / -W 1 1 ∧ W (4 * Jn m ns) 3 / -W (4 * Jn m ns) 1 < o1 m ns := by
  obtain ⟨hC, hN⟩ := hW
  obtain ⟨-, -, hJ2, -, -, -⟩ := J_spec hA
  have ho0 : (0 : ℝ) < o0 := by unfold o0; norm_num
  have ho1 : o0 ≤ o1 m ns := by
    have := ((w_envelope hA).1 (Jn m ns) le_rfl).1; unfold o1; exact this
  have ho1p : 0 < o1 m ns := by linarith
  have hlt : ∀ i, i ≤ 4 * Jn m ns → ∀ a b : Fin 4, a < b → W i a < W i b :=
    fun i hi a b hab => (hC i (by omega)).1 hab
  -- nesting propagated
  have hNest : ∀ i k, i + k ≤ 4 * Jn m ns → ∀ c : Fin 4, W i c ≤ W (i + k) c := by
    intro i k
    induction k with
    | zero => intro _ c; simp
    | succ k ih =>
      intro hk c
      have h1 := ih (by omega) c
      have h2 := hN (i + k) (by omega) c
      rw [← add_assoc]; exact le_trans h1 h2
  have hNest' : ∀ i j, i ≤ j → j ≤ 4 * Jn m ns → ∀ c : Fin 4, W i c ≤ W j c := by
    intro i j hij hj c
    have := hNest i (j - i) (by omega) c
    rwa [show i + (j - i) = j by omega] at this
  -- Step 1: W 1 2 > 0
  have hp1 : Tpt m ns ds 1 = gpt m ns ds 0 0 := by
    unfold Tpt; rw [if_neg (by omega), if_neg (by omega)]
  have hp13 : Tpt m ns ds 1 3 = 0 := by
    rw [hp1]; simp [gpt, liftPt, sig]
  have hmem := T_mem_simplex hA 1 (by omega)
  have hW12 : 0 < W 1 2 := by
    by_contra hneg
    push_neg at hneg
    have hpos := (hC 1 (by omega)).2.1
    rw [dot4, hp13] at hpos
    have a0 := hmem.1 0
    have a1 := hmem.1 1
    have a2 := hmem.1 2
    have l01 := hlt 1 (by omega) 0 2 (by decide)
    have l11 := hlt 1 (by omega) 1 2 (by decide)
    nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ -W 1 0) a0,
      mul_nonneg (by linarith : (0:ℝ) ≤ -W 1 1) a1,
      mul_nonneg (by linarith : (0:ℝ) ≤ -W 1 2) a2]
  -- Step 2: end of chain
  have hpE : Tpt m ns ds (4 * Jn m ns + 1) = Rlot (o1 m ns) := by
    unfold Tpt; rw [if_neg (by omega), if_pos rfl]
  have hEneg := (hC (4 * Jn m ns) (by omega)).2.2
  rw [hpE, dot_Rlot _ _ ho1p] at hEneg
  have hE : o1 m ns * W (4 * Jn m ns) 1 + W (4 * Jn m ns) 3 < 0 := by
    have h1o : (0:ℝ) < 1 + o1 m ns := by linarith
    by_contra h; push_neg at h
    have := div_nonneg h h1o.le
    linarith
  have hW2pos : ∀ i, 1 ≤ i → i ≤ 4 * Jn m ns → 0 < W i 2 := by
    intro i h1 h2; have := hNest' 1 i h1 h2 2; linarith
  have hE3 : 0 < W (4 * Jn m ns) 3 := by
    have := hW2pos (4 * Jn m ns) (by omega) le_rfl
    have := hlt (4 * Jn m ns) le_rfl 2 3 (by decide); linarith
  have hE1 : W (4 * Jn m ns) 1 < 0 := by
    by_contra h; push_neg at h
    have := mul_nonneg ho1p.le h
    linarith
  have hW1neg : ∀ i, i ≤ 4 * Jn m ns → W i 1 < 0 := by
    intro i h2; have := hNest' i (4 * Jn m ns) h2 le_rfl 1; linarith
  -- Step 3: start of chain
  have hp0 : Tpt m ns ds 0 = Rlot o0 := by unfold Tpt; rw [if_pos rfl]
  have hSpos := (hC 0 (by omega)).2.1
  rw [hp0, dot_Rlot _ _ ho0] at hSpos
  have hS : 0 < o0 * W 0 1 + W 0 3 := by
    have h1o : (0:ℝ) < 1 + o0 := by linarith
    by_contra h; push_neg at h
    have : (o0 * W 0 1 + W 0 3) / (1 + o0) ≤ 0 := div_nonpos_of_nonpos_of_nonneg h h1o.le
    linarith
  have hS' : 0 < o0 * W 1 1 + W 1 3 := by
    have a := hN 0 (by omega) 1
    have b := hN 0 (by omega) 3
    simp only [zero_add] at a b
    have := mul_le_mul_of_nonneg_left a ho0.le
    linarith
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i h1 h2
    exact ⟨hW2pos i h1 h2, hW1neg i h2, hlt i h2 0 1 (by decide), hlt i h2 2 3 (by decide)⟩
  · intro i h1 h2
    have a1 := hW1neg i (by omega)
    have b1 := hW1neg (i + 1) (by omega)
    have a0 := hlt i (by omega) 0 1 (by decide)
    have b0 := hlt (i + 1) (by omega) 0 1 (by decide)
    have a3 : 0 < W i 3 := by
      have := hW2pos i h1 (by omega); have := hlt i (by omega) 2 3 (by decide); linarith
    have n0 := hN i (by omega) 0
    have n1 := hN i (by omega) 1
    have n3 := hN i (by omega) 3
    constructor
    · rw [div_le_div_iff₀ (by linarith) (by linarith)]
      nlinarith [mul_le_mul_of_nonneg_left n3 (by linarith : (0:ℝ) ≤ -W i 1),
        mul_le_mul_of_nonneg_left n1 a3.le]
    · rw [div_le_div_iff₀ (by linarith) (by linarith)]
      nlinarith [mul_le_mul_of_nonneg_left n3 (by linarith : (0:ℝ) ≤ -W i 0),
        mul_le_mul_of_nonneg_left n0 a3.le]
  · have a1 := hW1neg 1 (by omega)
    rw [lt_div_iff₀ (by linarith)]; linarith
  · rw [div_lt_iff₀ (by linarith)]; linarith

end Q2CL
