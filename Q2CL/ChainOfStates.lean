import Q2CL.Defs

namespace Q2CL

open K4

/-- Scaling factors `λ_i` for `chainFn_of_states`. -/
private noncomputable def lamSeq (n : ℕ) (U S : ℕ → ℝ) : ℕ → ℝ
  | 0 => 1
  | i + 1 => if i + 2 < n then lamSeq n U S i / max (U (i + 1) / U i) (S (i + 1) / S i)
      else lamSeq n U S i

private lemma lamSeq_pos (n : ℕ) (U S : ℕ → ℝ)
    (hpos : ∀ i, i + 1 < n → 0 < S i ∧ S i < U i) : ∀ i, 0 < lamSeq n U S i
  | 0 => by simp [lamSeq]
  | i + 1 => by
    have ih := lamSeq_pos n U S hpos i
    simp only [lamSeq]
    split_ifs with h
    · have h1 := hpos (i + 1) (by omega)
      have h0 := hpos i (by omega)
      have ha : 0 < U (i + 1) / U i := div_pos (by linarith) (by linarith)
      exact div_pos ih (lt_of_lt_of_le ha (le_max_left _ _))
    · exact ih

/-- Normalized states `(U, S, V)` with ratio nesting give a chain (rescale by `λ`). -/
theorem chainFn_of_states (n : ℕ) (p : ℕ → Lot 4) (U S V : ℕ → ℝ)
    (hpos : ∀ i, i + 1 < n → 0 < S i ∧ S i < U i ∧ 1 < V i)
    (hnest : ∀ i, i + 2 < n → U (i + 1) ≤ U i ∧ S (i + 1) ≤ S i ∧
      U (i + 1) * V i ≤ V (i + 1) * U i ∧ S (i + 1) * V i ≤ V (i + 1) * S i)
    (hrel : ∀ i, i + 1 < n → 0 < fval (U i) (S i) (V i) (p i) ∧
      fval (U i) (S i) (V i) (p (i + 1)) < 0) :
    ∃ W, IsChainFn n p W := by
  have hlam := lamSeq_pos n U S (fun i hi => ⟨(hpos i hi).1, (hpos i hi).2.1⟩)
  set lam := lamSeq n U S with hlamdef
  have hdot : ∀ i q, dot (lam i • tvec (U i) (S i) (V i)) q
      = lam i * fval (U i) (S i) (V i) q := by
    intro i q
    simp only [dot, fval, tvec, Fin.sum_univ_four, Pi.smul_apply, smul_eq_mul]
    simp
    ring
  refine ⟨fun i => lam i • tvec (U i) (S i) (V i), ?_, ?_⟩
  · intro i hi
    obtain ⟨hS, hSU, hV⟩ := hpos i hi
    obtain ⟨h1, h2⟩ := hrel i hi
    have hl := hlam i
    refine ⟨?_, ?_, ?_⟩
    · rw [Fin.strictMono_iff_lt_succ]
      intro k
      fin_cases k <;> simp [tvec, Pi.smul_apply, smul_eq_mul] <;> nlinarith
    · rw [hdot]; exact mul_pos hl h1
    · rw [hdot]; exact mul_neg_of_pos_of_neg hl h2
  · intro i hi
    obtain ⟨hS, hSU, hV⟩ := hpos i (by omega)
    obtain ⟨hS', hSU', hV'⟩ := hpos (i + 1) (by omega)
    obtain ⟨n1, n2, n3, n4⟩ := hnest i hi
    have hl := hlam i
    have hU : 0 < U i := by linarith
    have hU' : 0 < U (i + 1) := by linarith
    set a := U (i + 1) / U i with ha
    set b := S (i + 1) / S i with hb
    have ha0 : 0 < a := div_pos hU' hU
    have hb0 : 0 < b := div_pos hS' hS
    have ha1 : a ≤ 1 := (div_le_one hU).2 n1
    have hb1 : b ≤ 1 := (div_le_one hS).2 n2
    have haV : a * V i ≤ V (i + 1) := by
      rw [ha, div_mul_eq_mul_div, div_le_iff₀ hU]; linarith
    have hbV : b * V i ≤ V (i + 1) := by
      rw [hb, div_mul_eq_mul_div, div_le_iff₀ hS]; linarith
    set μ := max a b with hμ
    have hμ0 : 0 < μ := lt_of_lt_of_le ha0 (le_max_left _ _)
    have hμ1 : μ ≤ 1 := max_le ha1 hb1
    have hμV : μ * V i ≤ V (i + 1) := by
      rcases le_total a b with h | h
      · rw [hμ, max_eq_right h]; exact hbV
      · rw [hμ, max_eq_left h]; exact haV
    have haμ : a ≤ μ := le_max_left _ _
    have hbμ : b ≤ μ := le_max_right _ _
    have hnext : lam (i + 1) = lam i / μ := by
      rw [hlamdef]
      show lamSeq n U S (i + 1) = _
      simp only [lamSeq, if_pos hi]
      rfl
    -- U(i+1) ≤ μ U i, S(i+1) ≤ μ S i
    have hUa : U (i + 1) ≤ μ * U i := by
      have : U (i + 1) = a * U i := by rw [ha]; field_simp
      rw [this]; exact mul_le_mul_of_nonneg_right haμ hU.le
    have hSb : S (i + 1) ≤ μ * S i := by
      have : S (i + 1) = b * S i := by rw [hb]; field_simp
      rw [this]; exact mul_le_mul_of_nonneg_right hbμ hS.le
    intro k
    simp only [hnext]
    fin_cases k <;> simp [tvec, Pi.smul_apply, smul_eq_mul]
    · rw [div_mul_eq_mul_div, div_le_iff₀ hμ0]; nlinarith
    · rw [div_mul_eq_mul_div, div_le_iff₀ hμ0]; nlinarith
    · rw [le_div_iff₀ hμ0]; nlinarith
    · rw [div_mul_eq_mul_div, le_div_iff₀ hμ0]; nlinarith

end Q2CL
