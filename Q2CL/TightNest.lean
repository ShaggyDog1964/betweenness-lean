import Q2CL.Defs
import Q2CL.RhoBounds
import Q2CL.WEnvelope

namespace Q2CL

open K4

private lemma rho_eq (m ns j : ℕ) (hSB : 0 < SB m ns j) (hUA : 0 < UA m ns j) :
    rho m ns j * SB m ns j * UA m ns j = UB m ns j * SA m ns j := by
  unfold rho; field_simp

private lemma wA_succ' (m ns k : ℕ) : wA m ns (k + 1) = wA m ns k * rho m ns k := by
  unfold wA; rw [Finset.prod_range_succ]; ring

/-- Nesting data of the tight vectors (Lemma 79, nesting): the `A → B` and `B → A'` steps are
equalities in `V` against the binding coordinate and strict in the other, and the two saving
steps `B_j → B_{j+1}`, `A_j → A_{j+1}` are strict in every coordinate. -/
theorem tight_nest {m ns : ℕ} {ds : ℝ} (hA : Adm m ns ds) :
    (∀ j, j < Jn m ns →
      VB m ns j * UA m ns j = VA m ns j * UB m ns j ∧
      SB m ns j * UA m ns j < UB m ns j * SA m ns j) ∧
    (∀ j, j + 1 < Jn m ns →
      VA m ns (j + 1) * SB m ns j = VB m ns j * SA m ns (j + 1) ∧
      UA m ns (j + 1) * SB m ns j < UB m ns j * SA m ns (j + 1) ∧
      UB m ns (j + 1) * VB m ns j < VB m ns (j + 1) * UB m ns j ∧
      SB m ns (j + 1) * VB m ns j < VB m ns (j + 1) * SB m ns j ∧
      UA m ns (j + 1) * VA m ns j < VA m ns (j + 1) * UA m ns j ∧
      SA m ns (j + 1) * VA m ns j < VA m ns (j + 1) * SA m ns j) := by
  obtain ⟨hg0, hg1, -, hJ, -, -⟩ := J_spec hA
  have hGL := gadget_lines hA
  have hRB := rho_bounds hA
  have hWE := w_envelope hA
  have ho0 : (0 : ℝ) < o0 := by unfold o0; norm_num
  have hpos : ∀ j, j < Jn m ns → 0 < SB m ns j ∧ 0 < SA m ns j ∧ 0 < UA m ns j ∧
      0 < UB m ns j := by
    intro j hj
    obtain ⟨h1, h2, h3, h4, -⟩ := hGL.1 j hj
    have hlt : 0 < SB m ns j := by linarith
    exact ⟨hlt, by linarith, by linarith, by linarith⟩
  have hw : ∀ j, j < Jn m ns → 0 < wA m ns j := fun j hj =>
    lt_of_lt_of_le ho0 (hWE.1 j hj.le).1
  have hr1 : ∀ j, j < Jn m ns → 1 < rho m ns j := by
    intro j hj
    have h := (hRB.1 j hj).1
    have hH : 0 < Hh m ns j := by
      have h1 := (hJ j hj).1
      have he : 0 ≤ gP m ns * epsJ m ns j := by
        apply mul_nonneg hg0.le
        unfold epsJ feps fa' fa fb uOf dlt; positivity
      linarith
    have : 0 < gP m ns / (2 * Hh m ns j) := by positivity
    linarith
  refine ⟨fun j hj => ?_, fun j hj => ?_⟩
  · obtain ⟨hSB, hSA, hUA, hUB⟩ := hpos j hj
    have er := rho_eq m ns j hSB hUA
    have hr := hr1 j hj
    constructor
    · unfold VB VA wB
      linear_combination wA m ns j * er
    · have hd : 0 < SB m ns j * UA m ns j * (rho m ns j - 1) :=
        mul_pos (mul_pos hSB hUA) (by linarith)
      linear_combination hd + er
  · have hj' : j < Jn m ns := by omega
    obtain ⟨hSB, hSA, hUA, hUB⟩ := hpos j hj'
    obtain ⟨hSB', hSA', hUA', hUB'⟩ := hpos (j + 1) hj
    have er := rho_eq m ns j hSB hUA
    have er' := rho_eq m ns (j + 1) hSB' hUA'
    have hw0 := hw j hj'
    have hr := hr1 j hj'
    have hr' := hr1 (j + 1) hj
    have h4 : UA m ns (j + 1) * SB m ns j < UB m ns j * SA m ns (j + 1) := by
      have := hRB.2 j hj
      rwa [div_lt_div_iff₀ hSA' hSB] at this
    have eVA : VA m ns (j + 1) = wA m ns j * rho m ns j * SA m ns (j + 1) := by
      unfold VA; rw [wA_succ']
    have eVB' : VB m ns (j + 1) =
        wA m ns j * rho m ns j * rho m ns (j + 1) * SB m ns (j + 1) := by
      unfold VB wB; rw [wA_succ']
    have eVB : VB m ns j = wA m ns j * rho m ns j * SB m ns j := rfl
    have eVA0 : VA m ns j = wA m ns j * SA m ns j := rfl
    have hwr : 0 < wA m ns j * rho m ns j := mul_pos hw0 (by linarith)
    refine ⟨?_, h4, ?_, ?_, ?_, ?_⟩
    · rw [eVA, eVB]; ring
    · rw [eVB', eVB]
      have hd : 0 < wA m ns j * rho m ns j * UB m ns (j + 1) *
          (UB m ns j * SA m ns (j + 1) - UA m ns (j + 1) * SB m ns j) :=
        mul_pos (mul_pos hwr hUB') (by linarith)
      refine lt_of_mul_lt_mul_right ?_ hUA'.le
      linear_combination hd - wA m ns j * rho m ns j * UB m ns j * er'
    · rw [eVB', eVB]
      have hd : 0 < wA m ns j * rho m ns j * SB m ns (j + 1) * SB m ns j *
          (rho m ns (j + 1) - 1) :=
        mul_pos (mul_pos (mul_pos hwr hSB') hSB) (by linarith)
      linear_combination hd
    · rw [eVA, eVA0]
      have hd : 0 < wA m ns j * SA m ns j *
          (UB m ns j * SA m ns (j + 1) - UA m ns (j + 1) * SB m ns j) :=
        mul_pos (mul_pos hw0 hSA) (by linarith)
      refine lt_of_mul_lt_mul_right ?_ hSB.le
      linear_combination hd - wA m ns j * SA m ns (j + 1) * er
    · rw [eVA, eVA0]
      have hd : 0 < wA m ns j * SA m ns (j + 1) * SA m ns j * (rho m ns j - 1) :=
        mul_pos (mul_pos (mul_pos hw0 hSA') hSA) (by linarith)
      linear_combination hd

end Q2CL
