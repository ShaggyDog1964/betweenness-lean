import Q2CL.Defs
import Q2CL.GadgetLines
import Q2CL.CwBound
import Q2CL.WEnvelope
import Q2CL.JSpec

namespace Q2CL

open K4

private lemma tm_mono {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 ≤ c) :
    StrictMonoOn (fun ω : ℝ => ω * b / (a + c * ω * (b - a)))
      {ω : ℝ | 0 < ω ∧ c * ω < 1} := by
  intro x hx y hy hxy
  obtain ⟨hx0, hx1⟩ := hx
  obtain ⟨hy0, hy1⟩ := hy
  have hDx : 0 < a + c * x * (b - a) := by
    have h0 : 0 ≤ c * x := mul_nonneg hc hx0.le
    nlinarith [mul_nonneg h0 hb.le, mul_pos (sub_pos.2 hx1) ha]
  have hDy : 0 < a + c * y * (b - a) := by
    have h0 : 0 ≤ c * y := mul_nonneg hc hy0.le
    nlinarith [mul_nonneg h0 hb.le, mul_pos (sub_pos.2 hy1) ha]
  show x * b / (a + c * x * (b - a)) < y * b / (a + c * y * (b - a))
  rw [div_lt_div_iff₀ hDx hDy]
  nlinarith [mul_pos (mul_pos ha hb) (sub_pos.2 hxy)]

/-- Lemma 78 (transfer map): `F_j` is strictly increasing on `{ω > 0, c_j ω < 1}` and maps
`w_A(j)` to `w_B(j)`. -/
theorem transfer_map {m ns : ℕ} {ds : ℝ} (hA : Adm m ns ds) :
    ∀ j, j < Jn m ns →
      StrictMonoOn (transF m ns ds j) {ω : ℝ | 0 < ω ∧ cOf (sig ns ds j) * ω < 1} ∧
      transF m ns ds j (wA m ns j) = wB m ns j := by
  intro j hj
  obtain ⟨hg0, hg1, -, -, -, -⟩ := J_spec hA
  obtain ⟨hSB, hSBA, hSAU, hSBU, -⟩ := (gadget_lines hA).1 j hj
  obtain ⟨hs0, hs1, hpA, hpB, -, -, -⟩ := cw_bound hA j hj
  have hwA : 0 < wA m ns j := by
    have := ((w_envelope hA).1 j hj.le).1
    unfold o0 at this; linarith
  have hc : 0 ≤ cOf (sig ns ds j) := by
    unfold cOf; apply div_nonneg hs0; linarith
  have hSBp : 0 < SB m ns j := by linarith
  have hSAp : 0 < SA m ns j := by linarith
  have hrA1 : 1 < UA m ns j / SA m ns j := by rw [one_lt_div hSAp]; exact hSAU
  have hrB1 : 1 < UB m ns j / SB m ns j := by rw [one_lt_div hSBp]; exact hSBU
  have hwB : wB m ns j = wA m ns j * (UB m ns j / SB m ns j) / (UA m ns j / SA m ns j) := by
    unfold wB rho; field_simp
  unfold transF
  generalize UA m ns j / SA m ns j = rA at hrA1 hwB ⊢
  generalize UB m ns j / SB m ns j = rB at hrB1 hwB ⊢
  generalize cOf (sig ns ds j) = c at hc hpA hpB ⊢
  rw [hwB] at hpB ⊢
  generalize wA m ns j = w at hwA hpA hpB ⊢
  have hrA0 : rA ≠ 0 := by linarith
  have hp1 : c * w < 1 := by linarith
  have hq1 : c * (w * rB / rA) < 1 := by linarith
  have hEA : 0 < rEff rA (c * w) := by unfold rEff; apply div_pos <;> linarith
  have hEB : 0 < rEff rB (c * (w * rB / rA)) := by unfold rEff; apply div_pos <;> linarith
  refine ⟨tm_mono hEA hEB hc, ?_⟩
  have hp0 : 0 ≤ c * w := mul_nonneg hc hwA.le
  have hD : rEff rA (c * w) + c * w * (rEff rB (c * (w * rB / rA)) - rEff rA (c * w)) ≠ 0 := by
    nlinarith [mul_nonneg hp0 hEB.le, mul_pos (sub_pos.2 hp1) hEA]
  rw [div_eq_iff hD]
  have hq' : 1 - c * (w * rB / rA) = (rA - c * w * rB) / rA := by field_simp
  have hRq : rA - c * w * rB ≠ 0 := by
    intro h; rw [h, zero_div] at hq'; linarith
  have hp1' : 1 - c * w ≠ 0 := by linarith
  unfold rEff
  rw [hq', show c * (w * rB / rA) = c * w * rB / rA by ring]
  generalize c * w = p at hRq hp1' ⊢
  have hX : (rB - p * rB / rA) / ((rA - p * rB) / rA) = rB * (rA - p) / (rA - p * rB) := by
    rw [div_eq_div_iff (div_ne_zero hRq hrA0) hRq]
    field_simp
  rw [hX]
  have hK : (rA - p) / (1 - p) + p * (rB * (rA - p) / (rA - p * rB) - (rA - p) / (1 - p))
      = rA * (rA - p) / (rA - p * rB) := by
    rw [eq_div_iff hRq]
    field_simp
    ring
  rw [hK]
  field_simp

end Q2CL
