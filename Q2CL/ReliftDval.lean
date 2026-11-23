import Q2CL.Defs

namespace Q2CL

open K4

/-- First-order effect of the re-lift direction on an on-point: rotating the effective line by
`(r0, r1)` while moving `log V` by `v` (with `U`, `S` re-lifted) changes the value at a point of
the line's slice by `-(1-s)(1+κ)/(1+H') · (r0(1-t) + r1 t)`, independently of `v`. -/
theorem relift_dval (U S V s t r0 r1 v : ℝ) (hs : s < 1) (hk : 0 < 1 + cOf s * V)
    (hU : U ≠ 0) (hS : S ≠ 0) (hH : 1 + hLift s (U * (1 - t) + S * t) V ≠ 0) :
    -(U * (((1 + cOf s * V) * r0 +
        ((U - cOf s * V) / (1 + cOf s * V) + 1) * (cOf s * V) * v) / U)) *
        liftPt s t (U * (1 - t) + S * t) V 0 -
      S * (((1 + cOf s * V) * r1 +
        ((S - cOf s * V) / (1 + cOf s * V) + 1) * (cOf s * V) * v) / S) *
        liftPt s t (U * (1 - t) + S * t) V 1 +
      V * v * liftPt s t (U * (1 - t) + S * t) V 3 =
    -((1 - s) * (1 + cOf s * V) / (1 + hLift s (U * (1 - t) + S * t) V)) *
      (r0 * (1 - t) + r1 * t) := by
  have h1s : (1 - s) ≠ 0 := by intro h; linarith
  have hk' : 1 + cOf s * V ≠ 0 := ne_of_gt hk
  have e2 : 1 + hLift s (U * (1 - t) + S * t) V
      = (1 + (U * (1 - t) + S * t)) / (1 + cOf s * V) := by
    unfold hLift; field_simp; ring
  have hL : 1 + (U * (1 - t) + S * t) ≠ 0 := by
    intro h0; apply hH; rw [e2, h0, zero_div]
  have e1 : 1 - hLift s (U * (1 - t) + S * t) V / (1 + hLift s (U * (1 - t) + S * t) V)
      = 1 / (1 + hLift s (U * (1 - t) + S * t) V) := by
    rw [eq_div_iff hH, sub_mul, div_mul_cancel₀ _ hH]; ring
  simp only [liftPt, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val, e1]
  rw [e2]
  have hsc : s = (1 - s) * cOf s := by unfold cOf; field_simp
  rw [show V * v * s = V * v * ((1 - s) * cOf s) by rw [← hsc]]
  generalize cOf s = c at *
  have hL2 : 1 + U - U * t + t * S ≠ 0 := by intro h0; apply hL; linarith
  have hD : (1 + U - U * t + t * S) * (1 + U - U * t + t * S)⁻¹ = 1 := mul_inv_cancel₀ hL2
  field_simp
  ring_nf
  linear_combination (-(c * V * v)) * hD

end Q2CL
