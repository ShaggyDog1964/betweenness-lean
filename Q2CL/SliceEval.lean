import Q2CL.Defs

namespace Q2CL

open K4

/-- Lemma 75(1) (slice evaluation): a normalized vector acts on slice `s` as its effective line,
and on `R(o)` through `V - oS`. -/
theorem slice_eval (U S V s t L V' : ℝ) (hs : s < 1) (hk : 1 + cOf s * V ≠ 0)
    (hH : 1 + hLift s L V' ≠ 0) (o : ℝ) (ho : 1 + o ≠ 0) :
    fval U S V (liftPt s t L V') =
      (1 - s) * (1 + cOf s * V) / (1 + hLift s L V') *
        (hLift s L V' - ((U - cOf s * V) * (1 - t) + (S - cOf s * V) * t) / (1 + cOf s * V)) ∧
    fval U S V (Rlot o) = (V - o * S) / (1 + o) := by
  constructor
  · have h1 : (1 - s) ≠ 0 := by linarith
    have hc : s = cOf s * (1 - s) := by unfold cOf; field_simp
    simp only [fval, liftPt, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons, Matrix.cons_val_three]
    generalize hLift s L V' = H at hH ⊢
    generalize cOf s = c at hk hc ⊢
    have hVs : V * s = V * (c * (1 - s)) := by rw [← hc]
    rw [hVs]
    have hk' : 1 + V * c ≠ 0 := by rwa [mul_comm]
    field_simp
    ring
  · simp only [fval, Rlot, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons, Matrix.cons_val_three]
    field_simp
    ring

end Q2CL
