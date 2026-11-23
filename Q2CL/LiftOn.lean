import Q2CL.Defs
import Q2CL.SliceEval

namespace Q2CL

open K4

/-- Lemma 75(2): a point lifted from the line `(U, S)` with that line's `V` lies on the
line's tight vector. -/
theorem lift_on (U S V s t : ℝ) (hs : s < 1) (hk : 1 + cOf s * V ≠ 0)
    (hH : 1 + hLift s (U * (1 - t) + S * t) V ≠ 0) :
    fval U S V (liftPt s t (U * (1 - t) + S * t) V) = 0 := by
  rw [(slice_eval U S V s t (U * (1 - t) + S * t) V hs hk hH 0 (by norm_num)).1]
  have h : hLift s (U * (1 - t) + S * t) V -
      ((U - cOf s * V) * (1 - t) + (S - cOf s * V) * t) / (1 + cOf s * V) = 0 := by
    unfold hLift
    rw [← sub_div, div_eq_zero_iff]
    left; ring
  rw [h, mul_zero]

end Q2CL
