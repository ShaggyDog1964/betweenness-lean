/-
`lift_strictMono` (Claim A in the proof of Theorem 36(2), the lift `u = v + M w`).
-/
import Q3L.Statement

namespace Q3L

open K4 (Lot)

/-- Adding a large multiple of a strictly increasing `w` makes any `v` strictly increasing.
Sketch. For `i < j` in `Fin K`, `w j - w i > 0`. The finite set of ratios
`(|v i| + |v j| + 1) / (w j - w i)` over pairs `i < j` is bounded above
(`Finset.exists_le` / `Set.Finite.bddAbove` on `Finset.univ ×ˢ Finset.univ`); take `M` such a
bound (and `M ≥ 0`). Then `v j + M * w j - (v i + M * w i) = (v j - v i) + M * (w j - w i)
≥ (v j - v i) + |v i| + |v j| + 1 > 0`. Evaluate `(v + M • w) k = v k + M * w k`
(`Pi.add_apply`, `Pi.smul_apply`, `smul_eq_mul`). -/
theorem lift_strictMono {K : ℕ} {w : Lot K} (hw : StrictMono w) (v : Lot K) :
    ∃ M : ℝ, StrictMono (v + M • w) := by
  classical
  let f : Fin K × Fin K → ℝ := fun p =>
    if p.1 < p.2 then (|v p.1| + |v p.2| + 1) / (w p.2 - w p.1) else 0
  have hf : ∀ p, 0 ≤ f p := by
    intro p
    simp only [f]
    split_ifs with h
    · have : 0 < w p.2 - w p.1 := sub_pos.mpr (hw h)
      positivity
    · exact le_rfl
  refine ⟨∑ p, f p, ?_⟩
  intro i j hij
  have hd : 0 < w j - w i := sub_pos.mpr (hw hij)
  have hle : f (i, j) ≤ ∑ p, f p :=
    Finset.single_le_sum (fun p _ => hf p) (Finset.mem_univ _)
  have hfij : f (i, j) = (|v i| + |v j| + 1) / (w j - w i) := by
    simp [f, hij]
  rw [hfij] at hle
  have key : |v i| + |v j| + 1 ≤ (∑ p, f p) * (w j - w i) := by
    rw [div_le_iff₀ hd] at hle; exact hle
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have h2 := le_abs_self (v i)
  have h3 := neg_abs_le (v j)
  nlinarith

end Q3L
