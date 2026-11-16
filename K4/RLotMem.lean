import K4.Defs

namespace K4

/-- A ratio edge lottery with `x ≥ 0` on two distinct existing prizes lies in the simplex.
Sketch: entries are `x/(x+1) ≥ 0`, `1/(x+1) > 0`, `0`; the sum is
`x/(x+1) + 1/(x+1) = 1` (split the sum over `Fin K` at the two indices
`⟨i, hi⟩`, `⟨j, hj⟩`, e.g. `Finset.sum_eq_add_of_mem` / `Finset.sum_ite_eq`). -/
theorem rLot_mem_simplex {K i j : ℕ} (hij : i ≠ j) (hi : i < K) (hj : j < K) {x : ℝ}
    (hx : 0 ≤ x) : rLot K i j x ∈ Simplex K := by
  have hx1 : 0 < x + 1 := by linarith
  show (∀ k, 0 ≤ rLot K i j x k) ∧ ∑ k, rLot K i j x k = 1
  refine ⟨fun k => ?_, ?_⟩
  · simp only [rLot]
    split_ifs
    · exact div_nonneg hx hx1.le
    · exact div_nonneg zero_le_one hx1.le
    · exact le_refl 0
  · have hfun : rLot K i j x = fun k : Fin K =>
        (if k = (⟨i, hi⟩ : Fin K) then x / (x + 1) else 0) +
        (if k = (⟨j, hj⟩ : Fin K) then 1 / (x + 1) else 0) := by
      funext k
      simp only [rLot]
      by_cases h1 : k.val = i
      · have h2 : k.val ≠ j := fun h => hij (h1.symm.trans h)
        have e1 : k = (⟨i, hi⟩ : Fin K) := Fin.ext h1
        have e2 : k ≠ (⟨j, hj⟩ : Fin K) := fun h => h2 (congrArg Fin.val h)
        rw [if_pos h1, if_pos e1, if_neg e2, add_zero]
      · have e1 : k ≠ (⟨i, hi⟩ : Fin K) := fun h => h1 (congrArg Fin.val h)
        rw [if_neg h1, if_neg e1, zero_add]
        by_cases h2 : k.val = j
        · have e2 : k = (⟨j, hj⟩ : Fin K) := Fin.ext h2
          rw [if_pos h2, if_pos e2]
        · have e2 : k ≠ (⟨j, hj⟩ : Fin K) := fun h => h2 (congrArg Fin.val h)
          rw [if_neg h2, if_neg e2]
    rw [hfun]
    simp only [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq,
      Finset.mem_univ, if_true]
    rw [← add_div, div_self hx1.ne']

end K4
