import Q2CL.Defs
import K4.RepresentableOfChain

namespace Q2CL

open K4

/-- "If" of Theorem 33 in the `IsChainFn` form (via `K4.representable_of_chain`). -/
theorem representable_of_chainFn (n : ℕ) (p : ℕ → Lot 4) (hp : ∀ i, i < n → p i ∈ Simplex 4)
    (W : ℕ → Lot 4) (h : IsChainFn n p W) : Representable ((List.range n).map p) := by
  by_cases hn : n < 2
  · refine K4.representable_of_chain (fun _ => (fun k : Fin 4 => ((k : ℕ) : ℝ))) p n hp
      ?_ ?_ ?_
    · intro _ a b hab
      have : (a : ℕ) < b := hab
      show ((a : ℕ) : ℝ) < ((b : ℕ) : ℝ)
      exact_mod_cast this
    · intro _; exact le_refl _
    · intro i hi; omega
  · have hn : 2 ≤ n := by omega
    refine K4.representable_of_chain (fun i => W (min i (n - 2))) p n hp ?_ ?_ ?_
    · intro i
      exact (h.1 (min i (n - 2)) (by omega)).1
    · intro i
      by_cases hi : i + 1 ≤ n - 2
      · have e1 : min i (n - 2) = i := by omega
        have e2 : min (i + 1) (n - 2) = i + 1 := by omega
        simp only [e1, e2]
        exact h.2 i (by omega)
      · have e1 : min i (n - 2) = n - 2 := by omega
        have e2 : min (i + 1) (n - 2) = n - 2 := by omega
        simp only [e1, e2]
        exact le_refl _
    · intro i hi
      have e1 : min i (n - 2) = i := by omega
      simp only [e1]
      exact (h.1 i hi).2
end Q2CL
