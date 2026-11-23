/-
# Assembly of `Q2CL.target` (no proof holes in this file)
-/
import Q2CL.Statement
import Q2CL.Defs
import Q2CL.WitnessArith
import Q2CL.TLength
import Q2CL.TSep
import Q2CL.TMemSimplex
import Q2CL.NotRepresentable
import Q2CL.Deletions
import Q2CL.Packing
import K4.NodupOfErase
import K4.EraseIdxSublist
import K4.RepresentableSublist

namespace Q2CL

open K4

theorem lower : lower_stmt := by
  intro δ hδ hδ1 n hn hS
  obtain ⟨hA, h32, hdiff, hsame, hsize⟩ := witness_arith δ hδ hδ1
  have hlen := T_length hA
  have hdel := deletions_representable hA
  have hnr := T_not_representable hA
  have hmem : ∀ x ∈ Tlist (mOf δ) (nsOf δ) δ, x ∈ Simplex 4 := by
    intro x hx
    unfold Tlist at hx
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
    exact T_mem_simplex hA i (List.mem_range.mp hi)
  have hlen3 : 3 ≤ (Tlist (mOf δ) (nsOf δ) δ).length := by
    have hm2 : (2 : ℝ) ≤ (mOf δ : ℝ) := by exact_mod_cast hA.1
    have hns : (1 : ℝ) ≤ (nsOf δ : ℝ) := by
      have : 1 ≤ nsOf δ := by unfold nsOf; omega
      exact_mod_cast this
    have h3 : ((3 : ℕ) : ℝ) < ((Tlist (mOf δ) (nsOf δ) δ).length : ℝ) := by
      have : (4 : ℝ) ≤ (mOf δ : ℝ) ^ 2 := by nlinarith
      push_cast
      nlinarith
    exact_mod_cast h3.le
  have hnd := nodup_of_eraseIdx_representable _ hlen3 hdel
  have hsep := T_sep hA h32 hδ le_rfl (le_trans le_rfl hδ1) hdiff hsame
  apply hnr
  apply hS _ hnd hmem hsep
  intro L' hsub hL'
  have hlt : L'.length < (Tlist (mOf δ) (nsOf δ) δ).length := by
    have h1 : ((L'.length : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hL'
    have h2 : ((L'.length : ℕ) : ℝ) < ((Tlist (mOf δ) (nsOf δ) δ).length : ℝ) := by
      linarith
    exact_mod_cast h2
  obtain ⟨k, hk, hs⟩ := exists_eraseIdx_of_sublist hsub hlt
  exact representable_sublist hs (hdel k hk)

theorem upper : upper_stmt := by
  intro δ hδ hδ1 L hnd hmem hsep hloc
  apply hloc L (List.Sublist.refl L)
  have h := packing δ hδ hδ1 L hnd hmem hsep
  have h2 : (L.length : ℝ) ≤ (⌈(3 / δ + 1) ^ 3⌉₊ : ℝ) := le_trans h (Nat.le_ceil _)
  exact_mod_cast h2

theorem target : target_stmt := ⟨lower, upper⟩

end Q2CL
