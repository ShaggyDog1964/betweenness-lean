import Q2CL.Defs
import Q2CL.DelR0
import Q2CL.DelRend
import Q2CL.DelXa
import Q2CL.DelYa
import Q2CL.DelYbMid
import Q2CL.DelXbMid
import Q2CL.DelLast
import Q2CL.RepresentableOfChainFn
import Q2CL.TMemSimplex
import Q2CL.JSpec
import K4.EraseIdxMapRange

namespace Q2CL

open K4

/-- Proposition 71 (deletions): every one-point deletion of `T(m, ns, ds)` is representable. -/
theorem deletions_representable {m ns : ℕ} {ds : ℝ} (hA : Adm m ns ds) :
    ∀ k, k < (Tlist m ns ds).length → Representable ((Tlist m ns ds).eraseIdx k) := by
  intro k hk
  have hlen : (Tlist m ns ds).length = 4 * Jn m ns + 2 := by unfold Tlist; simp
  rw [hlen] at hk
  unfold Tlist
  rw [K4.eraseIdx_map_range _ _ _ hk]
  have hn : 4 * Jn m ns + 2 - 1 = 4 * Jn m ns + 1 := by omega
  rw [hn]
  have hp : ∀ i, i < 4 * Jn m ns + 1 →
      (fun i => Tpt m ns ds (skipIdx k i)) i ∈ Simplex 4 := by
    intro i hi
    apply T_mem_simplex hA
    unfold skipIdx; split_ifs <;> omega
  suffices h : ∃ W, IsChainFn (4 * Jn m ns + 1) (fun i => Tpt m ns ds (skipIdx k i)) W by
    obtain ⟨W, hW⟩ := h
    exact representable_of_chainFn _ _ hp W hW
  rcases Nat.eq_zero_or_pos k with h0 | hpos
  · subst h0; exact del_R0 hA
  by_cases hend : k = 4 * Jn m ns + 1
  · subst hend; exact del_Rend hA
  obtain ⟨j, hj, hcase⟩ : ∃ j, j < Jn m ns ∧
      (k = 4 * j + 1 ∨ k = 4 * j + 2 ∨ k = 4 * j + 3 ∨ k = 4 * j + 4) :=
    ⟨(k - 1) / 4, by omega, by omega⟩
  rcases hcase with rfl | rfl | rfl | rfl
  · exact del_xa hA j hj
  · exact del_ya hA j hj
  · by_cases hj1 : j + 1 < Jn m ns
    · exact del_yb_mid hA j hj1
    · exact del_last hA _ (Or.inl (by omega))
  · by_cases hj1 : j + 1 < Jn m ns
    · exact del_xb_mid hA j hj1
    · exact del_last hA _ (Or.inr (by omega))

end Q2CL
