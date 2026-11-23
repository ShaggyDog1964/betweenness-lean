import Q2CL.Defs
import Q2CL.SepBasic
import Q2CL.SepDiffSlot
import Q2CL.SepSameSlot

namespace Q2CL

open K4

/-- Separation of `T(m, ns, ds)` (in place of Lemma 82, with explicit thresholds). -/
theorem T_sep {m ns : ℕ} {ds δ : ℝ} (hA : Adm m ns ds) (h32 : 32 ≤ m ^ 2 * ns)
    (hδ : 0 < δ) (hds : δ ≤ ds) (h11 : δ ≤ 11 / 1000)
    (hdiff : δ ≤ (7 / 25) / ((2 * (m : ℝ) + 1) * (401 / 80)))
    (hsame : δ ≤ 9 / 500 * ((m : ℝ) + 1) / (m : ℝ) ^ 2) :
    SepGe δ (Tlist m ns ds) := by
  obtain ⟨hB1, hB2⟩ := sep_basic hA
  have hD := sep_diff_slot hA h32
  have hS := sep_same_slot hA h32
  intro x hx y hy hxy
  unfold Tlist at hx hy
  rw [List.mem_map] at hx hy
  obtain ⟨i, hi, rfl⟩ := hx
  obtain ⟨i', hi', rfl⟩ := hy
  rw [List.mem_range] at hi hi'
  have hne : i ≠ i' := by rintro rfl; exact hxy rfl
  by_cases hR : i = 0 ∨ i = 4 * Jn m ns + 1
  · obtain ⟨k, hk⟩ := hB2 i i' hi hi' hne hR
    exact ⟨k, le_trans h11 hk⟩
  by_cases hR' : i' = 0 ∨ i' = 4 * Jn m ns + 1
  · obtain ⟨k, hk⟩ := hB2 i' i hi' hi (Ne.symm hne) hR'
    exact ⟨k, le_trans h11 (by rw [abs_sub_comm]; exact hk)⟩
  push_neg at hR hR'
  have e1 : Tpt m ns ds i = gpt m ns ds ((i - 1) / 4) ((i - 1) % 4) := by
    unfold Tpt; rw [if_neg hR.1, if_neg hR.2]
  have e2 : Tpt m ns ds i' = gpt m ns ds ((i' - 1) / 4) ((i' - 1) % 4) := by
    unfold Tpt; rw [if_neg hR'.1, if_neg hR'.2]
  rw [e1, e2]
  have hj : (i - 1) / 4 < Jn m ns := by omega
  have hj' : (i' - 1) / 4 < Jn m ns := by omega
  have hτ : (i - 1) % 4 < 4 := Nat.mod_lt _ (by norm_num)
  have hτ' : (i' - 1) % 4 < 4 := Nat.mod_lt _ (by norm_num)
  have hjt : (i - 1) / 4 ≠ (i' - 1) / 4 ∨ (i - 1) % 4 ≠ (i' - 1) % 4 := by
    by_contra hc
    push_neg at hc
    have a := Nat.div_add_mod (i - 1) 4
    have b := Nat.div_add_mod (i' - 1) 4
    omega
  by_cases hsig : sig ns ds ((i - 1) / 4) = sig ns ds ((i' - 1) / 4)
  · by_cases ht : ptT m ns ((i - 1) / 4) ((i - 1) % 4) = ptT m ns ((i' - 1) / 4) ((i' - 1) % 4)
    · obtain ⟨k, hk⟩ := hS _ _ _ _ hj hj' hτ hτ' hjt hsig ht
      exact ⟨k, le_trans hsame hk⟩
    · obtain ⟨k, hk⟩ := hD _ _ _ _ hj hj' hτ hτ' hsig ht
      exact ⟨k, le_trans hdiff hk⟩
  · exact ⟨3, le_trans hds (hB1 _ _ _ _ hj hj' hsig)⟩

end Q2CL
