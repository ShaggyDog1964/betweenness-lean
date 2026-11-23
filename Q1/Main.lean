/-
# Q1 main theorem: assembly only (no proof holes here)

(a) `hqc_local_three` and `not_isLocal_hqc_two` (proved in `Q1.Sanity`); the V-QC half by
the coordinate swap `isLocal_vqc_iff` and `not_isLocal_vqc_two` (`Q1.Sanity`).
(b) For every `n`, the zigzag ranking `zigzagList (n+1)` (length `n + 3`) is nodup, not in
R(HVQC), and every one-deletion of it is in R(HVQC); every sub-ranking with at most `n`
entries is a sub-ranking of a one-deletion (`K4.exists_eraseIdx_of_sublist`).
-/
import Q1.HqcLocal3
import Q1.IsLocalSwap
import Q1.Sanity
import Q1.InRSublist
import Q1.ZzLength
import Q1.ZzNotInR
import Q1.ZzCritical
import Q1.ZzNodup
import K4.EraseIdxSublist

namespace Q1

theorem hvqc_main : hvqc_stmt := by
  intro n hloc
  have hlen := zigzagList_length (n + 1)
  apply zz_not_inR (n + 1)
  apply hloc _ (zigzagList_nodup (by omega))
  intro L' hsub hL'
  obtain ⟨k, hk, hsub'⟩ := K4.exists_eraseIdx_of_sublist hsub (by omega)
  exact inR_sublist (zz_critical (n + 1) k hk) hsub'

theorem target : target_stmt :=
  ⟨⟨hqc_local_three, not_isLocal_hqc_two⟩,
    ⟨(isLocal_vqc_iff 3).2 hqc_local_three, not_isLocal_vqc_two⟩,
    hvqc_main⟩

end Q1
