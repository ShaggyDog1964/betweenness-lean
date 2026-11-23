import Q1.ChainWeakOrder
import Q1.ChainPairwise
import Q1.ChainHQC
import Q1.ChainVQC
import Q1.ZzLength
import Q1.CritUMono
import Q1.CritUConv
import Q1.CritMem
import Q1.CritNotMem

namespace Q1

/-- One-deletion criticality: deleting any position leaves a ranking in R(HVQC).
Sketch: `k < n + 2` (`zigzagList_length`), so `k ≤ n + 1`. Take `R := chainRel (critU k)`:
a weak order by `chainRel_weakOrder (critU_mono k)`; HQC and VQC by `chainRel_hqc` and
`chainRel_vqc` with `critU_conv`; pairwise strict by `chainRel_pairwise (critU_mono k)`
with `crit_mem` and `crit_not_mem`. -/
theorem zz_critical (n k : ℕ) (hk : k < (zigzagList n).length) :
    InR HVQC ((zigzagList n).eraseIdx k) := by
  have hk' : k ≤ n + 1 := by
    rw [zigzagList_length] at hk; omega
  exact ⟨chainRel (critU k), chainRel_weakOrder (critU_mono k),
    ⟨chainRel_hqc (fun t => (critU_conv k t).1), chainRel_vqc (fun t => (critU_conv k t).2)⟩,
    chainRel_pairwise (critU_mono k) _ (crit_mem hk') (crit_not_mem hk')⟩

end Q1
