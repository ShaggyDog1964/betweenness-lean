import K4.Defs
import K4.LogCertDelFirst
import K4.LogCertDelLast
import K4.LogCertDelA
import K4.LogCertDelD
import K4.LogCertDelDp
import K4.LogCertDelAp

namespace K4

/-- Every one-point deletion of `X_J` has a log certificate.
Sketch: case split. `k = 0`: `logCert_delFirst`. `k = 4J + 1`: `logCert_delLast`.
Otherwise `1 ≤ k ≤ 4J`; put `b = (k - 1) / 4 < J`, `r = (k - 1) % 4`; then
`k = 4b + 1 + r` (`omega`) and apply `logCert_delA` / `logCert_delD` / `logCert_delDp` /
`logCert_delAp` for `r = 0, 1, 2, 3` (rewrite `k` with `obtain rfl` or `▸`). -/
theorem logCert_exists (J : ℕ) (hJ : 1 ≤ J) (k : ℕ) (hk : k < 4 * J + 2) :
    ∃ u s v w : ℕ → ℤ, LogCert J k u s v w := by
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · exact logCert_delFirst J hJ
  by_cases hl : k = 4 * J + 1
  · subst hl; exact logCert_delLast J hJ
  have hb : (k - 1) / 4 < J := by omega
  have hr : (k - 1) % 4 < 4 := Nat.mod_lt _ (by norm_num)
  have hk' : k = 4 * ((k - 1) / 4) + 1 + (k - 1) % 4 := by omega
  rcases (by omega : (k - 1) % 4 = 0 ∨ (k - 1) % 4 = 1 ∨ (k - 1) % 4 = 2 ∨ (k - 1) % 4 = 3)
    with h | h | h | h
  · rw [hk', h]; exact logCert_delA J _ hb
  · rw [hk', h]; exact logCert_delD J _ hb
  · rw [hk', h]; exact logCert_delDp J _ hb
  · rw [hk', h]; exact logCert_delAp J _ hb

end K4
