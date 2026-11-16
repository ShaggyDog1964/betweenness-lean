/-
# Assembly of `K4.target` (no proof holes in this file)
-/
import K4.Statement
import K4.Defs
import K4.RacetrackLength
import K4.NodupOfErase
import K4.RacetrackMemSimplex
import K4.NotRepresentable
import K4.LogCertExists
import K4.RepresentableOfLogCert
import K4.SharpOfRacetrack

namespace K4

theorem target : target_stmt := by
  have hA : racetrack_stmt := by
    intro K hK J hJ
    have hdel : ∀ k < (racetrackList K J).length,
        Representable ((racetrackList K J).eraseIdx k) := by
      intro k hk
      rw [racetrack_length K J] at hk
      obtain ⟨u, s, v, w, h⟩ := logCert_exists J hJ k hk
      exact representable_of_logCert hK J k hk u s v w h
    have hlen : 3 ≤ (racetrackList K J).length := by
      rw [racetrack_length K J]
      omega
    exact And.intro (nodup_of_eraseIdx_representable (racetrackList K J) hlen hdel)
      (And.intro (racetrack_mem_simplex hK J)
        (And.intro (racetrack_not_representable hK J hJ) hdel))
  exact And.intro hA (sharp_of_racetrack hA)

end K4
