/-
# Assembly of `Odds.target` (no proof holes in this file)

Base-free parts are reused from the proved `K4` library: the integer log certificates
(`K4.logCert_exists`) and `K4.nodup_of_eraseIdx_representable`.
-/
import Odds.Statement
import Odds.Defs
import Odds.RacetrackBLength
import Odds.RacetrackBMemSimplex
import Odds.NotRepresentableB
import Odds.RepresentableOfLogCertB
import Odds.MaxOddsB
import Odds.BoundedOddsOfAB
import K4.LogCertExists
import K4.NodupOfErase

namespace Odds

open K4

theorem target : target_stmt := by
  have hA : racetrackB_stmt := by
    intro b hb K hK J hJ
    have hdel : ∀ k < (racetrackListB b K J).length,
        Representable ((racetrackListB b K J).eraseIdx k) := by
      intro k hk
      rw [racetrackB_length b K J] at hk
      obtain ⟨u, s, v, w, h⟩ := K4.logCert_exists J hJ k hk
      exact representable_of_logCertB hK hb J k hk u s v w h
    have hlen : 3 ≤ (racetrackListB b K J).length := by
      rw [racetrackB_length b K J]
      omega
    exact And.intro (K4.nodup_of_eraseIdx_representable (racetrackListB b K J) hlen hdel)
      (And.intro (racetrackB_mem_simplex hK (by linarith) J)
        (And.intro (racetrackB_not_representable hK hb J hJ) hdel))
  exact And.intro hA (And.intro racetrackB_maxOdds (boundedOdds_of_AB hA racetrackB_maxOdds))

end Odds
