import Odds.Defs
import Odds.RacetrackBEqMap
import Odds.RacePtBVals
import K4.PairwiseMapRange

namespace Odds

open K4

/-- The strict comparisons of `X_J^b` used by the impossibility argument
(base-`b` copy of `K4.racetrack_spref_facts`).
Sketch: from `h` get `R`, `hR`, `hpw`; `rw [racetrackB_eq_map, K4.pairwise_map_range_iff]
at hpw` gives `∀ p q, p < q → q < 4J+2 → SPref R (racePtB b K J p) (racePtB b K J q)`.
Instantiate at `0 < 1` (`1 = 4*0+1`), `4i+1 < 4i+2`, `4i+3 < 4i+4`, `4i+1 < 4i+4`,
`4i+4 < 4J+1`, `4i+1 < 4J+1`, `4i+4 < 4(i+1)+1` (bounds by `omega`), rewriting with
`racePtB_vals`. Identical to the K4 proof. -/
theorem racetrackB_spref_facts {K : ℕ} (b : ℝ) (J : ℕ) (hJ : 1 ≤ J)
    (h : Representable (racetrackListB b K J)) :
    ∃ R : Rel K, IsBetweennessPref R ∧
      SPref R (lotRB b K (parV0 J)) (lotPB b K (expA J 0)) ∧
      (∀ i, i < J →
        SPref R (lotPB b K (expA J i)) (lotQB b K (expD J i)) ∧
        SPref R (lotQB b K (expD J i + parG J)) (lotPB b K (expA J i + 4)) ∧
        SPref R (lotPB b K (expA J i)) (lotPB b K (expA J i + 4)) ∧
        SPref R (lotPB b K (expA J i + 4)) (lotRB b K (parV0 J + J * parBeta J)) ∧
        SPref R (lotPB b K (expA J i)) (lotRB b K (parV0 J + J * parBeta J))) ∧
      (∀ i, i + 1 < J →
        SPref R (lotPB b K (expA J i + 4)) (lotPB b K (expA J (i + 1)))) := by
  obtain ⟨R, hR, hpw⟩ := h
  rw [racetrackB_eq_map, pairwise_map_range_iff] at hpw
  obtain ⟨v0, vL, vb⟩ := racePtB_vals b K J
  refine ⟨R, hR, ?_, ?_, ?_⟩
  · have := hpw 0 1 (by omega) (by omega)
    obtain ⟨a1, -, -, -⟩ := vb 0 (by omega)
    rw [v0, show (1 : ℕ) = 4 * 0 + 1 by rfl, a1] at this
    exact this
  · intro i hi
    obtain ⟨a1, d1, d2, a2⟩ := vb i hi
    have h1 := hpw (4 * i + 1) (4 * i + 2) (by omega) (by omega)
    have h2 := hpw (4 * i + 3) (4 * i + 4) (by omega) (by omega)
    have h3 := hpw (4 * i + 1) (4 * i + 4) (by omega) (by omega)
    have h4 := hpw (4 * i + 4) (4 * J + 1) (by omega) (by omega)
    have h5 := hpw (4 * i + 1) (4 * J + 1) (by omega) (by omega)
    rw [a1, d1] at h1
    rw [d2, a2] at h2
    rw [a1, a2] at h3
    rw [a2, vL] at h4
    rw [a1, vL] at h5
    exact ⟨h1, h2, h3, h4, h5⟩
  · intro i hi
    obtain ⟨-, -, -, a2⟩ := vb i (by omega)
    obtain ⟨a1, -, -, -⟩ := vb (i + 1) hi
    have h := hpw (4 * i + 4) (4 * (i + 1) + 1) (by omega) (by omega)
    rw [a2, a1] at h
    exact h

end Odds
