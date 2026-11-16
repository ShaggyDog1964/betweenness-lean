import K4.Defs
import K4.RacetrackEqMap
import K4.PairwiseMapRange
import K4.RacePtVals

namespace K4

/-- The strict comparisons of `X_J` used by the impossibility argument.
Sketch: from `h` get `R`, `hR`, `hpw : (racetrackList K J).Pairwise (SPref R)`; rewrite with
`racetrack_eq_map` and `pairwise_map_range_iff` to get
`∀ i j, i < j → j < 4J+2 → SPref R (racePt K J i) (racePt K J j)`. Instantiate at the
positions `0 < 1` (note `4*0+1 = 1`), `4b+1 < 4b+2`, `4b+3 < 4b+4`, `4b+1 < 4b+4`,
`4b+4 < 4J+1`, `4b+1 < 4J+1`, `4b+4 < 4(b+1)+1` (all `< 4J+2` by `omega` using `b < J` or
`b + 1 < J`), rewriting each `racePt` with `racePt_vals`. -/
theorem racetrack_spref_facts {K : ℕ} (J : ℕ) (hJ : 1 ≤ J)
    (h : Representable (racetrackList K J)) :
    ∃ R : Rel K, IsBetweennessPref R ∧
      SPref R (lotR K (parV0 J)) (lotP K (expA J 0)) ∧
      (∀ b, b < J →
        SPref R (lotP K (expA J b)) (lotQ K (expD J b)) ∧
        SPref R (lotQ K (expD J b + parG J)) (lotP K (expA J b + 4)) ∧
        SPref R (lotP K (expA J b)) (lotP K (expA J b + 4)) ∧
        SPref R (lotP K (expA J b + 4)) (lotR K (parV0 J + J * parBeta J)) ∧
        SPref R (lotP K (expA J b)) (lotR K (parV0 J + J * parBeta J))) ∧
      (∀ b, b + 1 < J → SPref R (lotP K (expA J b + 4)) (lotP K (expA J (b + 1)))) := by
  obtain ⟨R, hR, hpw⟩ := h
  rw [racetrack_eq_map, pairwise_map_range_iff] at hpw
  obtain ⟨v0, vL, vb⟩ := racePt_vals K J
  refine ⟨R, hR, ?_, ?_, ?_⟩
  · have := hpw 0 1 (by omega) (by omega)
    obtain ⟨a1, -, -, -⟩ := vb 0 (by omega)
    rw [v0, show (1 : ℕ) = 4 * 0 + 1 by rfl, a1] at this
    exact this
  · intro b hb
    obtain ⟨a1, d1, d2, a2⟩ := vb b hb
    have h1 := hpw (4 * b + 1) (4 * b + 2) (by omega) (by omega)
    have h2 := hpw (4 * b + 3) (4 * b + 4) (by omega) (by omega)
    have h3 := hpw (4 * b + 1) (4 * b + 4) (by omega) (by omega)
    have h4 := hpw (4 * b + 4) (4 * J + 1) (by omega) (by omega)
    have h5 := hpw (4 * b + 1) (4 * J + 1) (by omega) (by omega)
    rw [a1, d1] at h1
    rw [d2, a2] at h2
    rw [a1, a2] at h3
    rw [a2, vL] at h4
    rw [a1, vL] at h5
    exact ⟨h1, h2, h3, h4, h5⟩
  · intro b hb
    obtain ⟨-, -, -, a2⟩ := vb b (by omega)
    obtain ⟨a1, -, -, -⟩ := vb (b + 1) hb
    have h := hpw (4 * b + 4) (4 * (b + 1) + 1) (by omega) (by omega)
    rw [a2, a1] at h
    exact h

end K4
