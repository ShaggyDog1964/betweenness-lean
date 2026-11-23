import Odds.Defs

namespace Odds

open K4

/-- Values of `racePtB` at the named positions (base-`b` copy of `K4.racePt_vals`).
Sketch: copy the proof of `K4.racePt_vals` (file `K4/RacePtVals.lean`) with `racePt →
racePtB b`, `ekLot → ekLotB b`, `lotP/Q/R → lotPB b/lotQB b/lotRB b`: unfold `racePtB`,
`rtKind`, `rtExp`, decide the `if`s with `omega`, close by `rfl` (note `parG_small J = 4`
definitionally). -/
theorem racePtB_vals (b : ℝ) (K J : ℕ) :
    racePtB b K J 0 = lotRB b K (parV0 J) ∧
    racePtB b K J (4 * J + 1) = lotRB b K (parV0 J + J * parBeta J) ∧
    ∀ i, i < J →
      racePtB b K J (4 * i + 1) = lotPB b K (expA J i) ∧
      racePtB b K J (4 * i + 2) = lotQB b K (expD J i) ∧
      racePtB b K J (4 * i + 3) = lotQB b K (expD J i + parG J) ∧
      racePtB b K J (4 * i + 4) = lotPB b K (expA J i + 4) := by
  refine ⟨?_, ?_, ?_⟩
  · simp [racePtB, rtKind, rtExp, ekLotB]
  · simp [racePtB, rtKind, rtExp, ekLotB]
  · intro i hi
    have e1a : 4 * i + 1 ≠ 0 := by omega
    have e1b : 4 * i + 1 ≠ 4 * J + 1 := by omega
    have e1c : (4 * i + 1 - 1) % 4 = 0 := by omega
    have e1d : (4 * i + 1 - 1) / 4 = i := by omega
    have e2a : 4 * i + 2 ≠ 0 := by omega
    have e2b : 4 * i + 2 ≠ 4 * J + 1 := by omega
    have e2c : (4 * i + 2 - 1) % 4 = 1 := by omega
    have e2d : (4 * i + 2 - 1) / 4 = i := by omega
    have e3a : 4 * i + 3 ≠ 0 := by omega
    have e3b : 4 * i + 3 ≠ 4 * J + 1 := by omega
    have e3c : (4 * i + 3 - 1) % 4 = 2 := by omega
    have e3d : (4 * i + 3 - 1) / 4 = i := by omega
    have e4a : 4 * i + 4 ≠ 0 := by omega
    have e4b : 4 * i + 4 ≠ 4 * J + 1 := by omega
    have e4c : (4 * i + 4 - 1) % 4 = 3 := by omega
    have e4d : (4 * i + 4 - 1) / 4 = i := by omega
    refine ⟨?_, ?_, ?_, ?_⟩
    · unfold racePtB rtKind rtExp
      rw [if_neg e1a, if_neg e1b, if_pos e1c, if_neg e1a, if_neg e1b, if_pos e1c, e1d]
      rfl
    · unfold racePtB rtKind rtExp
      rw [if_neg e2a, if_neg e2b, if_neg (by omega), if_neg (by omega),
        if_neg e2a, if_neg e2b, if_neg (by omega), if_pos e2c, e2d]
      rfl
    · unfold racePtB rtKind rtExp
      rw [if_neg e3a, if_neg e3b, if_neg (by omega), if_neg (by omega),
        if_neg e3a, if_neg e3b, if_neg (by omega), if_neg (by omega), if_pos e3c, e3d]
      rfl
    · unfold racePtB rtKind rtExp
      rw [if_neg e4a, if_neg e4b, if_neg (by omega), if_pos e4c,
        if_neg e4a, if_neg e4b, if_neg (by omega), if_neg (by omega), if_neg (by omega), e4d]
      rfl

end Odds
