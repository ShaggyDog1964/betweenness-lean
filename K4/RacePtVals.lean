import K4.Defs

namespace K4

/-- Values of `racePt` at the named positions: `R[v0]` at `0`, `R[v0 + Jβ]` at `4J+1`, and for
block `b < J`: `A_b` at `4b+1`, `D_b` at `4b+2`, `D'_b` at `4b+3`, `A'_b` at `4b+4`.
Sketch: unfold `racePt`, `rtKind`, `rtExp`, `ekLot`, `parG_small`; decide the `if`s with
`omega` (e.g. `4b+4 ≠ 4J+1` by parity, `(4b+3) % 4 = 3`, `(4b+3)/4 = b`), `simp`. -/
theorem racePt_vals (K J : ℕ) :
    racePt K J 0 = lotR K (parV0 J) ∧
    racePt K J (4 * J + 1) = lotR K (parV0 J + J * parBeta J) ∧
    ∀ b, b < J →
      racePt K J (4 * b + 1) = lotP K (expA J b) ∧
      racePt K J (4 * b + 2) = lotQ K (expD J b) ∧
      racePt K J (4 * b + 3) = lotQ K (expD J b + parG J) ∧
      racePt K J (4 * b + 4) = lotP K (expA J b + 4) := by
  refine ⟨?_, ?_, ?_⟩
  · simp [racePt, rtKind, rtExp, ekLot]
  · simp [racePt, rtKind, rtExp, ekLot]
  · intro b hb
    have e1a : 4 * b + 1 ≠ 0 := by omega
    have e1b : 4 * b + 1 ≠ 4 * J + 1 := by omega
    have e1c : (4 * b + 1 - 1) % 4 = 0 := by omega
    have e1d : (4 * b + 1 - 1) / 4 = b := by omega
    have e2a : 4 * b + 2 ≠ 0 := by omega
    have e2b : 4 * b + 2 ≠ 4 * J + 1 := by omega
    have e2c : (4 * b + 2 - 1) % 4 = 1 := by omega
    have e2d : (4 * b + 2 - 1) / 4 = b := by omega
    have e3a : 4 * b + 3 ≠ 0 := by omega
    have e3b : 4 * b + 3 ≠ 4 * J + 1 := by omega
    have e3c : (4 * b + 3 - 1) % 4 = 2 := by omega
    have e3d : (4 * b + 3 - 1) / 4 = b := by omega
    have e4a : 4 * b + 4 ≠ 0 := by omega
    have e4b : 4 * b + 4 ≠ 4 * J + 1 := by omega
    have e4c : (4 * b + 4 - 1) % 4 = 3 := by omega
    have e4d : (4 * b + 4 - 1) / 4 = b := by omega
    refine ⟨?_, ?_, ?_, ?_⟩
    · unfold racePt rtKind rtExp
      rw [if_neg e1a, if_neg e1b, if_pos e1c, if_neg e1a, if_neg e1b, if_pos e1c, e1d]
      rfl
    · unfold racePt rtKind rtExp
      rw [if_neg e2a, if_neg e2b, if_neg (by omega), if_neg (by omega),
        if_neg e2a, if_neg e2b, if_neg (by omega), if_pos e2c, e2d]
      rfl
    · unfold racePt rtKind rtExp
      rw [if_neg e3a, if_neg e3b, if_neg (by omega), if_neg (by omega),
        if_neg e3a, if_neg e3b, if_neg (by omega), if_neg (by omega), if_pos e3c, e3d]
      rfl
    · unfold racePt rtKind rtExp
      rw [if_neg e4a, if_neg e4b, if_neg (by omega), if_pos e4c,
        if_neg e4a, if_neg e4b, if_neg (by omega), if_neg (by omega), if_neg (by omega), e4d]
      rfl

end K4
