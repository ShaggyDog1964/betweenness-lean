import Odds.Defs

namespace Odds

open K4

/-- Every exponent of the racetrack is at most the last one, `v0 + J β`.
Sketch. Unfold `rtExp`, `expA`, `expD`, `parV0`, `parD`, `parG`, `parG_small`, `parH`,
`parBeta`; `split_ifs`. Cases `i = 0` (`v0 ≤ v0 + Jβ`) and `i = 4J+1` (equality) are
`omega`. Otherwise `1 ≤ i ≤ 4J`, so `q := (i-1)/4 ≤ J - 1`, i.e. `q + 1 ≤ J`. Then
* `P` entries: `q h ≤ q h + 4 ≤ (J-1) h + 4 < J h + 1 = D ≤ v0` with `h = 4J+8 ≥ 4`;
* `Q` entries: `D + q (G+2) ≤ D + q (G+2) + G < D + J (G+2) ≤ v0` since
  `q (G+2) + G < (q+1)(G+2) ≤ J (G+2)`.
These are nonlinear for `omega`: give `Nat.mul_le_mul_right (4*J+8) (hq : q + 1 ≤ J)` and
`Nat.mul_le_mul_right (4*J+6) hq` (or use `nlinarith`) and finish with `omega`/`nlinarith`. -/
theorem rtExp_le (J i : ℕ) (hi : i < 4 * J + 2) :
    rtExp J i ≤ parV0 J + J * parBeta J := by
  unfold rtExp
  simp only [parV0, parD, parG, parH, parBeta, expA, expD, parG_small]
  split_ifs with h0 h1 h2 h3 h4
  · omega
  · omega
  all_goals
    have hq : (i - 1) / 4 + 1 ≤ J := by omega
    have e1 := Nat.mul_le_mul_right (4 * J + 8) hq
    have e2 := Nat.mul_le_mul_right (4 * J + 4 + 2) hq
    rw [Nat.add_mul, one_mul] at e1 e2
    omega

end Odds
