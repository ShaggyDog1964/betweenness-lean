/-
# Bounded odds: statement of the base-`b` racetrack theorem

The racetrack is critical in every base `b > 1`, so bounded odds do not bound tests.

This file contains ONLY definitions and headline `Prop`s. There are no theorems, no proof
holes, and no assumed axioms. It imports `K4.Statement` (audited) and reuses, verbatim
and without restating them, its definitions of:
  * `K4.Lot`, `K4.Simplex` (lotteries and the simplex Δ^{K-1}),
  * `K4.IsBetweennessPref` (the betweenness axioms, through `K4.Representable`),
  * `K4.Representable`, `K4.LocallyRepresentable` (representability and `n`-locality),
  * the integer parameters `K4.parG_small, parG, parH, parBeta, parD, parV0, expA, expD`.
The only new ingredients are the real base `b`, the base-`b` edge lotteries, the base-`b`
racetrack list (same shape and same integer exponents as `K4.racetrackList`), and a notion of
"odds at most `M`" for an arbitrary lottery.

Plain-language summary of `target_stmt` (end of file):
  (A) For every real `b > 1`, every `K ≥ 4` and every `J ≥ 1`, the base-`b` racetrack
      `racetrackListB b K J` (4J+2 lotteries) has no repeated entries, lies in the simplex, is
      NOT the strict ranking of any betweenness preference, and becomes such a ranking after
      deleting any single entry.
  (B) For the same `b, K, J`, the smallest `M` such that every entry of the list has odds at
      most `M` is exactly `b ^ (v0 + J * beta)`.
  (C) For every `K ≥ 4`, every real `M > 1` and every `n`, some finite strict order of
      distinct lotteries in Δ^{K-1}, all with odds at most `M`, is `n`-locally representable
      but not representable.
(C) follows from (A) and (B) by an easy argument (take `4J+2 > n` and
`b = M ^ (1/(v0 + J*beta))`), but it is stated on its own so that Proposition 24 of the working
paper appears literally. (A) and (B) are the steps of its proof in Appendix A.16 of the paper.

Conventions (as in `K4.Statement`). Prizes are `Fin K`, numbered `0 < 1 < … < K-1` from worst
to best. A lottery is a function `Fin K → ℝ`.
-/
import Mathlib
import K4.Statement

namespace Odds

open K4

/-! ## 1. Odds of a lottery -/

/-- `OddsLe M p`: every odds ratio inside the support of `p` is at most `M`. Precisely, for
any two prizes `i, j` with `p j > 0`, we have `p i ≤ M * p j`, i.e. `p i / p j ≤ M`.
(If `p i = 0` the condition is automatic for `M ≥ 0`.) For the edge lottery
`edgeLotB b K i j c` below with `b > 1`, the two nonzero masses are `b^c/(b^c+1)` and
`1/(b^c+1)`, so its ratios are `b^c ≥ 1` and `b^(-c)`, and `OddsLe M` holds iff
`b^c ≤ M`. This is the paper's "odds" of `E_ij(x)`, namely `x`, when `x ≥ 1`. -/
def OddsLe {K : ℕ} (M : ℝ) (p : Lot K) : Prop :=
  ∀ i j : Fin K, 0 < p j → p i ≤ M * p j

/-! ## 2. The base-`b` racetrack family

Same as `K4` §4, with `2` replaced by the real number `b`. For `K > 4` the extra prizes
`4, …, K-1` get probability 0. -/

/-- `edgeLotB b K i j c`: probability `b^c/(b^c+1)` on prize `i`, `1/(b^c+1)` on prize `j`,
zero elsewhere. So the ratio `prob(i) / prob(j)` is `b^c` (the exponent `c` is a natural
number; `b ^ c` is the ordinary real power). With `b = 2` this is literally `K4.edgeLot`
(see `base_two_agrees_stmt` below). Used only with `i ≠ j`, both `< 4`. -/
noncomputable def edgeLotB (b : ℝ) (K i j c : ℕ) : Lot K := fun k =>
  if k.val = i then b ^ c / (b ^ c + 1)
  else if k.val = j then 1 / (b ^ c + 1)
  else 0

/-- `P[c] = (b^c, 0, 1, 0)/(b^c+1)`: weight on prizes 0 and 2. -/
noncomputable def lotPB (b : ℝ) (K c : ℕ) : Lot K := edgeLotB b K 0 2 c

/-- `Q[c] = (0, b^c, 1, 0)/(b^c+1)`: weight on prizes 1 and 2. -/
noncomputable def lotQB (b : ℝ) (K c : ℕ) : Lot K := edgeLotB b K 1 2 c

/-- `R[c] = (0, b^c, 0, 1)/(b^c+1)`: weight on prizes 1 and 3. -/
noncomputable def lotRB (b : ℝ) (K c : ℕ) : Lot K := edgeLotB b K 1 3 c

/-- Block `j = i + 1` (0-based `i`), best to worst, with the K4 integer exponents:
`A_j = P[a_j]`, `D_j = Q[d_j]`, `D'_j = Q[d_j + G]`, `A'_j = P[a_j + g]`.
Identical to `K4.block` except that the lotteries use base `b`. -/
noncomputable def blockB (b : ℝ) (K J i : ℕ) : List (Lot K) :=
  [lotPB b K (expA J i), lotQB b K (expD J i), lotQB b K (expD J i + parG J),
   lotPB b K (expA J i + parG_small J)]

/-- Blocks `1, …, m` (0-based indices `0, …, m-1`) concatenated in order
(same recursion as `K4.blocksUpTo`). -/
noncomputable def blocksUpToB (b : ℝ) (K J : ℕ) : ℕ → List (Lot K)
  | 0 => []
  | m + 1 => blocksUpToB b K J m ++ blockB b K J m

/-- The base-`b` order `X_J^b`, best to worst: `R[v0]`, then blocks `1..J`, then
`R[v0 + J*beta]`. Length `4J + 2`. Same shape and exponents as `K4.racetrackList`. -/
noncomputable def racetrackListB (b : ℝ) (K J : ℕ) : List (Lot K) :=
  [lotRB b K (parV0 J)] ++ blocksUpToB b K J J ++ [lotRB b K (parV0 J + J * parBeta J)]

/-- `X_J^b` is a critical obstruction in Δ^{K-1}: no repeated entries, every entry is a
lottery, the whole order is NOT representable, and deleting any single entry (position `k`)
leaves a representable order. (Same four conjuncts as `K4.RacetrackCritical`.) -/
def RacetrackCriticalB (b : ℝ) (K J : ℕ) : Prop :=
  (racetrackListB b K J).Nodup ∧
  (∀ x ∈ racetrackListB b K J, x ∈ Simplex K) ∧
  ¬ Representable (racetrackListB b K J) ∧
  ∀ k < (racetrackListB b K J).length, Representable ((racetrackListB b K J).eraseIdx k)

/-! ## 3. Headline statements -/

/-- (A) For every real `b > 1`, the base-`b` racetrack is critical for every `K ≥ 4` and
`J ≥ 1`. -/
def racetrackB_stmt : Prop :=
  ∀ b : ℝ, 1 < b → ∀ K : ℕ, 4 ≤ K → ∀ J : ℕ, 1 ≤ J → RacetrackCriticalB b K J

/-- (B) For every real `b > 1`, `K ≥ 4`, `J ≥ 1`: the largest odds in `X_J^b` are
`b ^ (v0 + J*beta)`. Stated as: `b ^ (v0 + J*beta)` is the LEAST `M` such that every entry of
the list has odds at most `M`. -/
def maxOddsB_stmt : Prop :=
  ∀ b : ℝ, 1 < b → ∀ K : ℕ, 4 ≤ K → ∀ J : ℕ, 1 ≤ J →
    IsLeast {M : ℝ | ∀ x ∈ racetrackListB b K J, OddsLe M x} (b ^ (parV0 J + J * parBeta J))

/-- (C) Bounded odds do not bound tests: for every `K ≥ 4`, every real `M > 1` and every `n`,
there is a list `L` (a strict order, best first) of distinct lotteries in Δ^{K-1}, each with
odds at most `M`, that is `n`-locally representable but not representable. This is
`¬ K4.LocalComplete K n` with the extra constraint that all lotteries have odds `≤ M`. -/
def boundedOdds_impossibility_stmt : Prop :=
  ∀ K : ℕ, 4 ≤ K → ∀ M : ℝ, 1 < M → ∀ n : ℕ,
    ∃ L : List (Lot K), L.Nodup ∧ (∀ x ∈ L, x ∈ Simplex K) ∧ (∀ x ∈ L, OddsLe M x) ∧
      LocallyRepresentable n L ∧ ¬ Representable L

/-- The whole claim: (A), (B) and (C). -/
def target_stmt : Prop := racetrackB_stmt ∧ maxOddsB_stmt ∧ boundedOdds_impossibility_stmt

/-! ## 4. Audit control (statement only, not part of the target)

With `b = 2` the base-`b` list is literally the K4 racetrack, so (A) specializes to
`K4.racetrack_stmt`. This is expected to hold by unfolding (`(2:ℝ) ^ c` in both). -/
def base_two_agrees_stmt : Prop := ∀ K J : ℕ, racetrackListB 2 K J = racetrackList K J

end Odds
