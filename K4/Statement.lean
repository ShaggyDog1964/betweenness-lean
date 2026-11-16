/-
# K ≥ 4: statement of the racetrack theorem and the sharp impossibility

This file contains ONLY definitions and headline `Prop`s. There are no theorems, no proof
holes, and no assumed axioms. It does not import any `REU.*` file: the general-dimension
simplex and the betweenness axioms are restated here so that they can be audited on their own.

Plain-language summary of `target_stmt` (end of file):
  (A) For every K ≥ 4 and every J ≥ 1, the explicit list `racetrackList K J` (4J+2 lotteries)
      has no repeated entries, lies in the simplex, is NOT the strict ranking of any
      betweenness preference, and becomes such a ranking after deleting any single entry.
  (B) For every K ≥ 4 and every n, `LocalComplete K n` fails: some finite strict order in the
      simplex is n-locally representable but not representable.
(B) follows from (A) by an easy argument (take 4J+2 > n; every sub-order with at most 4J+1
elements sits inside a one-point deletion). Both are stated explicitly. The random-rule
version is NOT stated here; it follows from (B) through the point-mass remark, but that step
is not part of this statement.

Conventions. Prizes are `Fin K`, numbered `0 < 1 < … < K-1` from worst to best. So the
1-based prizes 1,2,3,4 are indices 0,1,2,3 here. A lottery is a function `Fin K → ℝ`.
-/
import Mathlib

namespace K4

/-! ## 1. Simplex, mixtures, FOSD -/

/-- A lottery over `K` prizes: `p i` is the probability of prize `i` (prize `0` is worst).
Only points of `Simplex K` are real lotteries; other functions are just ambient points. -/
abbrev Lot (K : ℕ) := Fin K → ℝ

/-- The probability simplex Δ^{K-1}: nonnegative entries that sum to 1. (This matches
Mathlib's `stdSimplex ℝ (Fin K)`; it is written out here so it can be read directly.) -/
def Simplex (K : ℕ) : Set (Lot K) := {p | (∀ i, 0 ≤ p i) ∧ ∑ i, p i = 1}

/-- The mixture `t • q + (1 - t) • r`, taken coordinate by coordinate. -/
def mix {K : ℕ} (t : ℝ) (q r : Lot K) : Lot K := t • q + (1 - t) • r

/-- Upper tail: the probability that `p` gives a prize at least as good as `k`. -/
def tail {K : ℕ} (p : Lot K) (k : Fin K) : ℝ :=
  ∑ i ∈ Finset.univ.filter (fun i : Fin K => k ≤ i), p i

/-- `q` weakly first-order stochastically dominates `r`: for every prize `k`, `q` is at least
as likely as `r` to give a prize at least as good as `k`.
(At K = 3 this is exactly `REU.FOSD`: the `k = 1` tail is `1 - prob(worst)` and the `k = 2`
tail is `prob(best)`; the `k = 0` tail is the total mass, equal to 1 on the simplex.) -/
def FOSD {K : ℕ} (q r : Lot K) : Prop := ∀ k : Fin K, tail r k ≤ tail q k

/-- Strict FOSD: weak dominance and `q ≠ r`. -/
def StrictFOSD {K : ℕ} (q r : Lot K) : Prop := FOSD q r ∧ q ≠ r

/-! ## 2. Betweenness preferences, from the axioms -/

/-- A binary relation on lotteries; `R q r` reads "q is weakly preferred to r". -/
abbrev Rel (K : ℕ) := Lot K → Lot K → Prop

/-- Strict part: `q ≻ r` means `q ≽ r` and not `r ≽ q`. -/
def SPref {K : ℕ} (R : Rel K) (q r : Lot K) : Prop := R q r ∧ ¬ R r q

/-- Indifference: `q ∼ r` means `q ≽ r` and `r ≽ q`. -/
def Indiff {K : ℕ} (R : Rel K) (q r : Lot K) : Prop := R q r ∧ R r q

/-- A betweenness preference on the simplex Δ^{K-1}. Same axioms as
`REU.IsBetweennessPref`, in general dimension. Every axiom quantifies only over points of
`Simplex K`; the relation is unconstrained off the simplex.
Continuity: the upper and lower contour sets are closed in the subspace topology of the
simplex (the ambient topology on `Fin K → ℝ` is the usual product topology). -/
structure IsBetweennessPref {K : ℕ} (R : Rel K) : Prop where
  /-- Completeness: any two lotteries are comparable. -/
  complete : ∀ q ∈ Simplex K, ∀ r ∈ Simplex K, R q r ∨ R r q
  /-- Transitivity. -/
  trans : ∀ q ∈ Simplex K, ∀ r ∈ Simplex K, ∀ s ∈ Simplex K, R q r → R r s → R q s
  /-- `{q ∈ Δ : q ≽ r}` is closed in `Δ`. -/
  closed_upper : ∀ r ∈ Simplex K, IsClosed {q : Simplex K | R q.1 r}
  /-- `{q ∈ Δ : r ≽ q}` is closed in `Δ`. -/
  closed_lower : ∀ r ∈ Simplex K, IsClosed {q : Simplex K | R r q.1}
  /-- Strict FOSD monotonicity: strict dominance implies strict preference. -/
  strictMono : ∀ q ∈ Simplex K, ∀ r ∈ Simplex K, StrictFOSD q r → SPref R q r
  /-- Betweenness, strict part: `q ≻ r ⇒ q ≻ tq + (1-t)r ≻ r` for `t ∈ (0,1)`. -/
  btw_strict : ∀ q ∈ Simplex K, ∀ r ∈ Simplex K, ∀ t ∈ Set.Ioo (0 : ℝ) 1,
    SPref R q r → SPref R q (mix t q r) ∧ SPref R (mix t q r) r
  /-- Betweenness, indifference part: `q ∼ r ⇒ tq + (1-t)r ∼ q` for `t ∈ (0,1)`. -/
  btw_indiff : ∀ q ∈ Simplex K, ∀ r ∈ Simplex K, ∀ t ∈ Set.Ioo (0 : ℝ) 1,
    Indiff R q r → Indiff R (mix t q r) q

/-! ## 3. Strict orders on finite sets, representability, locality

A strict (total) order on a finite set `X` is encoded as a list with no repeated entries,
listed from best to worst; `X` is the set of entries. This encoding is faithful: each finite
strict total order is exactly one such list. Restricting the order to a subset `Y ⊆ X` gives
the sublist of entries in `Y`, in the same order (`List.Sublist`). -/

/-- The list `L` (best first) is representable: some betweenness preference ranks every
earlier entry STRICTLY above every later entry. For a list without repeats this says exactly
that the order is the restriction of `≻` to the entries (strictness on the entries follows,
because each pair is strictly ranked one way). A list with a repeated entry is never
representable, which is why the family claim below also asserts `Nodup`. -/
def Representable {K : ℕ} (L : List (Lot K)) : Prop :=
  ∃ R : Rel K, IsBetweennessPref R ∧ L.Pairwise (SPref R)

/-- `n`-locally representable: every sub-order with at most `n` elements is representable. -/
def LocallyRepresentable {K : ℕ} (n : ℕ) (L : List (Lot K)) : Prop :=
  ∀ L' : List (Lot K), L'.Sublist L → L'.length ≤ n → Representable L'

/-- `LocalComplete(K, n)`: every `n`-locally representable strict order on
every finite subset of Δ^{K-1} is representable. -/
def LocalComplete (K n : ℕ) : Prop :=
  ∀ L : List (Lot K), L.Nodup → (∀ x ∈ L, x ∈ Simplex K) →
    LocallyRepresentable n L → Representable L

/-! ## 4. The racetrack family

Edge lotteries: two-point lotteries whose odds ratio is a power of 2. For `K > 4` the extra
prizes `4, …, K-1` get probability 0 (the family lives on the face of prizes 0,1,2,3). -/

/-- `edgeLot K i j c`: probability `2^c/(2^c+1)` on prize `i`, `1/(2^c+1)` on prize `j`, zero
elsewhere. So the ratio `prob(i) / prob(j)` is `2^c`. (Used only with `i ≠ j`, both `< 4`.) -/
noncomputable def edgeLot (K i j c : ℕ) : Lot K := fun k =>
  if k.val = i then (2 : ℝ) ^ c / ((2 : ℝ) ^ c + 1)
  else if k.val = j then 1 / ((2 : ℝ) ^ c + 1)
  else 0

/-- `P[c] = (2^c, 0, 1, 0)/(2^c+1)`: weight on 1-based prizes 1 and 3 (indices 0 and 2). -/
noncomputable def lotP (K c : ℕ) : Lot K := edgeLot K 0 2 c

/-- `Q[c] = (0, 2^c, 1, 0)/(2^c+1)`: weight on 1-based prizes 2 and 3 (indices 1 and 2). -/
noncomputable def lotQ (K c : ℕ) : Lot K := edgeLot K 1 2 c

/-- `R[c] = (0, 2^c, 0, 1)/(2^c+1)`: weight on 1-based prizes 2 and 4 (indices 1 and 3). -/
noncomputable def lotR (K c : ℕ) : Lot K := edgeLot K 1 3 c

/-- Parameter `g = 4` (rise of the `P` exponent inside one block). -/
def parG_small (_J : ℕ) : ℕ := 4
/-- Parameter `G = 4J + 4` (rise of the `Q` exponent inside one block). -/
def parG (J : ℕ) : ℕ := 4 * J + 4
/-- Parameter `h = 4J + 8` (spacing of `P` exponents between blocks). -/
def parH (J : ℕ) : ℕ := 4 * J + 8
/-- Parameter `beta = 4J` (the `R`-budget per block; total budget `J * beta`). -/
def parBeta (J : ℕ) : ℕ := 4 * J
/-- Parameter `D = J*h + 1` (first `Q` exponent). -/
def parD (J : ℕ) : ℕ := J * parH J + 1
/-- Parameter `v0 = D + J(G+2) + 4J + 1` (exponent of the top `R`). -/
def parV0 (J : ℕ) : ℕ := parD J + J * (parG J + 2) + 4 * J + 1

/-- `a_j = (j-1) h`, written with a 0-based block index `i = j - 1`. -/
def expA (J i : ℕ) : ℕ := i * parH J
/-- `d_j = D + (j-1)(G+2)`, written with a 0-based block index `i = j - 1`. -/
def expD (J i : ℕ) : ℕ := parD J + i * (parG J + 2)

/-- Block `j = i + 1`, best to worst: `A_j = P[a_j]`, `D_j = Q[d_j]`, `D'_j = Q[d_j + G]`,
`A'_j = P[a_j + g]`. -/
noncomputable def block (K J i : ℕ) : List (Lot K) :=
  [lotP K (expA J i), lotQ K (expD J i), lotQ K (expD J i + parG J),
   lotP K (expA J i + parG_small J)]

/-- Blocks `1, …, m` (0-based indices `0, …, m-1`) concatenated in order. -/
noncomputable def blocksUpTo (K J : ℕ) : ℕ → List (Lot K)
  | 0 => []
  | m + 1 => blocksUpTo K J m ++ block K J m

/-- The order `X_J`, best to worst: `R[v0]`, then blocks `1..J`, then `R[v0 + J*beta]`.
Length `4J + 2`. Example `J = 1` (`g=4, G=8, h=12, D=13, v0=28`):
`R[28] > P[0] > Q[13] > Q[21] > P[4] > R[32]`. -/
noncomputable def racetrackList (K J : ℕ) : List (Lot K) :=
  [lotR K (parV0 J)] ++ blocksUpTo K J J ++ [lotR K (parV0 J + J * parBeta J)]

/-- `X_J` is a critical obstruction in Δ^{K-1}: no repeated entries, every entry is a
lottery, the whole order is NOT representable, and deleting any single entry (position
`k`) leaves a representable order. -/
def RacetrackCritical (K J : ℕ) : Prop :=
  (racetrackList K J).Nodup ∧
  (∀ x ∈ racetrackList K J, x ∈ Simplex K) ∧
  ¬ Representable (racetrackList K J) ∧
  ∀ k < (racetrackList K J).length, Representable ((racetrackList K J).eraseIdx k)

/-! ## 5. Headline statements -/

/-- (A) The racetrack family is critical for every `K ≥ 4` and `J ≥ 1`. -/
def racetrack_stmt : Prop :=
  ∀ K : ℕ, 4 ≤ K → ∀ J : ℕ, 1 ≤ J → RacetrackCritical K J

/-- (B) Sharp impossibility: for every `K ≥ 4` and every `n`, `LocalComplete K n`
fails. -/
def sharp_impossibility_stmt : Prop :=
  ∀ K : ℕ, 4 ≤ K → ∀ n : ℕ, ¬ LocalComplete K n

/-- The whole claim of the target: (A) and (B). -/
def target_stmt : Prop := racetrack_stmt ∧ sharp_impossibility_stmt

/-! ## 6. Non-vacuity control (statement only, not part of the target)

At K = 3 the analogue of (B) should be FALSE: `LocalComplete 3 4` is expected to hold. The
reason is outside this file and unchecked here: Theorem 1 (`REU.thm1_stmt`, proved in Lean)
with the point-mass remark. For the point-mass rule of a strict order,
Bracketing holds automatically and Chord Dominance only looks at sets of at most 4 points.
Transferring this needs the affine identification of `Simplex 3` with `REU.Tri`
(`(u, v) = (p 0, p 2)`), which is not formalized. Separately, the family (A) does not make
sense at K = 3: `lotR 3 c` puts mass `2^c/(2^c+1) < 1` on prize 1 and nothing else, so it is
not in `Simplex 3`, and the `Simplex` conjunct of `RacetrackCritical 3 J` is false. -/
def control_K3_stmt : Prop := LocalComplete 3 4

end K4
