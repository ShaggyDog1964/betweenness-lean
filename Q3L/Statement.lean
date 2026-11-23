/-
# Planar dichotomy: statement

Planar dichotomy: on a finite set `X` of lotteries whose affine hull has dimension at most 2,
binary choice probabilities determine menu choice probabilities for every mixture of
betweenness preferences exactly when the direction plane of `X` contains a nonzero weak-FOSD
direction.

This file contains ONLY definitions and headline `Prop`s. There are no theorems, no proof
holes, and no assumed axioms.

Source: Theorem 36 of the working paper, parts (1), (2) and (3), which are (i), (ii) and (iii)
here. Theorem, lemma, example and equation numbers in the comments of `Q3L` refer to the
working paper. Part (ii) is stated for general `K ≥ 3`, as in the paper, not only for `K = 4`.
(At `K = 3` the hypothesis of (ii) can never hold, so (ii) is vacuous there.) Lemma 86 and
Example 37 of the paper are NOT part of the target; the hypotheses of (i) and (ii) are shown
to be satisfiable only by the separate control statements in Section 7 below, which are also
not part of the target.

Reused verbatim from `K4.Statement` (audited), not restated:
  * `K4.Lot K` (a lottery is a function `Fin K → ℝ`; prize `0` is worst, `K-1` best),
  * `K4.Simplex K` (nonnegative entries summing to 1),
  * `K4.tail p k` (`∑_{i ≥ k} p i`, the upper tail at prize `k`),
  * `K4.Rel`, `K4.SPref` (strict part `q ≻ r`),
  * `K4.IsBetweennessPref` (BT: complete, transitive, continuous, strictly FOSD-monotone,
    betweenness), all axioms quantified over the simplex only.

Restated here for `K` prizes, word for word as in `REU.Statement` (which has them only for
the 3-prize triangle `REU.Pt`): `StrictOn`, `IsMaxIn`, `RandomChoiceRule`, `IsMixture`,
`minOr1`. The only change is the type of lotteries (`K4.Lot K` instead of `REU.Pt`).

New here: `dot`, `euRel`, `IsEUPref` (EU by a utility vector), the direction space, the
weak-FOSD cone, the north/south split of a menu, formula (1), binary reduction, the
"½[u] + ½[Mw − u]" form of the counterexample mixtures, and the at-most-two-rankings
predicate of the collinear case.

Decidability: finite sets of lotteries and filters on them use classical decidability
(as in `REU.Statement`).
-/
import Mathlib
import K4.Statement

namespace Q3L

open K4 (Lot Simplex tail Rel SPref IsBetweennessPref)

/-! ## 1. Choice from menus (restated from `REU.Statement` for `K` prizes) -/

/-- `R` is strict on `X`: no two distinct elements of `X` are indifferent under `R`.
(Same as `REU.StrictOn`.) -/
def StrictOn {K : ℕ} (R : Rel K) (X : Finset (Lot K)) : Prop :=
  ∀ x ∈ X, ∀ y ∈ X, x ≠ y → ¬ (R x y ∧ R y x)

/-- `x` is the (unique) `R`-best element of menu `A`: `x ∈ A` and `x ≻ y` (strictly) for
every other `y ∈ A`. (Same as `REU.IsMaxIn`.) -/
def IsMaxIn {K : ℕ} (R : Rel K) (x : Lot K) (A : Finset (Lot K)) : Prop :=
  x ∈ A ∧ ∀ y ∈ A, y ≠ x → SPref R x y

/-- A random choice rule on the menus of `X` (menus = nonempty `A ⊆ X`).
`p x A` is the probability that `x` is chosen from `A`. Values on non-menus are junk;
only `A ⊆ X` is constrained: probabilities are nonnegative, zero outside the menu, and sum
to 1 over a nonempty menu. (Same as `REU.RandomChoiceRule`.) -/
structure RandomChoiceRule {K : ℕ} (X : Finset (Lot K)) where
  p : Lot K → Finset (Lot K) → ℝ
  nonneg : ∀ A ⊆ X, ∀ x, 0 ≤ p x A
  zero_of_not_mem : ∀ A ⊆ X, ∀ x, x ∉ A → p x A = 0
  sum_one : ∀ A ⊆ X, A.Nonempty → ∑ x ∈ A, p x A = 1

open Classical in
/-- `ρ` is a finite mixture of preferences from class `C`, each strict on `X`:
finitely many relations `R i` in `C`, weights `w i ≥ 0` summing to 1, with
`ρ(x, A) = Σ_i w_i · [x is the R_i-best element of A]` on every menu `A ⊆ X` and every
`x ∈ A`. (Same as `REU.IsMixture`.) With `C = IsBetweennessPref` this is "a mixture of
betweenness preferences strict on `X`". -/
def IsMixture {K : ℕ} (C : Rel K → Prop) (X : Finset (Lot K)) (ρ : RandomChoiceRule X) :
    Prop :=
  ∃ (n : ℕ) (R : Fin n → Rel K) (w : Fin n → ℝ),
    (∀ i, C (R i) ∧ StrictOn (R i) X) ∧
    (∀ i, 0 ≤ w i) ∧
    ∑ i, w i = 1 ∧
    ∀ A ⊆ X, A.Nonempty → ∀ x ∈ A,
      ρ.p x A = ∑ i, if IsMaxIn (R i) x A then w i else 0

/-- Minimum of `g` over a finite set, with the convention `min ∅ = 1`.
(Same as `REU.minOr1`.) -/
noncomputable def minOr1 {K : ℕ} (S : Finset (Lot K)) (g : Lot K → ℝ) : ℝ :=
  if h : S.Nonempty then S.inf' h g else 1

/-! ## 2. Expected utility (by a utility vector) -/

/-- Euclidean pairing `u · p = ∑_k u k * p k` (expected utility of `p` under utility `u`). -/
noncomputable def dot {K : ℕ} (u p : Lot K) : ℝ := ∑ k, u k * p k

/-- The EU relation of the utility vector `u`: `p` is weakly preferred to `q` iff
`u · q ≤ u · p`. -/
def euRel {K : ℕ} (u : Lot K) : Rel K := fun p q => dot u q ≤ dot u p

/-- `R` is an EU preference: on the simplex it coincides with `euRel u` for some utility
vector `u` with strictly increasing coordinates (`u 0 < u 1 < … < u (K-1)`; `StrictMono`
on `Fin K` with its usual order). This is the paper's class of preferences `≿_u` with `u`
strictly increasing. It is NOT the
axiomatic `REU.IsEUPref` (BT plus independence), and it does not by itself include the BT
axioms; that is why part (ii) below separately asserts that its mixtures are mixtures of
betweenness preferences. -/
def IsEUPref {K : ℕ} (R : Rel K) : Prop :=
  ∃ u : Lot K, StrictMono u ∧
    ∀ p ∈ Simplex K, ∀ q ∈ Simplex K, (R p q ↔ dot u q ≤ dot u p)

/-! ## 3. Geometry: direction space, affine hull, weak-FOSD cone -/

/-- The direction space `V` of `aff(X)`: the linear span of all differences `p - q` with
`p, q ∈ X` (Mathlib's `vectorSpan`, which equals the direction of `affineSpan`).
`dim aff(X) = finrank V`. `X` is collinear iff `finrank V ≤ 1`. -/
noncomputable def dirSpace {K : ℕ} (X : Finset (Lot K)) : Submodule ℝ (Lot K) :=
  vectorSpan ℝ (↑X : Set (Lot K))

/-- The affine hull `aff(X)` of `X` (Mathlib's `affineSpan`). Empty iff `X` is empty. -/
noncomputable def affHull {K : ℕ} (X : Finset (Lot K)) : AffineSubspace ℝ (Lot K) :=
  affineSpan ℝ (↑X : Set (Lot K))

/-- The cone `D` of weak-FOSD directions: vectors `d` with total sum `0` (so `d ∈ H_0`) and
every upper tail `t_j(d) = ∑_{k ≥ j} d k` nonnegative. The tail at `j = 0` is the total sum,
which is `0`, so the condition there is automatic; the real conditions are `j = 1, …, K-1`,
as for the cone `F` of the paper. For lotteries `p, q`, `p - q ∈ D` iff `p` weakly
FOSD-dominates `q`. -/
def FOSDCone (K : ℕ) : Set (Lot K) :=
  {d | ∑ k, d k = 0 ∧ ∀ j : Fin K, 0 ≤ tail d j}

/-- `V ∩ D = {0}`: the only weak-FOSD direction in the direction space of `X` is `0`. -/
def MeetsConeTrivially {K : ℕ} (X : Finset (Lot K)) : Prop :=
  ∀ d ∈ dirSpace X, d ∈ FOSDCone K → d = 0

/-- `aff(X)` lies in an EU indifference hyperplane: there are `w` with strictly increasing
coordinates and a number `γ` with `w · p = γ` for every `p ∈ aff(X)`. -/
def InIndiffHyperplane {K : ℕ} (X : Finset (Lot K)) (w : Lot K) : Prop :=
  StrictMono w ∧ ∃ γ : ℝ, ∀ p ∈ affHull X, dot w p = γ

/-! ## 4. Formula (1) and binary reduction -/

/-- `y` is north of `x` in the frame `(d0, g)`: writing `x - y = α d0 + β g`, the
coefficient `β` is positive. Used only when `d0, g` are linearly independent and span the
direction space, and `x, y ∈ X`; then `x - y` has exactly one such decomposition, so this is
the condition `μ(x, y) > 0` of Theorem 36(1), where the paper writes `λ, μ` for `α, β`. Its
negation is `β(x, y) ≤ 0`. -/
def IsNorth {K : ℕ} (d0 g x y : Lot K) : Prop :=
  ∃ α β : ℝ, x - y = α • d0 + β • g ∧ 0 < β

open Classical in
/-- `A_N(x) = {y ∈ A \ {x} : β(x, y) > 0}`. -/
noncomputable def AN {K : ℕ} (d0 g : Lot K) (A : Finset (Lot K)) (x : Lot K) :
    Finset (Lot K) :=
  A.filter (fun y => y ≠ x ∧ IsNorth d0 g x y)

open Classical in
/-- `A_S(x) = {y ∈ A \ {x} : β(x, y) ≤ 0}`: everything in `A` other than `x` that is not in
`A_N(x)`. -/
noncomputable def AS {K : ℕ} (d0 g : Lot K) (A : Finset (Lot K)) (x : Lot K) :
    Finset (Lot K) :=
  A.filter (fun y => y ≠ x ∧ ¬ IsNorth d0 g x y)

/-- Formula (1), the displayed formula of Theorem 36(1), for the frame `(d0, g)`: for every
menu `A ⊆ X` and `x ∈ A`,
`ρ(x, A) = max(0, min_{y ∈ A_S(x)} ρ(x,{x,y}) + min_{y ∈ A_N(x)} ρ(x,{x,y}) − 1)`,
with an empty minimum equal to 1. (For `A = {x}` both sets are empty and the right side is
`1`.) -/
def PlanarFormula {K : ℕ} (X : Finset (Lot K)) (ρ : RandomChoiceRule X) (d0 g : Lot K) :
    Prop :=
  ∀ A ⊆ X, ∀ x ∈ A,
    ρ.p x A = max 0 (minOr1 (AS d0 g A x) (fun y => ρ.p x {x, y})
                    + minOr1 (AN d0 g A x) (fun y => ρ.p x {x, y}) - 1)

/-- A binary reduction holds on `X`: any two mixtures of betweenness preferences (each strict
on `X`) that agree on every binary menu `{x, y} ⊆ X` agree on every menu `A ⊆ X`. -/
def BinaryReduction {K : ℕ} (X : Finset (Lot K)) : Prop :=
  ∀ ρ ρ' : RandomChoiceRule X,
    IsMixture IsBetweennessPref X ρ → IsMixture IsBetweennessPref X ρ' →
    (∀ x ∈ X, ∀ y ∈ X, ρ.p x {x, y} = ρ'.p x {x, y}) →
    ∀ A ⊆ X, A.Nonempty → ∀ x ∈ A, ρ.p x A = ρ'.p x A

/-! ## 5. The counterexample form of part (ii) and the collinear case -/

/-- `ρ = ½[u] + ½[M w − u]`: there are a utility vector `u` and a number `M` such that both
`u` and `M w − u` have strictly increasing coordinates, both EU relations are strict on `X`,
and on every menu `A ⊆ X` the rule `ρ` picks the `u`-best element with probability `½` and
the `(M w − u)`-best element with probability `½` (adding up when they coincide). -/
def IsHalfReversal {K : ℕ} (X : Finset (Lot K)) (w : Lot K) (ρ : RandomChoiceRule X) :
    Prop :=
  ∃ (u : Lot K) (M : ℝ),
    StrictMono u ∧ StrictMono (M • w - u) ∧
    StrictOn (euRel u) X ∧ StrictOn (euRel (M • w - u)) X ∧
    ∀ A ⊆ X, A.Nonempty → ∀ x ∈ A,
      ρ.p x A = (open Classical in if IsMaxIn (euRel u) x A then 1 / 2 else 0)
              + (open Classical in if IsMaxIn (euRel (M • w - u)) x A then 1 / 2 else 0)

/-- At most two strict rankings of `X` come from betweenness preferences: among any three
betweenness preferences that are strict on `X`, two rank `X` identically (the same strict
comparisons between all pairs of elements of `X`). This is the claim of Theorem 36(3) that at
most two rankings are representable. -/
def AtMostTwoRankings {K : ℕ} (X : Finset (Lot K)) : Prop :=
  ∀ R : Fin 3 → Rel K, (∀ i, IsBetweennessPref (R i) ∧ StrictOn (R i) X) →
    ∃ i j : Fin 3, i ≠ j ∧ ∀ x ∈ X, ∀ y ∈ X, (SPref (R i) x y ↔ SPref (R j) x y)

/-! ## 6. Headline statements -/

/-- Theorem 36(1). Let `K ≥ 3`, `X` a finite subset of the simplex with `dim V = 2`, `d0` a
nonzero weak-FOSD direction in `V`, and `g ∈ V` with `d0, g` linearly independent. Then every
mixture of betweenness preferences strict on `X` satisfies formula (1) in the frame
`(d0, g)`, and a binary reduction holds on `X`. (Every admissible frame is covered.) -/
def part_i_stmt : Prop :=
  ∀ K : ℕ, 3 ≤ K → ∀ X : Finset (Lot K), (↑X : Set (Lot K)) ⊆ Simplex K →
    Module.finrank ℝ (dirSpace X) = 2 →
    ∀ d0 ∈ dirSpace X, d0 ∈ FOSDCone K → d0 ≠ 0 →
    ∀ g ∈ dirSpace X, LinearIndependent ℝ ![d0, g] →
      (∀ ρ : RandomChoiceRule X, IsMixture IsBetweennessPref X ρ → PlanarFormula X ρ d0 g) ∧
      BinaryReduction X

/-- Theorem 36(2). Let `K ≥ 3` and `X` a finite subset of the simplex with `dim V = 2`.
(a) `V ∩ D = {0}` iff `aff(X)` lies in an EU indifference hyperplane `w · p = γ` with `w`
strictly increasing.
(b) If `V ∩ D = {0}`, then for some such `w` there are two random choice rules `ρ, ρ'` on `X`,
each of the form `½[u] + ½[M w − u]`, each a mixture of EU preferences and a mixture of
betweenness preferences (strict on `X`), with every binary probability `ρ(x,{x,y})`,
`ρ'(x,{x,y})` equal to `½` for distinct `x, y ∈ X`, that differ on some 3-element menu;
and no binary reduction holds on `X`. -/
def part_ii_stmt : Prop :=
  ∀ K : ℕ, 3 ≤ K → ∀ X : Finset (Lot K), (↑X : Set (Lot K)) ⊆ Simplex K →
    Module.finrank ℝ (dirSpace X) = 2 →
      (MeetsConeTrivially X ↔ ∃ w : Lot K, InIndiffHyperplane X w) ∧
      (MeetsConeTrivially X →
        (∃ w : Lot K, InIndiffHyperplane X w ∧
          ∃ ρ ρ' : RandomChoiceRule X,
            IsHalfReversal X w ρ ∧ IsHalfReversal X w ρ' ∧
            IsMixture IsEUPref X ρ ∧ IsMixture IsEUPref X ρ' ∧
            IsMixture IsBetweennessPref X ρ ∧ IsMixture IsBetweennessPref X ρ' ∧
            (∀ x ∈ X, ∀ y ∈ X, x ≠ y → ρ.p x {x, y} = 1 / 2 ∧ ρ'.p x {x, y} = 1 / 2) ∧
            ∃ A ⊆ X, A.card = 3 ∧ ∃ x ∈ A, ρ.p x A ≠ ρ'.p x A) ∧
        ¬ BinaryReduction X)

/-- Theorem 36(3), the collinear case. Let `K ≥ 3` and `X` a finite subset of the simplex
with `dim V ≤ 1`. Then betweenness preferences strict on `X` induce at most two rankings of
`X`, and a binary reduction holds on `X`. (Theorem 36(3) also identifies the two rankings as the
two orders along the line; that identification is not stated here.) -/
def part_iii_stmt : Prop :=
  ∀ K : ℕ, 3 ≤ K → ∀ X : Finset (Lot K), (↑X : Set (Lot K)) ⊆ Simplex K →
    Module.finrank ℝ (dirSpace X) ≤ 1 →
      AtMostTwoRankings X ∧ BinaryReduction X

/-- The whole claim: parts (i), (ii) and (iii). Together they cover every
finite `X` with `dim aff(X) ≤ 2`: `dim V ≤ 1` is (iii); `dim V = 2` is (i) when `V ∩ D ≠ {0}`
and (ii) when `V ∩ D = {0}`. -/
def target_stmt : Prop := part_i_stmt ∧ part_ii_stmt ∧ part_iii_stmt

/-! ## 7. Non-vacuity controls (statements only, NOT part of the target)

These say that the hypotheses of (i) and (ii) can hold, so neither part is vacuous. -/

/-- The three lotteries of Example 37 (`K = 4`):
`a = (½, 0, 0, ½)`, `b = (0, ½, ½, 0)`, `c = (¼, 0, ¾, 0)`. -/
noncomputable def ctrlX_ii : Finset (Lot 4) :=
  {![1/2, 0, 0, 1/2], ![0, 1/2, 1/2, 0], ![1/4, 0, 3/4, 0]}

/-- Control for (ii): `ctrlX_ii` lies in the simplex, has `dim V = 2`, and `V ∩ D = {0}`. -/
def control_ii_stmt : Prop :=
  (↑ctrlX_ii : Set (Lot 4)) ⊆ Simplex 4 ∧ Module.finrank ℝ (dirSpace ctrlX_ii) = 2 ∧
    MeetsConeTrivially ctrlX_ii

/-- The face `{e_0, e_1, e_2}` of the 3-simplex (`K = 4`; `e_k` is the sure prize `k`). -/
noncomputable def ctrlX_i : Finset (Lot 4) :=
  {![1, 0, 0, 0], ![0, 1, 0, 0], ![0, 0, 1, 0]}

/-- Control for (i): `ctrlX_i` lies in the simplex, has `dim V = 2`, and contains the
nonzero weak-FOSD direction `e_1 − e_0` in `V`. -/
def control_i_stmt : Prop :=
  (↑ctrlX_i : Set (Lot 4)) ⊆ Simplex 4 ∧ Module.finrank ℝ (dirSpace ctrlX_i) = 2 ∧
    ∃ d0 ∈ dirSpace ctrlX_i, d0 ∈ FOSDCone 4 ∧ d0 ≠ 0

end Q3L
