/-
# Q1: statement of the two-attribute example

Separate quasi-concavity on the plane. This file contains ONLY definitions and headline
`Prop`s. There are no theorems, no proof holes and no assumed axioms. It imports nothing
from `REU.*` or `K4.*`, so it can be audited on its own. The target is Proposition 15 of
the working paper.

Plain-language summary of `target_stmt` (end of file):
  (a) H-QC rankings are 3-local and not 2-local (so the locality number is exactly 3).
      The same holds for V-QC rankings.
  (b) Rankings of preferences that are H-QC and V-QC at the same time are n-local for
      no n.

Setting. Alternatives are points of `ℝ × ℝ`. A preference is any complete, transitive
relation on ALL of `ℝ × ℝ`. Continuity is NOT imposed, and there is no monotonicity
or dominance condition. Coordinates: `x.1` is the first (horizontal) coordinate and `x.2`
the second (vertical) one. A horizontal line is a set `{x | x.2 = c}` and a vertical line
is a set `{x | x.1 = c}`.

An explicit family (zigzag midpoint chains) is defined in Section 5 with its
criticality claim `zigzag_stmt`. That claim is NOT part of `target_stmt`. It is recorded
for the proof and for the audit only.
-/
import Mathlib

namespace Q1

/-! ## 1. Preferences on the plane -/

/-- A point of the plane: one alternative with two attributes. -/
abbrev Pt := ℝ × ℝ

/-- A binary relation on the plane. `R x y` reads "x is weakly preferred to y". -/
abbrev Rel := Pt → Pt → Prop

/-- Strict part: `x ≻ y` means `x ≽ y` and not `y ≽ x`. -/
def SPref (R : Rel) (x y : Pt) : Prop := R x y ∧ ¬ R y x

/-- An admissible preference: a weak order on the whole plane, that is, complete and
transitive. Reflexivity follows from completeness. Nothing else is required. In
particular continuity is not required. -/
structure IsWeakOrder (R : Rel) : Prop where
  /-- Completeness: any two points are comparable. -/
  complete : ∀ x y : Pt, R x y ∨ R y x
  /-- Transitivity. -/
  trans : ∀ x y z : Pt, R x y → R y z → R x z

/-! ## 2. The two properties -/

/-- P = H-QC (horizontal quasi-concavity). Every upper contour set `{y | y ≽ x}` meets
every horizontal line in an interval. Written out: if `y` and `z` lie on one horizontal
line and are both weakly preferred to `x`, then every point `w` of that line whose first
coordinate lies between those of `y` and `z` is also weakly preferred to `x`.
(`Set.uIcc a b` is the closed interval between `a` and `b`, in either order.)
Equivalently: for each fixed second coordinate, the preference restricted to that line is
quasi-concave (single-peaked, plateaus allowed). -/
def HQC (R : Rel) : Prop :=
  ∀ x y z w : Pt, y.2 = z.2 → w.2 = y.2 → w.1 ∈ Set.uIcc y.1 z.1 →
    R y x → R z x → R w x

/-- Q = V-QC (vertical quasi-concavity). The same condition as `HQC` with the two
coordinates swapped: every upper contour set meets every vertical line in an interval. -/
def VQC (R : Rel) : Prop :=
  ∀ x y z w : Pt, y.1 = z.1 → w.1 = y.1 → w.2 ∈ Set.uIcc y.2 z.2 →
    R y x → R z x → R w x

/-- P and Q: ONE preference that is both H-QC and V-QC. Equivalently, every upper contour
set is orthogonally convex. This is the conjunction of the properties for a single
preference. It is not the intersection of the two ranking classes. -/
def HVQC (R : Rel) : Prop := HQC R ∧ VQC R

/-! ## 3. Rankings, the class R(P), locality

A strict ranking of a finite set `S` of points is encoded as a list with no repeated
entries, listed from best to worst. `S` is the set of entries. Each strict total order on a
finite set is exactly one such list. Restricting the ranking to a subset of `S` gives the
sublist of entries in that subset, in the same order (`List.Sublist`). -/

/-- The list `L` (best first) is in R(Prop): some admissible preference with property
`Prop` ranks every earlier entry STRICTLY above every later entry. For a list without
repeats, this says exactly that the ranking is the restriction of that preference's
strict part to the entries. A list with a repeated entry is never in R(Prop), because
`SPref R x x` is false. -/
def InR (P : Rel → Prop) (L : List Pt) : Prop :=
  ∃ R : Rel, IsWeakOrder R ∧ P R ∧ L.Pairwise (SPref R)

/-- `L` passes every test of size at most `n`: each sub-ranking of `L` with at most `n`
elements is in R(Prop). -/
def LocallyInR (P : Rel → Prop) (n : ℕ) (L : List Pt) : Prop :=
  ∀ L' : List Pt, L'.Sublist L → L'.length ≤ n → InR P L'

/-- R(Prop) is `n`-local: every ranking (list without repeats) whose sub-rankings with at
most `n` elements are all in R(Prop) is itself in R(Prop).
(Monotone in `n`: `n`-local implies `(n+1)`-local.) -/
def IsLocal (P : Rel → Prop) (n : ℕ) : Prop :=
  ∀ L : List Pt, L.Nodup → LocallyInR P n L → InR P L

/-! ## 4. Headline statements -/

/-- (a) for P. R(H-QC) is 3-local and NOT 2-local, so its locality number is exactly 3.
(The intended witness for "not 2-local" is `(0,0) ≻ (2,0) ≻ (1,0)`.) -/
def hqc_stmt : Prop := IsLocal HQC 3 ∧ ¬ IsLocal HQC 2

/-- (a) for Q. R(V-QC) is 3-local and NOT 2-local, so its locality number is exactly 3. -/
def vqc_stmt : Prop := IsLocal VQC 3 ∧ ¬ IsLocal VQC 2

/-- (b) R(H-QC and V-QC) is `n`-local for no `n`. -/
def hvqc_stmt : Prop := ∀ n : ℕ, ¬ IsLocal HVQC n

/-- The whole claim (Proposition 15 of the working paper): (a) for H-QC, (a) for V-QC, and
(b). -/
def target_stmt : Prop := hqc_stmt ∧ vqc_stmt ∧ hvqc_stmt

/-! ## 5. The zigzag family (auxiliary, NOT part of `target_stmt`)

Zigzag midpoint chains. Set `p_0 = a_0 = (0,0)`. For `k ≥ 1`, segment
`s_k` has length `2k`, starts at `p_{k-1}`, and goes right for odd `k` and up for even `k`.
Its end is `a_k` and its midpoint is `p_k`. (For `k = 1` this gives `a_1 = (2,0)` and
`p_1 = (1,0)`.) The ranking is `a_0 ≻ a_1 ≻ … ≻ a_n ≻ p_n`, with
`n + 2` entries. Example `n = 4`: `(0,0),(2,0),(1,4),(7,2),(4,10)`, then `(4,6)`. -/

/-- Half of segment `s_k` as a vector: `(k, 0)` for odd `k`, `(0, k)` for even `k`. -/
def halfStep (k : ℕ) : ℤ × ℤ := if k % 2 = 0 then (0, (k : ℤ)) else ((k : ℤ), 0)

/-- Midpoints: `p_0 = (0,0)` and `p_{k+1} = p_k + halfStep (k+1)`. -/
def midPt : ℕ → ℤ × ℤ
  | 0 => (0, 0)
  | k + 1 => midPt k + halfStep (k + 1)

/-- Endpoints: `a_0 = (0,0)` and `a_{k+1} = p_k + 2 * halfStep (k+1)`. -/
def endPt : ℕ → ℤ × ℤ
  | 0 => (0, 0)
  | k + 1 => midPt k + (2 * (halfStep (k + 1)).1, 2 * (halfStep (k + 1)).2)

/-- An integer point viewed as a point of the plane. -/
def toPt (v : ℤ × ℤ) : Pt := ((v.1 : ℝ), (v.2 : ℝ))

/-- The ranking `F_n` followed by `x_n`: `a_0 ≻ a_1 ≻ … ≻ a_n ≻ p_n`, best first. -/
def zigzagList (n : ℕ) : List Pt :=
  (List.range (n + 1)).map (fun k => toPt (endPt k)) ++ [toPt (midPt n)]

/-- The criticality claim for every `n ≥ 2`. The list has no repeated entries.
It is in R(H-QC) and in R(V-QC). It is NOT in R(H-QC and V-QC). Deleting any single entry
(position `k`) leaves a ranking in R(H-QC and V-QC). (The list has length `n + 2`, so this
implies `hvqc_stmt`. At `n = 1` the list is `(0,0),(2,0),(1,0)`, which is not even in
R(H-QC). That is why `n ≥ 2` is required.) -/
def zigzag_stmt : Prop :=
  ∀ n : ℕ, 2 ≤ n →
    (zigzagList n).Nodup ∧
    InR HQC (zigzagList n) ∧
    InR VQC (zigzagList n) ∧
    ¬ InR HVQC (zigzagList n) ∧
    ∀ k < (zigzagList n).length, InR HVQC ((zigzagList n).eraseIdx k)

end Q1
