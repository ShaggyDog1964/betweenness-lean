/-
# Shared definitions for the Q1 development (no theorems, no proof holes)

Plain definitions used by the lemma files `Q1/*.lean`. The statement is
`Q1/Statement.lean`.

* `HConv`, `VConv`: a set meets every horizontal (vertical) line in an interval.
* `chainRel U`: the weak order induced by a monotone chain of sets `U 0 ⊆ U 1 ⊆ …`:
  `x ≽ y` iff `x` lies in every `U k` that contains `y`. (Discontinuous step preference.)
* `hHull S`: the horizontal hull of a finite list of points.
* `orth t`: a closed lower-left quadrant containing `a_0, …, a_{t-1}` of the zigzag
  family (`orth 0 = ∅`).
* `critU i t`: the chain used to show that deleting position `i` of `zigzagList n`
  leaves a ranking in R(HVQC).
-/
import Q1.Statement

namespace Q1

/-- `U` meets every horizontal line in an interval. -/
def HConv (U : Set Pt) : Prop :=
  ∀ y z w : Pt, y ∈ U → z ∈ U → y.2 = z.2 → w.2 = y.2 → w.1 ∈ Set.uIcc y.1 z.1 → w ∈ U

/-- `U` meets every vertical line in an interval. -/
def VConv (U : Set Pt) : Prop :=
  ∀ y z w : Pt, y ∈ U → z ∈ U → y.1 = z.1 → w.1 = y.1 → w.2 ∈ Set.uIcc y.2 z.2 → w ∈ U

/-- The step preference of a chain of sets: `x ≽ y` iff every `U k` containing `y`
contains `x`. -/
def chainRel (U : ℕ → Set Pt) : Rel := fun x y => ∀ k, y ∈ U k → x ∈ U k

/-- Horizontal hull of a finite list: points on a horizontal segment joining two
(possibly equal) entries of `S` that lie on a common horizontal line. -/
def hHull (S : List Pt) : Set Pt :=
  {w | ∃ y ∈ S, ∃ z ∈ S, y.2 = z.2 ∧ w.2 = y.2 ∧ w.1 ∈ Set.uIcc y.1 z.1}

/-- `orth 0 = ∅`; `orth (m+1)` is the quadrant
`{x | x.1 ≤ (midPt m).1 + m ∧ x.2 ≤ (midPt m).2 + m}`. It contains `a_0, …, a_m`. -/
def orth : ℕ → Set Pt
  | 0 => ∅
  | m + 1 => {x | x.1 ≤ ((midPt m).1 : ℝ) + m ∧ x.2 ≤ ((midPt m).2 : ℝ) + m}

/-- The chain for the deletion of position `i`: the quadrant `orth (min t i)` together with
the later endpoints `a_j`, `i < j ≤ t`. -/
def critU (i t : ℕ) : Set Pt :=
  orth (min t i) ∪ {x | ∃ j, i < j ∧ j ≤ t ∧ x = toPt (endPt j)}

end Q1
