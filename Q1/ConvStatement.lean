/-
# Q1 via Conv: bridge statements

Definitions and headline `Prop`s only: no theorems, no proof holes, no axioms. Imports only
`Conv.Statement` and `Q1.Statement`.

Plain-language summary of `conv_target_stmt` (end of file). On the plane, let `CH` (`CV`)
be the horizontally (vertically) convex sets. Then `CH` and `CV` are convexities, H-QC,
V-QC and H-QC-and-V-QC are exactly the `UCC` conditions for `CH`, `CV` and both, `CH` and
`CV` have Carathéodory bound exactly 2, and orthogonal convexity `CH ∩ CV` has no finite
Carathéodory bound.
-/
import Conv.Statement
import Q1.Statement

namespace Q1

/-- Horizontal convexity: sets meeting every horizontal line in an interval. -/
def CH : Set (Set Pt) := {U | ∀ y z w : Pt, y ∈ U → z ∈ U → y.2 = z.2 → w.2 = y.2 →
  w.1 ∈ Set.uIcc y.1 z.1 → w ∈ U}

/-- Vertical convexity: sets meeting every vertical line in an interval. -/
def CV : Set (Set Pt) := {U | ∀ y z w : Pt, y ∈ U → z ∈ U → y.1 = z.1 → w.1 = y.1 →
  w.2 ∈ Set.uIcc y.2 z.2 → w ∈ U}

/-- `CH` and `CV` are convexities. -/
def convexity_stmt : Prop := Conv.IsConvexity CH ∧ Conv.IsConvexity CV

/-- H-QC, V-QC and H-QC-and-V-QC are the upper-contour-convexity conditions for `CH`, `CV`
and both. -/
def bridge_stmt : Prop := (∀ R : Rel, HQC R ↔ Conv.UCC CH R) ∧ (∀ R : Rel, VQC R ↔ Conv.UCC CV R) ∧
  (∀ R : Rel, HVQC R ↔ (Conv.UCC CH R ∧ Conv.UCC CV R))

/-- `CH` has Carathéodory bound 2 and not 1. -/
def cara_H_stmt : Prop := Conv.CaraBound CH 2 ∧ ¬ Conv.CaraBound CH 1

/-- `CV` has Carathéodory bound 2 and not 1. -/
def cara_V_stmt : Prop := Conv.CaraBound CV 2 ∧ ¬ Conv.CaraBound CV 1

/-- Orthogonal convexity (the join) has no finite Carathéodory bound. -/
def cara_HV_stmt : Prop := ∀ c : ℕ, ¬ Conv.CaraBound (CH ∩ CV) c

/-- The whole bridge claim. -/
def conv_target_stmt : Prop :=
  convexity_stmt ∧ bridge_stmt ∧ cara_H_stmt ∧ cara_V_stmt ∧ cara_HV_stmt

end Q1
