/-
# Conv: statement of the Carathéodory criterion

Abstract convexity and locality of rankings. This file contains ONLY definitions and
headline `Prop`s. There are no theorems, no proof holes and no assumed axioms. It imports
only Mathlib, so it can be audited on its own.

Plain-language summary of `target_stmt` (end of file). Let `C` be a convexity on a type
`α`, that is, a family of sets closed under arbitrary intersections. A preference is
`C`-quasi-concave (`UCC`) when every upper contour set is `C`-convex.
  (a) A ranking (list without repeats) is in R(UCC C) iff it has no obstruction: no entry
      other than the first lies in the `C`-hull of the entries ranked above it (`char_stmt`).
  (b) For `n ≥ 2`, R(UCC C) is `n`-local iff `C` has Carathéodory number at most `n - 1`
      (`locality_stmt`). Hence R(UCC C) is local for some `n` iff `C` has a finite
      Carathéodory bound (`local_iff_finite_stmt`).
  (c) The intersection of two convexities is a convexity, its quasi-concave preferences are
      exactly those quasi-concave for both, and its hull is the join of the hull operators
      (`join_stmt`). The same locality criterion holds for the conjunction of two
      properties, with the bound taken for the intersection (`conj_local_stmt`).

Preferences are weak orders (complete and transitive) on ALL of `α`. Nothing else is
required.

In the working paper, (a) and (b) are parts (1) and (2) and the last sentence of part (3) of
Theorem 4, and (c) is Proposition 13 without its statement that the hull operator of `C₁ ∩ C₂`
is the least of the operators described there.
-/
import Mathlib

namespace Conv

universe u

variable {α : Type u}

/-- A binary relation on `α`. `R x y` reads "x is weakly preferred to y". -/
abbrev Rel (α : Type u) := α → α → Prop

/-- Strict part: `x ≻ y` means `x ≽ y` and not `y ≽ x`. -/
def SPref (R : Rel α) (x y : α) : Prop := R x y ∧ ¬ R y x

/-- An admissible preference: a weak order, that is, complete and transitive. -/
structure IsWeakOrder (R : Rel α) : Prop where
  /-- Completeness: any two alternatives are comparable. -/
  complete : ∀ x y : α, R x y ∨ R y x
  /-- Transitivity. -/
  trans : ∀ x y z : α, R x y → R y z → R x z

/-- The list `L` (best first) is in R(P): some weak order with property `P` ranks every
earlier entry STRICTLY above every later entry. -/
def InR (P : Rel α → Prop) (L : List α) : Prop :=
  ∃ R : Rel α, IsWeakOrder R ∧ P R ∧ L.Pairwise (SPref R)

/-- `L` passes every test of size at most `n`: each sub-ranking of `L` with at most `n`
entries is in R(P). -/
def LocallyInR (P : Rel α → Prop) (n : ℕ) (L : List α) : Prop :=
  ∀ L' : List α, L'.Sublist L → L'.length ≤ n → InR P L'

/-- R(P) is `n`-local: every ranking without repeats whose sub-rankings with at most `n`
entries are all in R(P) is itself in R(P). -/
def IsLocal (P : Rel α → Prop) (n : ℕ) : Prop :=
  ∀ L : List α, L.Nodup → LocallyInR P n L → InR P L

/-- A convexity: closed under intersections of arbitrary subfamilies (the empty one gives univ). -/
def IsConvexity (C : Set (Set α)) : Prop := ∀ S : Set (Set α), S ⊆ C → ⋂₀ S ∈ C

/-- The `C`-hull of `S`: the intersection of all members of `C` containing `S`. -/
def hull (C : Set (Set α)) (S : Set α) : Set α := ⋂₀ {U | U ∈ C ∧ S ⊆ U}

/-- Every upper contour set `{y | y ≽ x}` is C-convex. -/
def UCC (C : Set (Set α)) (R : Rel α) : Prop := ∀ x : α, {y | R y x} ∈ C

/-- Carathéodory bound `c`: every point of the hull of a finite set `A` lies in the hull of
some subset of `A` with at most `c` elements. -/
def CaraBound (C : Set (Set α)) (c : ℕ) : Prop :=
  ∀ A : Finset α, ∀ p ∈ hull C (↑A : Set α), ∃ B ⊆ A, B.card ≤ c ∧ p ∈ hull C (↑B : Set α)

/-- No obstruction in `L`: no entry after the first lies in the `C`-hull of the entries
ranked above it. -/
def NoObstruction (C : Set (Set α)) (L : List α) : Prop :=
  ∀ (j : ℕ) (hj : j < L.length), 0 < j → L[j] ∉ hull C {x | x ∈ L.take j}

/-- Characterisation: a list is in R(UCC C) iff it has no obstruction. -/
def char_stmt : Prop := ∀ (α : Type u) (C : Set (Set α)), IsConvexity C →
  ∀ L : List α, InR (UCC C) L ↔ NoObstruction C L

/-- Locality number: for `n ≥ 2`, R(UCC C) is `n`-local iff the Carathéodory bound is `n - 1`. -/
def locality_stmt : Prop := ∀ (α : Type u) (C : Set (Set α)), IsConvexity C →
  ∀ n : ℕ, 2 ≤ n → (IsLocal (UCC C) n ↔ CaraBound C (n - 1))

/-- R(UCC C) is local for some `n` iff some finite Carathéodory bound exists. -/
def local_iff_finite_stmt : Prop := ∀ (α : Type u) (C : Set (Set α)), IsConvexity C →
  ((∃ n, IsLocal (UCC C) n) ↔ ∃ c, CaraBound C c)

/-- Joins: the intersection of two convexities is a convexity, its quasi-concave preferences
are those quasi-concave for both, and its hull is the closure under both hull operators. -/
def join_stmt : Prop := ∀ (α : Type u) (C₁ C₂ : Set (Set α)), IsConvexity C₁ → IsConvexity C₂ →
  IsConvexity (C₁ ∩ C₂) ∧ (∀ R : Rel α, (UCC C₁ R ∧ UCC C₂ R) ↔ UCC (C₁ ∩ C₂) R) ∧
  ∀ S : Set α, hull (C₁ ∩ C₂) S = ⋂₀ {T | S ⊆ T ∧ hull C₁ T = T ∧ hull C₂ T = T}

/-- The locality criterion for the conjunction of two quasi-concavity properties. -/
def conj_local_stmt : Prop := ∀ (α : Type u) (C₁ C₂ : Set (Set α)), IsConvexity C₁ → IsConvexity C₂ →
  ∀ n : ℕ, 2 ≤ n → (IsLocal (fun R => UCC C₁ R ∧ UCC C₂ R) n ↔ CaraBound (C₁ ∩ C₂) (n - 1))

/-- The whole claim of the Conv library. -/
def target_stmt : Prop :=
  char_stmt.{u} ∧ locality_stmt.{u} ∧ local_iff_finite_stmt.{u} ∧ join_stmt.{u} ∧ conj_local_stmt.{u}

end Conv
