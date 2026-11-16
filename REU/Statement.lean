/-
# Theorem 1: statement (audit file)

This file contains ONLY definitions and the headline statements, written as `Prop`s
(`def …_stmt : Prop`). Nothing is assumed here: there are no theorems and no proof holes,
no assumed axioms. Later files prove `thm1_stmt`, `thm1_reu_stmt`, `bridge_stmt`.

Coordinates (Marschak–Machina): a lottery over prizes worst < middle < best is the point
`(u, v)` with `u = prob(worst)`, `v = prob(best)`. Vertices: worst `(1,0)`,
middle `(0,0)`, best `(0,1)`.
-/
import Mathlib

open MeasureTheory

namespace REU

/-! ## 1. Triangle, mixtures, FOSD -/

/-- A point `(u, v)` of the plane; `u = prob(worst)`, `v = prob(best)`. -/
abbrev Pt := ℝ × ℝ

/-- The Marschak triangle `T = {(u,v) : u ≥ 0, v ≥ 0, u + v ≤ 1}` (closed). -/
def Tri : Set Pt := {p | 0 ≤ p.1 ∧ 0 ≤ p.2 ∧ p.1 + p.2 ≤ 1}

/-- The mixture `t q + (1 - t) r` (coordinatewise). -/
def mix (t : ℝ) (q r : Pt) : Pt := t • q + (1 - t) • r

/-- `q` weakly first-order stochastically dominates `r`:
`u_q ≤ u_r` (no more weight on worst) and `v_r ≤ v_q` (at least as much on best). -/
def FOSD (q r : Pt) : Prop := q.1 ≤ r.1 ∧ r.2 ≤ q.2

/-- Strict FOSD: weak dominance and `q ≠ r`. -/
def StrictFOSD (q r : Pt) : Prop := FOSD q r ∧ q ≠ r

/-- `a` is strictly north-east of `b`: more weight on worst AND more weight on best
(`a` is the riskier end of an FOSD-incomparable pair). -/
def NE (a b : Pt) : Prop := b.1 < a.1 ∧ b.2 < a.2

/-- Slope of the segment from `b` to `a` (only used when `NE a b`, so the denominator
is positive). -/
noncomputable def slope (a b : Pt) : ℝ := (a.2 - b.2) / (a.1 - b.1)

/-! ## 2. Preferences, from the axioms -/

/-- A binary relation on lotteries; `R q r` reads "q is weakly preferred to r". -/
abbrev Rel := Pt → Pt → Prop

/-- Strict part: `q ≻ r`. -/
def SPref (R : Rel) (q r : Pt) : Prop := R q r ∧ ¬ R r q

/-- Indifference: `q ∼ r`. -/
def Indiff (R : Rel) (q r : Pt) : Prop := R q r ∧ R r q

/-- A betweenness preference on the triangle. Every axiom quantifies only over points of
`Tri`; the relation is unconstrained off `Tri`.
Continuity: upper and lower contour sets are closed in the subspace topology of `Tri`. -/
structure IsBetweennessPref (R : Rel) : Prop where
  complete : ∀ q ∈ Tri, ∀ r ∈ Tri, R q r ∨ R r q
  trans : ∀ q ∈ Tri, ∀ r ∈ Tri, ∀ s ∈ Tri, R q r → R r s → R q s
  /-- `{q ∈ T : q ≽ r}` is closed in `T`. -/
  closed_upper : ∀ r ∈ Tri, IsClosed {q : Tri | R q.1 r}
  /-- `{q ∈ T : r ≽ q}` is closed in `T`. -/
  closed_lower : ∀ r ∈ Tri, IsClosed {q : Tri | R r q.1}
  /-- Strict FOSD monotonicity. -/
  strictMono : ∀ q ∈ Tri, ∀ r ∈ Tri, StrictFOSD q r → SPref R q r
  /-- Betweenness, strict part: `q ≻ r ⇒ q ≻ tq + (1-t)r ≻ r` for `t ∈ (0,1)`. -/
  btw_strict : ∀ q ∈ Tri, ∀ r ∈ Tri, ∀ t ∈ Set.Ioo (0 : ℝ) 1,
    SPref R q r → SPref R q (mix t q r) ∧ SPref R (mix t q r) r
  /-- Betweenness, indifference part: `q ∼ r ⇒ tq + (1-t)r ∼ q` for `t ∈ (0,1)`. -/
  btw_indiff : ∀ q ∈ Tri, ∀ r ∈ Tri, ∀ t ∈ Set.Ioo (0 : ℝ) 1,
    Indiff R q r → Indiff R (mix t q r) q

/-- Expected-utility preference: a betweenness preference that also satisfies
independence: `q ≽ r ⇔ tq + (1-t)s ≽ tr + (1-t)s` for `t ∈ (0,1]`, all `q r s ∈ T`. -/
def IsEUPref (R : Rel) : Prop :=
  IsBetweennessPref R ∧
    ∀ q ∈ Tri, ∀ r ∈ Tri, ∀ s ∈ Tri, ∀ t ∈ Set.Ioc (0 : ℝ) 1,
      (R q r ↔ R (mix t q s) (mix t r s))

/-- `R` is strict on `X`: no two distinct elements of `X` are indifferent. -/
def StrictOn (R : Rel) (X : Finset Pt) : Prop :=
  ∀ x ∈ X, ∀ y ∈ X, x ≠ y → ¬ (R x y ∧ R y x)

/-- `x` is the (unique) `R`-best element of menu `A`: `x ∈ A` and `x ≻ y` for every other
`y ∈ A`. -/
def IsMaxIn (R : Rel) (x : Pt) (A : Finset Pt) : Prop :=
  x ∈ A ∧ ∀ y ∈ A, y ≠ x → SPref R x y

/-! ## 3. Random choice rules and mixtures -/

/-- A random choice rule on the menus of `X` (menus = nonempty `A ⊆ X`).
`p x A` is the probability that `x` is chosen from `A`. Values on non-menus are junk;
only `A ⊆ X` is constrained. -/
structure RandomChoiceRule (X : Finset Pt) where
  p : Pt → Finset Pt → ℝ
  nonneg : ∀ A ⊆ X, ∀ x, 0 ≤ p x A
  zero_of_not_mem : ∀ A ⊆ X, ∀ x, x ∉ A → p x A = 0
  sum_one : ∀ A ⊆ X, A.Nonempty → ∑ x ∈ A, p x A = 1

open Classical in
/-- `ρ` is a finite mixture of preferences from class `C`, each strict on `X`:
weights `w i ≥ 0` summing to 1 with `ρ(x, A) = Σ_i w_i · [x is the R_i-max of A]` on every
menu `A ⊆ X` and every `x ∈ A`. -/
def IsMixture (C : Rel → Prop) (X : Finset Pt) (ρ : RandomChoiceRule X) : Prop :=
  ∃ (n : ℕ) (R : Fin n → Rel) (w : Fin n → ℝ),
    (∀ i, C (R i) ∧ StrictOn (R i) X) ∧
    (∀ i, 0 ≤ w i) ∧
    ∑ i, w i = 1 ∧
    ∀ A ⊆ X, A.Nonempty → ∀ x ∈ A,
      ρ.p x A = ∑ i, if IsMaxIn (R i) x A then w i else 0

/-! ## 4. The conditions -/

/-- `y` lies on the line through `a` and `b` (`a ≠ b`): zero cross product. -/
def OnLine (a b y : Pt) : Prop :=
  (y.1 - a.1) * (b.2 - a.2) - (y.2 - a.2) * (b.1 - a.1) = 0

/-- The lines `L(ab)` and `L(cd)` have a common point in the CLOSED triangle. -/
def linesMeetInTri (a b c d : Pt) : Prop :=
  ∃ y ∈ Tri, OnLine a b y ∧ OnLine c d y

/-- `L(ab) = L(cd)`: both `c` and `d` lie on the line through `a`, `b`
(for chords, `a ≠ b` and `c ≠ d`, so this is equality of lines). -/
def collinear4 (a b c d : Pt) : Prop :=
  OnLine a b c ∧ OnLine a b d

/-- Chord value `f(ab) = ρ(a, {a, b})`: probability the NE (riskier) end is chosen. -/
noncomputable def fChord {X : Finset Pt} (ρ : RandomChoiceRule X) (a b : Pt) : ℝ := ρ.p a {a, b}

/-- `(a, b)` is a chord of `X`: `a, b ∈ X` and `a` is strictly NE of `b`. -/
def IsChord (X : Finset Pt) (a b : Pt) : Prop := a ∈ X ∧ b ∈ X ∧ NE a b

/-- CD-dom: a strictly FOSD-dominated element is never chosen from the pair. -/
def CDDom (X : Finset Pt) (ρ : RandomChoiceRule X) : Prop :=
  ∀ q ∈ X, ∀ r ∈ X, StrictFOSD q r → ρ.p r {q, r} = 0

/-- Chord Dominance (CD-dom, CD-cross, CD-col). -/
def ChordDominance (X : Finset Pt) (ρ : RandomChoiceRule X) : Prop :=
  CDDom X ρ ∧
  (∀ a b c d, IsChord X a b → IsChord X c d →
      linesMeetInTri a b c d → slope c d < slope a b → fChord ρ c d ≤ fChord ρ a b) ∧
  (∀ a b c d, IsChord X a b → IsChord X c d →
      collinear4 a b c d → fChord ρ a b = fChord ρ c d)

/-- Extended Chord Dominance (REU clause): CD-dom, and for ALL pairs of chords, steeper
chord has weakly larger `f`, equal slopes give equal `f`. -/
def ChordDominanceAll (X : Finset Pt) (ρ : RandomChoiceRule X) : Prop :=
  CDDom X ρ ∧
  (∀ a b c d, IsChord X a b → IsChord X c d →
      slope c d < slope a b → fChord ρ c d ≤ fChord ρ a b) ∧
  (∀ a b c d, IsChord X a b → IsChord X c d →
      slope a b = slope c d → fChord ρ a b = fChord ρ c d)

open Classical in
/-- `A_NE(x)`: elements of `A` other than `x` that are strictly NE of `x` OR strictly
FOSD-dominate `x`. -/
noncomputable def ANE (A : Finset Pt) (x : Pt) : Finset Pt :=
  A.filter (fun a => a ≠ x ∧ (NE a x ∨ StrictFOSD a x))

open Classical in
/-- `A_SW(x) = A \ ({x} ∪ A_NE(x))`: everything else (strictly SW of `x`, or strictly
FOSD-dominated by `x`). -/
noncomputable def ASW (A : Finset Pt) (x : Pt) : Finset Pt :=
  A.filter (fun a => a ≠ x ∧ ¬ (NE a x ∨ StrictFOSD a x))

/-- Minimum of `g` over a finite set, with the convention `min ∅ = 1`. -/
noncomputable def minOr1 (S : Finset Pt) (g : Pt → ℝ) : ℝ :=
  if h : S.Nonempty then S.inf' h g else 1

/-- Bracketing: for every menu `A ⊆ X` and `x ∈ A`,
`ρ(x, A) = max(0, min_{b ∈ A_SW(x)} ρ(x,{x,b}) + min_{a ∈ A_NE(x)} ρ(x,{x,a}) − 1)`. -/
def Bracketing (X : Finset Pt) (ρ : RandomChoiceRule X) : Prop :=
  ∀ A ⊆ X, ∀ x ∈ A,
    ρ.p x A = max 0 (minOr1 (ASW A x) (fun b => ρ.p x {x, b})
                    + minOr1 (ANE A x) (fun a => ρ.p x {x, a}) - 1)

/-! ## 5. Headline statements -/

/-- Theorem 1: mixture of betweenness preferences strict on `X` ⇔ CD ∧ B. -/
def thm1_stmt : Prop :=
  ∀ X : Finset Pt, (↑X : Set Pt) ⊆ Tri → ∀ ρ : RandomChoiceRule X,
    IsMixture IsBetweennessPref X ρ ↔ ChordDominance X ρ ∧ Bracketing X ρ

/-- Theorem 1, REU clause: mixture of EU preferences strict on `X` ⇔ CD-all ∧ B. -/
def thm1_reu_stmt : Prop :=
  ∀ X : Finset Pt, (↑X : Set Pt) ⊆ Tri → ∀ ρ : RandomChoiceRule X,
    IsMixture IsEUPref X ρ ↔ ChordDominanceAll X ρ ∧ Bracketing X ρ

/-- Bridge lemma, for any class `C` of relations:
(a) a measure-theoretic random preference (any probability space `Ω`, each `R ω ∈ C` strict
on `X`, measurable "x is the R ω-max of A" events) inducing `ρ` makes `ρ` a finite mixture;
(b) conversely, every finite mixture is induced by such a random preference. -/
def bridge_stmt.{u} : Prop :=
  ∀ (C : Rel → Prop) (X : Finset Pt) (ρ : RandomChoiceRule X),
    (∀ (Ω : Type u) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (R : Ω → Rel),
        (∀ ω, C (R ω) ∧ StrictOn (R ω) X) →
        (∀ A ⊆ X, ∀ x ∈ A, MeasurableSet {ω | IsMaxIn (R ω) x A}) →
        (∀ A ⊆ X, A.Nonempty → ∀ x ∈ A, ρ.p x A = (μ {ω | IsMaxIn (R ω) x A}).toReal) →
        IsMixture C X ρ) ∧
    (IsMixture C X ρ →
      ∃ (Ω : Type u) (_ : MeasurableSpace Ω) (μ : Measure Ω) (R : Ω → Rel),
        IsProbabilityMeasure μ ∧
        (∀ ω, C (R ω) ∧ StrictOn (R ω) X) ∧
        (∀ A ⊆ X, ∀ x ∈ A, MeasurableSet {ω | IsMaxIn (R ω) x A}) ∧
        (∀ A ⊆ X, A.Nonempty → ∀ x ∈ A, ρ.p x A = (μ {ω | IsMaxIn (R ω) x A}).toReal))

end REU
