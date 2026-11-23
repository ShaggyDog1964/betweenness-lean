/-
`collinear_menu`: on a collinear `X`, menu probabilities equal those of the
binary menu of the two line-extreme elements.
-/
import Q3L.Statement
import Q3L.LineRanking

namespace Q3L

open K4 (Lot Simplex IsBetweennessPref)

/-- On a collinear `X`, for a menu `A` with line-minimum `a` and line-maximum `b` (`a ≠ b`),
every mixture of betweenness preferences has `ρ(x, A) = ρ(x, {a, b})`.
Sketch. Unpack `hρ` (`n, R, w, hform`). `φ` is injective on `X` (`hrep`), so `a` is the unique
`φ`-minimum of `A`, `b` the unique maximum, and `φ a < φ b`.
Claim: for every `i` and every `x`, `IsMaxIn (R i) x A ↔ IsMaxIn (R i) x {a, b}`. By
`line_ranking` (for `R i`, strict on `X`), either `SPref (R i) p q ↔ φ p < φ q` on `X`; then
both sides say `x = a` (on `A`: `x` beats all others iff `x` has the strictly smallest `φ`; on
`{a, b}` likewise). Or `SPref (R i) p q ↔ φ q < φ p`; then both sides say `x = b`.
If `x ∈ {a, b}`: `hform` on `A` and on `{a, b}` (`⊆ X`, nonempty) plus the claim
(`Finset.sum_congr`). If `x ∉ {a, b}`: `ρ.p x {a, b} = 0` (`zero_of_not_mem`) and, by the claim,
no `IsMaxIn (R i) x A` holds (`IsMaxIn _ x {a,b}` needs `x ∈ {a,b}`), so `hform` gives `0`. -/
private lemma cm_isMax_iff {K : ℕ} {X : Finset (Lot K)} {R : K4.Rel K} {ψ : Lot K → ℝ}
    (hinj : ∀ x ∈ X, ∀ y ∈ X, ψ x = ψ y → x = y)
    (hR : ∀ x ∈ X, ∀ y ∈ X, (K4.SPref R x y ↔ ψ x < ψ y))
    {S : Finset (Lot K)} (hS : S ⊆ X) {a : Lot K} (ha : a ∈ S) (hmin : ∀ y ∈ S, ψ a ≤ ψ y)
    (x : Lot K) : IsMaxIn R x S ↔ x = a := by
  constructor
  · rintro ⟨hxS, hx⟩
    by_contra hxa
    have h := (hR x (hS hxS) a (hS ha)).1 (hx a ha (Ne.symm hxa))
    exact absurd (hmin x hxS) (not_le.2 h)
  · rintro rfl
    refine ⟨ha, fun y hy hyx => (hR x (hS ha) y (hS hy)).2 ?_⟩
    exact lt_of_le_of_ne (hmin y hy) (fun h => hyx (hinj _ (hS hy) _ (hS ha) h.symm))

theorem collinear_menu {K : ℕ} {X : Finset (Lot K)} (hXs : (↑X : Set (Lot K)) ⊆ Simplex K)
    {x0 d : Lot K} {φ : Lot K → ℝ} (hrep : ∀ x ∈ X, x = x0 + φ x • d)
    (ρ : RandomChoiceRule X) (hρ : IsMixture IsBetweennessPref X ρ)
    {A : Finset (Lot K)} (hA : A ⊆ X) {a b : Lot K} (ha : a ∈ A) (hb : b ∈ A) (hab : a ≠ b)
    (hmin : ∀ y ∈ A, φ a ≤ φ y) (hmax : ∀ y ∈ A, φ y ≤ φ b) {x : Lot K} (hx : x ∈ A) :
    ρ.p x A = ρ.p x {a, b} := by
  classical
  obtain ⟨n, R, w, hRC, _, _, hform⟩ := hρ
  have hinj : ∀ x ∈ X, ∀ y ∈ X, φ x = φ y → x = y := by
    intro x hx y hy h
    rw [hrep x hx, hrep y hy, h]
  have hninj : ∀ x ∈ X, ∀ y ∈ X, (fun z => -φ z) x = (fun z => -φ z) y → x = y :=
    fun x hx y hy h => hinj x hx y hy (neg_inj.1 h)
  have hab2 : ({a, b} : Finset (Lot K)) ⊆ X := by
    intro z hz
    rcases Finset.mem_insert.1 hz with rfl | hz
    · exact hA ha
    · rw [Finset.mem_singleton.1 hz]; exact hA hb
  have hab1 : ({a, b} : Finset (Lot K)) ⊆ A := by
    intro z hz
    rcases Finset.mem_insert.1 hz with rfl | hz
    · exact ha
    · rw [Finset.mem_singleton.1 hz]; exact hb
  have claim : ∀ i z, IsMaxIn (R i) z A ↔ IsMaxIn (R i) z {a, b} := by
    intro i z
    rcases line_ranking hXs hrep (hRC i).1 (hRC i).2 with h | h
    · rw [cm_isMax_iff hinj h hA ha hmin,
        cm_isMax_iff hinj h hab2 (Finset.mem_insert_self a {b})
          (fun y hy => hmin y (hab1 hy))]
    · have h' : ∀ x ∈ X, ∀ y ∈ X,
          (K4.SPref (R i) x y ↔ (fun z => -φ z) x < (fun z => -φ z) y) :=
        fun x hx y hy => by rw [h x hx y hy]; exact neg_lt_neg_iff.symm
      rw [cm_isMax_iff hninj h' hA hb (fun y hy => neg_le_neg (hmax y hy)),
        cm_isMax_iff hninj h' hab2 (Finset.mem_insert_of_mem (Finset.mem_singleton_self b))
          (fun y hy => neg_le_neg (hmax y (hab1 hy)))]
  rw [hform A hA ⟨x, hx⟩ x hx]
  by_cases hxab : x ∈ ({a, b} : Finset (Lot K))
  · rw [hform {a, b} hab2 ⟨a, Finset.mem_insert_self a {b}⟩ x hxab]
    exact Finset.sum_congr rfl fun i _ => by simp only [claim i x]
  · rw [ρ.zero_of_not_mem _ hab2 x hxab]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [if_neg]
    rw [claim i x]
    exact fun h => hxab h.1

end Q3L
