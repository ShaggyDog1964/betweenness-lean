/-
`line_ranking`: a betweenness preference strict on a collinear `X` ranks it
monotonically along the line (proof of Theorem 36(3), first part).
-/
import Q3L.Statement
import Q3L.MixParam
import K4.SprefTrans

namespace Q3L

open K4 (Lot Simplex Rel SPref IsBetweennessPref)

/-- A betweenness preference strict on `X ⊆` a line ranks `X` either by increasing or by
decreasing line parameter.
Sketch. `φ` is injective on `X` (`hrep`). Betweenness on triples (T): for `x, y, z ∈ X` with
`φ x < φ y < φ z`, `mix_of_param` gives `y = mix t x z`; if `SPref R x z` then `btw_strict`
gives `SPref R x y ∧ SPref R y z`; if `SPref R z x` then (using `mix t x z = mix (1-t) z x`)
`SPref R z y ∧ SPref R y x`.
If `X` has at most one point both alternatives hold (`SPref R x x` is false). Otherwise let
`m, M ∈ X` minimize / maximize `φ` (`Finset.exists_min_image`, `exists_max_image`), `m ≠ M`.
Strictness and completeness give `SPref R m M` or `SPref R M m`. Case `SPref R m M`: show the
first alternative. (→) if `SPref R x y` and not `φ x < φ y`, then `φ y < φ x` (`x ≠ y` since
`SPref R x x` fails; injectivity) and the (←) direction gives `SPref R y x`, contradicting
asymmetry. (←) let `φ x < φ y`. If `x = m`: `y = M` or `φ m < φ y < φ M`, and (T) on
`(m, y, M)` gives `SPref R m y`. If `x ≠ m`: `φ m < φ x`, so (T) on `(m, x, M)` gives
`SPref R x M` (note `x ≠ M` as `φ x < φ y ≤ φ M`); if `y = M` done, else (T) on `(x, y, M)`
with `SPref R x M` gives `SPref R x y`. Case `SPref R M m`: symmetric (second alternative). -/
private lemma lr_triple {K : ℕ} {X : Finset (Lot K)} (hXs : (↑X : Set (Lot K)) ⊆ Simplex K)
    {x0 d : Lot K} {φ : Lot K → ℝ} (hrep : ∀ x ∈ X, x = x0 + φ x • d)
    {R : Rel K} (hR : IsBetweennessPref R) {x y z : Lot K} (hx : x ∈ X) (hy : y ∈ X)
    (hz : z ∈ X) (hxy : φ x < φ y) (hyz : φ y < φ z) (hxz : SPref R x z) :
    SPref R x y ∧ SPref R y z := by
  obtain ⟨t, ht, rfl⟩ := mix_of_param (hrep x hx) (hrep _ hy) (hrep z hz) hxy hyz
  exact hR.btw_strict x (hXs hx) z (hXs hz) t ht hxz

private lemma lr_key {K : ℕ} {X : Finset (Lot K)} (hXs : (↑X : Set (Lot K)) ⊆ Simplex K)
    {x0 d : Lot K} {φ : Lot K → ℝ} (hrep : ∀ x ∈ X, x = x0 + φ x • d)
    {R : Rel K} (hR : IsBetweennessPref R) {m M : Lot K} (hm : m ∈ X) (hM : M ∈ X)
    (hmin : ∀ x ∈ X, φ m ≤ φ x) (hmax : ∀ x ∈ X, φ x ≤ φ M) (hmM : SPref R m M) :
    ∀ x ∈ X, ∀ y ∈ X, (SPref R x y ↔ φ x < φ y) := by
  have inj : ∀ x ∈ X, ∀ y ∈ X, φ x = φ y → x = y := by
    intro x hx y hy h
    rw [hrep x hx, hrep y hy, h]
  have hA : ∀ x ∈ X, x ≠ M → SPref R x M := by
    intro x hx hxM
    by_cases hxm : x = m
    · subst hxm; exact hmM
    have h1 : φ m < φ x := lt_of_le_of_ne (hmin x hx) (fun h => hxm (inj _ hx _ hm h.symm))
    have h2 : φ x < φ M := lt_of_le_of_ne (hmax x hx) (fun h => hxM (inj _ hx _ hM h))
    exact (lr_triple hXs hrep hR hm hx hM h1 h2 hmM).2
  have back : ∀ x ∈ X, ∀ y ∈ X, φ x < φ y → SPref R x y := by
    intro x hx y hy hxy
    have hxM : x ≠ M := by
      rintro rfl; exact absurd (hmax y hy) (not_le.2 hxy)
    have hxM' := hA x hx hxM
    by_cases hyM : y = M
    · subst hyM; exact hxM'
    have h2 : φ y < φ M := lt_of_le_of_ne (hmax y hy) (fun h => hyM (inj _ hy _ hM h))
    exact (lr_triple hXs hrep hR hx hy hM hxy h2 hxM').1
  intro x hx y hy
  refine ⟨fun hs => ?_, back x hx y hy⟩
  rcases lt_trichotomy (φ x) (φ y) with h | h | h
  · exact h
  · have := inj _ hx _ hy h
    subst this
    exact absurd hs.1 hs.2
  · exact absurd hs.1 (back y hy x hx h).2

theorem line_ranking {K : ℕ} {X : Finset (Lot K)} (hXs : (↑X : Set (Lot K)) ⊆ Simplex K)
    {x0 d : Lot K} {φ : Lot K → ℝ} (hrep : ∀ x ∈ X, x = x0 + φ x • d)
    {R : Rel K} (hR : IsBetweennessPref R) (hst : StrictOn R X) :
    (∀ x ∈ X, ∀ y ∈ X, (SPref R x y ↔ φ x < φ y)) ∨
      (∀ x ∈ X, ∀ y ∈ X, (SPref R x y ↔ φ y < φ x)) := by
  rcases X.eq_empty_or_nonempty with hX | hX
  · left; subst hX; simp
  obtain ⟨m, hm, hmin⟩ := X.exists_min_image φ hX
  obtain ⟨M, hM, hmax⟩ := X.exists_max_image φ hX
  have inj : ∀ x ∈ X, ∀ y ∈ X, φ x = φ y → x = y := by
    intro x hx y hy h
    rw [hrep x hx, hrep y hy, h]
  by_cases hmM : m = M
  · subst hmM
    have hall : ∀ x ∈ X, x = m := fun x hx =>
      inj _ hx _ hm (le_antisymm (hmax x hx) (hmin x hx))
    left
    intro x hx y hy
    rw [hall x hx, hall y hy]
    exact ⟨fun h => absurd h.1 h.2, fun h => absurd h (lt_irrefl _)⟩
  have hcmp : SPref R m M ∨ SPref R M m := by
    rcases hR.complete m (hXs hm) M (hXs hM) with h | h
    · left; exact ⟨h, fun h' => hst m hm M hM hmM ⟨h, h'⟩⟩
    · right; exact ⟨h, fun h' => hst m hm M hM hmM ⟨h', h⟩⟩
  rcases hcmp with h | h
  · exact Or.inl (lr_key hXs hrep hR hm hM hmin hmax h)
  · right
    have hrep' : ∀ x ∈ X, x = x0 + (fun z => -φ z) x • (-d) := by
      intro x hx
      simp only [neg_smul, smul_neg, neg_neg]
      exact hrep x hx
    have := lr_key (φ := fun z => -φ z) hXs hrep' hR hM hm
      (fun x hx => neg_le_neg (hmax x hx)) (fun x hx => neg_le_neg (hmin x hx)) h
    intro x hx y hy
    rw [this x hx y hy]
    exact neg_lt_neg_iff

end Q3L
