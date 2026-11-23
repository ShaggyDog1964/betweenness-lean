/-
`exists_halfReversal_rule`: from a generic direction `v` to the rule
`½[u] + ½[M w − u]` and its menu values (the two mixtures in the proof of Theorem 36(2), one
at a time).
-/
import Q3L.Statement
import Q3L.DotEq
import Q3L.LiftStrictMono
import Q3L.HalfRule
import Q3L.IsMaxInEu
import Q3L.TwoEuMixture

namespace Q3L

open K4 (Lot IsBetweennessPref)

/-- Let `w` be strictly increasing and orthogonal to `dirSpace X`, and `v` injective on `X`.
Then some `ρ = ½[u] + ½[M w − u]` (with `u` ordering `X` as `v` does and `M w − u` reversing
it) is a half-reversal, a mixture of EU and of betweenness preferences, has every binary
probability `½`, gives probability `0` to an element of `A` that is neither the `v`-largest
nor the `v`-smallest, and `½` to the strict `v`-smallest element of `A` when `|A| ≥ 2`.
Sketch. `lift_strictMono hw v` gives `M` with `u := v + M • w` strictly increasing;
`lift_strictMono hw (-u)` gives `M'` with `-u + M' • w` strictly increasing, which equals
`M' • w - u` (`funext`, `ring`/`abel`). Put `u' := M' • w - u`.
Order transfer: for `x, y ∈ X`, `x - y ∈ dirSpace X` (`vsub_mem_vectorSpan`), so
`dot w x = dot w y` by `hperp` (`dot_eq_dotProduct`, `dotProduct_sub`). Hence
`dot u x - dot u y = dot v x - dot v y` and `dot u' x - dot u' y = -(dot v x - dot v y)`.
So both EU relations are strict on `X` (from `hinj`), and for `A ⊆ X`, by
`isMaxIn_euRel_iff`: `IsMaxIn (euRel u) x A ↔ x ∈ A ∧ ∀ y ∈ A, y ≠ x → dot v y < dot v x` and
`IsMaxIn (euRel u') x A ↔ x ∈ A ∧ ∀ y ∈ A, y ≠ x → dot v x < dot v y`.
`exists_halfRule` gives `ρ`. `IsHalfReversal`: witnesses `u, M'`. Mixtures:
`mixture_of_two_eu`. Binary, `x ≠ y`: exactly one of `dot v y < dot v x`,
`dot v x < dot v y` holds (`hinj`, `lt_or_gt_of_ne`), so exactly one `if` is `1/2`.
Neither-extreme: both `if`s are false. Strict minimum with something above: the first `if`
is false (the `y` above), the second true, so `0 + 1/2`. -/
theorem exists_halfReversal_rule {K : ℕ} {X : Finset (Lot K)} {w : Lot K}
    (hw : StrictMono w) (hperp : ∀ v ∈ dirSpace X, dot w v = 0) {v : Lot K}
    (hinj : ∀ x ∈ X, ∀ y ∈ X, x ≠ y → dot v x ≠ dot v y) :
    ∃ ρ : RandomChoiceRule X, IsHalfReversal X w ρ ∧ IsMixture IsEUPref X ρ ∧
      IsMixture IsBetweennessPref X ρ ∧
      (∀ x ∈ X, ∀ y ∈ X, x ≠ y → ρ.p x {x, y} = 1 / 2) ∧
      (∀ A ⊆ X, ∀ x ∈ A, (∃ y ∈ A, dot v x < dot v y) → (∃ y ∈ A, dot v y < dot v x) →
        ρ.p x A = 0) ∧
      (∀ A ⊆ X, ∀ x ∈ A, (∃ y ∈ A, dot v x < dot v y) →
        (∀ y ∈ A, y ≠ x → dot v x < dot v y) → ρ.p x A = 1 / 2) := by
  classical
  obtain ⟨M, hM⟩ := lift_strictMono hw v
  set u : Lot K := v + M • w with hu_def
  obtain ⟨M', hM'⟩ := lift_strictMono hw (-u)
  have hu'eq : -u + M' • w = M' • w - u := by
    funext k; simp only [Pi.add_apply, Pi.neg_apply, Pi.sub_apply]; ring
  rw [hu'eq] at hM'
  have hwX : ∀ x ∈ X, ∀ y ∈ X, dot w x = dot w y := by
    intro x hx y hy
    have hmem : x - y ∈ dirSpace X := by
      have := vsub_mem_vectorSpan ℝ (s := (↑X : Set (Lot K))) hx hy
      rw [vsub_eq_sub] at this
      exact this
    have h0 := hperp _ hmem
    rw [dot_eq_dotProduct, dotProduct_sub] at h0
    rw [dot_eq_dotProduct, dot_eq_dotProduct]; linarith
  have hdu : ∀ x, dot u x = dot v x + M * dot w x := by
    intro x
    simp only [hu_def, dot_eq_dotProduct, add_dotProduct, smul_dotProduct, smul_eq_mul]
  have hdu' : ∀ x, dot (M' • w - u) x = M' * dot w x - (dot v x + M * dot w x) := by
    intro x
    rw [← hdu]
    simp only [dot_eq_dotProduct, sub_dotProduct, smul_dotProduct, smul_eq_mul]
  have hlt : ∀ x ∈ X, ∀ y ∈ X, (dot u x < dot u y ↔ dot v x < dot v y) := by
    intro x hx y hy
    rw [hdu, hdu, hwX x hx y hy]; constructor <;> intro h <;> linarith
  have hlt' : ∀ x ∈ X, ∀ y ∈ X,
      (dot (M' • w - u) x < dot (M' • w - u) y ↔ dot v y < dot v x) := by
    intro x hx y hy
    rw [hdu', hdu', hwX x hx y hy]; constructor <;> intro h <;> linarith
  have hsu : StrictOn (euRel u) X := by
    intro x hx y hy hxy ⟨h1, h2⟩
    apply hinj x hx y hy hxy
    unfold euRel at h1 h2
    rw [hdu, hdu, hwX x hx y hy] at h1 h2; linarith
  have hsu' : StrictOn (euRel (M' • w - u)) X := by
    intro x hx y hy hxy ⟨h1, h2⟩
    apply hinj x hx y hy hxy
    unfold euRel at h1 h2
    rw [hdu', hdu', hwX x hx y hy] at h1 h2; linarith
  obtain ⟨ρ, hρ⟩ := exists_halfRule hsu hsu'
  have hmax1 : ∀ A ⊆ X, ∀ x ∈ A,
      (IsMaxIn (euRel u) x A ↔ ∀ y ∈ A, y ≠ x → dot v y < dot v x) := by
    intro A hA x hx
    rw [isMaxIn_euRel_iff]
    constructor
    · rintro ⟨_, h⟩ y hy hyx; exact (hlt y (hA hy) x (hA hx)).1 (h y hy hyx)
    · intro h; exact ⟨hx, fun y hy hyx => (hlt y (hA hy) x (hA hx)).2 (h y hy hyx)⟩
  have hmax2 : ∀ A ⊆ X, ∀ x ∈ A,
      (IsMaxIn (euRel (M' • w - u)) x A ↔ ∀ y ∈ A, y ≠ x → dot v x < dot v y) := by
    intro A hA x hx
    rw [isMaxIn_euRel_iff]
    constructor
    · rintro ⟨_, h⟩ y hy hyx; exact (hlt' y (hA hy) x (hA hx)).1 (h y hy hyx)
    · intro h; exact ⟨hx, fun y hy hyx => (hlt' y (hA hy) x (hA hx)).2 (h y hy hyx)⟩
  have hmix := mixture_of_two_eu hM hM' hsu hsu' ρ (fun A _ _ x _ => hρ x A)
  refine ⟨ρ, ⟨u, M', hM, hM', hsu, hsu', fun A _ _ x _ => hρ x A⟩, hmix.1, hmix.2,
    ?_, ?_, ?_⟩
  · intro x hx y hy hxy
    have hA : ({x, y} : Finset (Lot K)) ⊆ X := by
      intro z hz; simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl <;> assumption
    have hxA : x ∈ ({x, y} : Finset (Lot K)) := by simp
    have hyA : y ∈ ({x, y} : Finset (Lot K)) := by simp
    rw [hρ]
    have hne := hinj x hx y hy hxy
    rcases lt_or_gt_of_ne hne with h | h
    · have n1 : ¬ IsMaxIn (euRel u) x {x, y} := fun hm =>
        absurd ((hmax1 _ hA x hxA).1 hm y hyA (Ne.symm hxy)) (not_lt.mpr h.le)
      have p2 : IsMaxIn (euRel (M' • w - u)) x {x, y} := by
        rw [hmax2 _ hA x hxA]; intro z hz hzx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hz
        rcases hz with rfl | rfl
        · exact absurd rfl hzx
        · exact h
      simp [n1, p2]
    · have p1 : IsMaxIn (euRel u) x {x, y} := by
        rw [hmax1 _ hA x hxA]; intro z hz hzx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hz
        rcases hz with rfl | rfl
        · exact absurd rfl hzx
        · exact h
      have n2 : ¬ IsMaxIn (euRel (M' • w - u)) x {x, y} := fun hm =>
        absurd ((hmax2 _ hA x hxA).1 hm y hyA (Ne.symm hxy)) (not_lt.mpr h.le)
      simp [p1, n2]
  · rintro A hA x hx ⟨y, hy, hxy⟩ ⟨z, hz, hzx⟩
    have n1 : ¬ IsMaxIn (euRel u) x A := fun hm =>
      absurd ((hmax1 A hA x hx).1 hm y hy (by rintro rfl; exact lt_irrefl _ hxy))
        (not_lt.mpr hxy.le)
    have n2 : ¬ IsMaxIn (euRel (M' • w - u)) x A := fun hm =>
      absurd ((hmax2 A hA x hx).1 hm z hz (by rintro rfl; exact lt_irrefl _ hzx))
        (not_lt.mpr hzx.le)
    rw [hρ]; simp [n1, n2]
  · rintro A hA x hx ⟨y, hy, hxy⟩ hmin
    have n1 : ¬ IsMaxIn (euRel u) x A := fun hm =>
      absurd ((hmax1 A hA x hx).1 hm y hy (by rintro rfl; exact lt_irrefl _ hxy))
        (not_lt.mpr hxy.le)
    have p2 : IsMaxIn (euRel (M' • w - u)) x A := (hmax2 A hA x hx).2 hmin
    rw [hρ]; simp [n1, p2]

end Q3L
