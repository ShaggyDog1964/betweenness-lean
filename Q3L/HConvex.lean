/-
`strict_contour_convex` (part of the proof of Lemma 34; Lemma 1, strict part).
-/
import Q3L.Statement
import K4.MixMem
import K4.SprefTrans

namespace Q3L

open K4 (Lot Simplex Rel SPref Indiff IsBetweennessPref mix mix_mem_simplex)

private lemma mix_swap {K : ℕ} (t : ℝ) (p q : Lot K) : mix t p q = mix (1 - t) q p := by
  unfold mix
  funext i
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- A proper mixture is weakly above one of its endpoints. -/
private lemma mix_ge_min {K : ℕ} {R : Rel K} (hR : IsBetweennessPref R) {p q : Lot K}
    (hp : p ∈ Simplex K) (hq : q ∈ Simplex K) {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1) :
    R (mix t p q) p ∨ R (mix t p q) q := by
  have ht' : (1 - t) ∈ Set.Ioo (0 : ℝ) 1 := ⟨by linarith [ht.2], by linarith [ht.1]⟩
  by_cases hpq : R p q
  · by_cases hqp : R q p
    · exact Or.inl (hR.btw_indiff p hp q hq t ht ⟨hpq, hqp⟩).1
    · exact Or.inr (hR.btw_strict p hp q hq t ht ⟨hpq, hqp⟩).2.1
  · have hqp : R q p := (hR.complete p hp q hq).resolve_left hpq
    rw [mix_swap]
    exact Or.inl (hR.btw_strict q hq p hp (1 - t) ht' ⟨hqp, hpq⟩).2.1

/-- A proper mixture is weakly below one of its endpoints. -/
private lemma mix_le_max {K : ℕ} {R : Rel K} (hR : IsBetweennessPref R) {p q : Lot K}
    (hp : p ∈ Simplex K) (hq : q ∈ Simplex K) {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1) :
    R p (mix t p q) ∨ R q (mix t p q) := by
  have ht' : (1 - t) ∈ Set.Ioo (0 : ℝ) 1 := ⟨by linarith [ht.2], by linarith [ht.1]⟩
  by_cases hpq : R p q
  · by_cases hqp : R q p
    · exact Or.inl (hR.btw_indiff p hp q hq t ht ⟨hpq, hqp⟩).2
    · exact Or.inl (hR.btw_strict p hp q hq t ht ⟨hpq, hqp⟩).1.1
  · have hqp : R q p := (hR.complete p hp q hq).resolve_left hpq
    rw [mix_swap]
    exact Or.inr (hR.btw_strict q hq p hp (1 - t) ht' ⟨hqp, hpq⟩).1.1

/-- The strict upper and strict lower contour sets of `r` (inside the simplex) are convex.
Sketch (upper; lower is symmetric). Let `p, q` be in the set, `a, b ≥ 0`, `a + b = 1`. If
`a = 0` or `b = 0` the point is `q` or `p` (`zero_smul`, `one_smul`, `zero_add`). Otherwise
`a ∈ (0,1)` and `a • p + b • q = K4.mix a p q` (`b = 1 - a`), which lies in the simplex
(`K4.mix_mem_simplex`). By completeness, `SPref R p q`, `SPref R q p` or `p ∼ q`.
* `SPref R p q`: `btw_strict` gives `SPref R (mix a p q) q`; with `SPref R q r`,
  `K4.spref_trans` gives `SPref R (mix a p q) r`.
* `SPref R q p`: `mix a p q = mix (1-a) q p` (`ring`/`module` on functions); `btw_strict`
  with `t = 1 - a` gives `SPref R (mix) p`, then `spref_trans` with `SPref R p r`.
* `p ∼ q`: `btw_indiff` gives `mix a p q ∼ p`; then `R mix r` by `trans`, and `¬ R r mix`
  (else `R r p` by `trans`, contradicting `SPref R p r`).
Lower set: same three cases with the inequalities reversed (`SPref R r p`, `SPref R r q`). -/
theorem strict_contour_convex {K : ℕ} {R : Rel K} (hR : IsBetweennessPref R) {r : Lot K}
    (hr : r ∈ Simplex K) :
    Convex ℝ {p | p ∈ Simplex K ∧ SPref R p r} ∧
      Convex ℝ {p | p ∈ Simplex K ∧ SPref R r p} := by
  refine ⟨?_, ?_⟩
  · intro p hp q hq a b ha hb hab
    obtain ⟨hpS, hpr⟩ := hp
    obtain ⟨hqS, hqr⟩ := hq
    rcases eq_or_lt_of_le ha with h0 | ha0
    · subst h0
      have : b = 1 := by linarith
      subst this
      simpa using ⟨hqS, hqr⟩
    rcases eq_or_lt_of_le hb with h0 | hb0
    · subst h0
      have : a = 1 := by linarith
      subst this
      simpa using ⟨hpS, hpr⟩
    have hb' : b = 1 - a := by linarith
    have hm : a • p + b • q = mix a p q := by rw [hb']; rfl
    have hmS := mix_mem_simplex hpS hqS ha (by linarith : a ≤ 1)
    rw [hm]
    refine ⟨hmS, ?_⟩
    have key : ∀ x ∈ Simplex K, R (mix a p q) x → SPref R x r → SPref R (mix a p q) r :=
      fun x hx hmx hxr => ⟨hR.trans _ hmS x hx r hr hmx hxr.1,
        fun hrm => hxr.2 (hR.trans r hr _ hmS x hx hrm hmx)⟩
    rcases (mix_ge_min hR hpS hqS ⟨ha0, by linarith⟩) with h | h
    · exact key p hpS h hpr
    · exact key q hqS h hqr
  · intro p hp q hq a b ha hb hab
    obtain ⟨hpS, hpr⟩ := hp
    obtain ⟨hqS, hqr⟩ := hq
    rcases eq_or_lt_of_le ha with h0 | ha0
    · subst h0
      have : b = 1 := by linarith
      subst this
      simpa using ⟨hqS, hqr⟩
    rcases eq_or_lt_of_le hb with h0 | hb0
    · subst h0
      have : a = 1 := by linarith
      subst this
      simpa using ⟨hpS, hpr⟩
    have hb' : b = 1 - a := by linarith
    have hm : a • p + b • q = mix a p q := by rw [hb']; rfl
    have hmS := mix_mem_simplex hpS hqS ha (by linarith : a ≤ 1)
    rw [hm]
    refine ⟨hmS, ?_⟩
    have key : ∀ x ∈ Simplex K, R x (mix a p q) → SPref R r x → SPref R r (mix a p q) :=
      fun x hx hxm hrx => ⟨hR.trans r hr x hx _ hmS hrx.1 hxm,
        fun hmr => hrx.2 (hR.trans x hx _ hmS r hr hxm hmr)⟩
    rcases (mix_le_max hR hpS hqS ⟨ha0, by linarith⟩) with h | h
    · exact key p hpS h hpr
    · exact key q hqS h hqr

end Q3L
