/-
`strictMono_of_sign` (part of the proof of Lemma 34: the separating vector is strictly
increasing).
-/
import Q3L.Statement
import Q3L.DotEq
import K4.Defs
import K4.FosdShift
import K4.SprefTrans

namespace Q3L

open K4 (Lot Simplex Rel SPref IsBetweennessPref)

private lemma sum_mul_vtx {K j : ℕ} (hj : j < K) (W : Lot K) :
    ∑ k, W k * K4.vtx K j k = W ⟨j, hj⟩ := by
  rw [Finset.sum_eq_single_of_mem (⟨j, hj⟩ : Fin K) (Finset.mem_univ _)]
  · simp [K4.vtx]
  · intro b _ hb
    have hbm : b.val ≠ j := fun h => hb (Fin.ext h)
    simp [K4.vtx, hbm]

private lemma sum_vtx {K j : ℕ} (hj : j < K) : ∑ k, K4.vtx K j k = 1 := by
  have := sum_mul_vtx hj (fun _ => 1)
  simpa using this

/-- If `dot W` gives the sign of the comparison with `r` on the simplex, and some positive
simplex point `p` has `dot W p = 0`, then `W` is strictly increasing.
Proof: `p ∼ r`; shifting the mass `p a` from prize `a` to `a+1` gives a strict FOSD
improvement `p' ≻ p ∼ r`, so `0 < dot W p' = p a * (W (a+1) - W a)`; then induct on the gap. -/
theorem strictMono_of_sign {K : ℕ} {R : Rel K} (hR : IsBetweennessPref R) {r : Lot K}
    (hr : r ∈ Simplex K) {W : Lot K}
    (hsign : ∀ p ∈ Simplex K, (SPref R p r ↔ 0 < dot W p) ∧ (SPref R r p ↔ dot W p < 0))
    (hp : ∃ p ∈ Simplex K, (∀ k, 0 < p k) ∧ dot W p = 0) : StrictMono W := by
  obtain ⟨p, hpS, hpos, hp0⟩ := hp
  have hn1 : ¬ SPref R p r := fun h => by
    have := ((hsign p hpS).1.mp h); linarith
  have hn2 : ¬ SPref R r p := fun h => by
    have := ((hsign p hpS).2.mp h); linarith
  have hpr : R p r := by
    rcases hR.complete p hpS r hr with h | h
    · exact h
    · by_contra h'; exact hn2 ⟨h, h'⟩
  have hrp : R r p := by
    rcases hR.complete p hpS r hr with h | h
    · by_contra h'; exact hn1 ⟨h, h'⟩
    · exact h
  have step : ∀ a (h : a + 1 < K), W ⟨a, by omega⟩ < W ⟨a + 1, h⟩ := by
    intro a h
    have ha : a < K := by omega
    set ε := p ⟨a, ha⟩ with hε
    have hεpos : 0 < ε := hpos _
    set p' : Lot K := p + ε • (K4.vtx K (a + 1) - K4.vtx K a) with hp'
    have hp'S : p' ∈ Simplex K := by
      refine ⟨fun k => ?_, ?_⟩
      · simp only [hp', Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, K4.vtx]
        by_cases h1 : k.val = a
        · have hk : k = ⟨a, ha⟩ := Fin.ext h1
          subst hk
          simp [hε]
        · have := (hpS.1 k)
          by_cases h2 : k.val = a + 1
          · simp [h1, h2]; nlinarith
          · simp [h1, h2]; exact this
      · simp only [hp', Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib, sum_vtx h,
          sum_vtx ha, hpS.2]
        ring
    have hfosd := K4.strictFOSD_shift (show a < a + 1 by omega) h p hεpos
    have h1 : SPref R p' p := hR.strictMono p' hp'S p hpS hfosd
    have h2 : SPref R p' r :=
      ⟨hR.trans p' hp'S p hpS r hr h1.1 hpr,
        fun hrp' => h1.2 (hR.trans p hpS r hr p' hp'S hpr hrp')⟩
    have h3 := (hsign p' hp'S).1.mp h2
    have hdot : dot W p' = dot W p + ε * (W ⟨a + 1, h⟩ - W ⟨a, ha⟩) := by
      simp only [dot, hp', Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, mul_add]
      rw [Finset.sum_add_distrib]
      have : ∑ k, W k * (ε * (K4.vtx K (a + 1) k - K4.vtx K a k))
          = ε * (∑ k, W k * K4.vtx K (a + 1) k - ∑ k, W k * K4.vtx K a k) := by
        rw [← Finset.sum_sub_distrib, Finset.mul_sum]
        exact Finset.sum_congr rfl fun k _ => by ring
      rw [this, sum_mul_vtx h, sum_mul_vtx ha]
    rw [hdot, hp0] at h3
    have : 0 < W ⟨a + 1, h⟩ - W ⟨a, ha⟩ := by
      by_contra hc
      nlinarith [not_lt.mp hc]
    linarith
  have gap : ∀ m i (h : i + m + 1 < K), W ⟨i, by omega⟩ < W ⟨i + m + 1, h⟩ := by
    intro m
    induction m with
    | zero => intro i h; exact step i h
    | succ n ih =>
      intro i h
      exact lt_trans (ih i (by omega)) (step (i + n + 1) (by omega))
  intro i j hij
  have hij' : i.val < j.val := hij
  have := gap (j.val - i.val - 1) i.val (by omega)
  have e : (⟨i.val + (j.val - i.val - 1) + 1, by omega⟩ : Fin K) = j :=
    Fin.ext (by simp only; omega)
  rw [e] at this
  exact this

end Q3L
