/-
`sign_iff_of_sep` (part of the proof of Lemma 34: weak separation plus one strict witness
on each side gives the exact sign characterization).
-/
import Q3L.Statement
import Q3L.DotEq
import Q3L.MixNear
import K4.MixMem
import K4.SprefTrans

namespace Q3L

open K4 (Lot Simplex Rel SPref IsBetweennessPref)

private lemma dot_mix' {K : ℕ} (W a b : Lot K) (t : ℝ) :
    dot W (K4.mix t a b) = t * dot W a + (1 - t) * dot W b := by
  simp only [dot, K4.mix, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  ring

private lemma exists_t_pos {a b : ℝ} (ha : 0 < a) (hb : b < 0) :
    ∃ t ∈ Set.Ioo (0 : ℝ) 1, 0 < t * a + (1 - t) * b := by
  have hd : 0 < a - 2 * b := by linarith
  refine ⟨-2 * b / (a - 2 * b), ⟨div_pos (by linarith) hd, ?_⟩, ?_⟩
  · rw [div_lt_one hd]; linarith
  · have : -2 * b / (a - 2 * b) * a + (1 - -2 * b / (a - 2 * b)) * b
        = (-(a * b)) / (a - 2 * b) := by
      field_simp
      ring
    rw [this]
    exact div_pos (by nlinarith) hd

/-- Let `W` be `≥ 0` on the strict upper set of `r`, `≤ 0` on the strict lower set, both sets
relatively open (traces of open `G`, `G'`), with a lower point `z` where `dot W z < 0` and an
upper point `z'` where `dot W z' > 0`. Then on the simplex, `p ≻ r ↔ dot W p > 0` and
`r ≻ p ↔ dot W p < 0`.
Sketch (`dot` of `K4.mix t a b` is `t * dot W a + (1-t) * dot W b`, by `dot_eq_dotProduct`).
(c) `0 < dot W p → SPref R p r`. Otherwise `R r p` (completeness and `¬ SPref`). If `¬ R p r`
then `SPref R r p`, so `dot W p ≤ 0` by `hL`: contradiction. So `p ∼ r`. Then `SPref R p z`
(`R p z` by `trans p r z`; `¬ R z p`, else `R z r`). For `t ∈ (0,1)`, `btw_strict` gives
`SPref R p m` and `SPref R m z` for `m = K4.mix t p z ∈ Simplex`. Then `SPref R r m`
(`R r m` by `trans r p m`; `¬ R m r`, else `R m p` by `trans m r p`). So `dot W m ≤ 0` by `hL`,
but `t * dot W p + (1-t) * dot W z > 0` for `t` close to `1`, e.g.
`t := (1 + t₀)/2`, `t₀ := -dot W z / (dot W p - dot W z) ∈ (0,1)`. Contradiction.
(d) `dot W p < 0 → SPref R r p`: symmetric, with `z'` and `hU`.
(e) `SPref R p r → 0 < dot W p`. `hU` gives `≥ 0`; suppose `dot W p = 0`. `p ∈ G` (`hGU`).
`exists_mix_mem_open hG _ z` gives `s₀`; take `s := s₀ / 2`, `m := K4.mix s z p ∈ G ∩ Simplex`,
so `SPref R m r` and `dot W m ≥ 0` by `hU`; but `dot W m = s * dot W z < 0`.
(f) `SPref R r p → dot W p < 0`: symmetric, with `G'`, `z'` and `hL`. -/
theorem sign_iff_of_sep {K : ℕ} {R : Rel K} (hR : IsBetweennessPref R) {r : Lot K}
    (hr : r ∈ Simplex K) {W : Lot K} {G G' : Set (Lot K)} (hG : IsOpen G) (hG' : IsOpen G')
    (hGU : ∀ p ∈ Simplex K, (p ∈ G ↔ SPref R p r))
    (hGL : ∀ p ∈ Simplex K, (p ∈ G' ↔ SPref R r p))
    (hU : ∀ p ∈ Simplex K, SPref R p r → 0 ≤ dot W p)
    (hL : ∀ p ∈ Simplex K, SPref R r p → dot W p ≤ 0)
    (hz : ∃ z ∈ Simplex K, SPref R r z ∧ dot W z < 0)
    (hz' : ∃ z ∈ Simplex K, SPref R z r ∧ 0 < dot W z) :
    ∀ p ∈ Simplex K, (SPref R p r ↔ 0 < dot W p) ∧ (SPref R r p ↔ dot W p < 0) := by
  intro p hp
  -- (c)
  have hc : 0 < dot W p → SPref R p r := by
    intro hWp
    by_contra hn
    have hrp : R r p := by
      by_contra hrp
      rcases hR.complete p hp r hr with h | h
      · exact hn ⟨h, hrp⟩
      · exact hrp h
    have hpr : R p r := by
      by_contra hpr
      have := hL p hp ⟨hrp, hpr⟩
      linarith
    obtain ⟨z, hzS, hrz, hWz⟩ := hz
    have hpz : SPref R p z := ⟨hR.trans p hp r hr z hzS hpr hrz.1,
      fun h => hrz.2 (hR.trans z hzS p hp r hr h hpr)⟩
    obtain ⟨t, ht, hpos⟩ := exists_t_pos hWp hWz
    have hmS : K4.mix t p z ∈ Simplex K := K4.mix_mem_simplex hp hzS ht.1.le ht.2.le
    have hpm := (hR.btw_strict p hp z hzS t ht hpz).1
    have hrm : SPref R r (K4.mix t p z) :=
      ⟨hR.trans r hr p hp _ hmS hrp hpm.1,
        fun h => hpm.2 (hR.trans _ hmS r hr p hp h hrp)⟩
    have := hL _ hmS hrm
    rw [dot_mix'] at this
    linarith
  -- (d)
  have hd : dot W p < 0 → SPref R r p := by
    intro hWp
    by_contra hn
    have hpr : R p r := by
      by_contra hpr
      rcases hR.complete r hr p hp with h | h
      · exact hn ⟨h, hpr⟩
      · exact hpr h
    have hrp : R r p := by
      by_contra hrp
      have := hU p hp ⟨hpr, hrp⟩
      linarith
    obtain ⟨z, hzS, hzr, hWz⟩ := hz'
    have hzp : SPref R z p := ⟨hR.trans z hzS r hr p hp hzr.1 hrp,
      fun h => hzr.2 (hR.trans r hr p hp z hzS hrp h)⟩
    obtain ⟨t, ht, hpos⟩ := exists_t_pos (a := -dot W p) (b := -dot W z) (by linarith)
      (by linarith)
    have ht' : 1 - t ∈ Set.Ioo (0 : ℝ) 1 := ⟨by linarith [ht.2], by linarith [ht.1]⟩
    have hmS : K4.mix (1 - t) z p ∈ Simplex K :=
      K4.mix_mem_simplex hzS hp ht'.1.le ht'.2.le
    have hmp := (hR.btw_strict z hzS p hp (1 - t) ht' hzp).2
    have hmr : SPref R (K4.mix (1 - t) z p) r :=
      ⟨hR.trans _ hmS p hp r hr hmp.1 hpr,
        fun h => hmp.2 (hR.trans p hp r hr _ hmS hpr h)⟩
    have := hU _ hmS hmr
    rw [dot_mix'] at this
    nlinarith
  refine ⟨⟨fun h => ?_, hc⟩, ⟨fun h => ?_, hd⟩⟩
  · -- (e)
    have h0 := hU p hp h
    rcases h0.lt_or_eq with h1 | h1
    · exact h1
    exfalso
    obtain ⟨z, hzS, hrz, hWz⟩ := hz
    have hpG : p ∈ G := (hGU p hp).2 h
    obtain ⟨s₀, hs₀, hs₁, hmem⟩ := exists_mix_mem_open hG hpG z
    have hmG := hmem (s₀ / 2) (by linarith) (by linarith)
    have hmS : K4.mix (s₀ / 2) z p ∈ Simplex K :=
      K4.mix_mem_simplex hzS hp (by linarith) (by linarith)
    have := hU _ hmS ((hGU _ hmS).1 hmG)
    rw [dot_mix', ← h1] at this
    nlinarith
  · -- (f)
    have h0 := hL p hp h
    rcases h0.lt_or_eq with h1 | h1
    · exact h1
    exfalso
    obtain ⟨z, hzS, hzr, hWz⟩ := hz'
    have hpG : p ∈ G' := (hGL p hp).2 h
    obtain ⟨s₀, hs₀, hs₁, hmem⟩ := exists_mix_mem_open hG' hpG z
    have hmG := hmem (s₀ / 2) (by linarith) (by linarith)
    have hmS : K4.mix (s₀ / 2) z p ∈ Simplex K :=
      K4.mix_mem_simplex hzS hp (by linarith) (by linarith)
    have := hL _ hmS ((hGL _ hmS).1 hmG)
    rw [dot_mix', h1] at this
    nlinarith

end Q3L
