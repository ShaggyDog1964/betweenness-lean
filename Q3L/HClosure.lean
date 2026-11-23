/-
`nonneg_of_relOpen` (part of the proof of Lemma 34: from interior points to the whole
relatively open set).
-/
import Q3L.Statement
import Q3L.DotEq
import Q3L.MixNear
import K4.MixMem

namespace Q3L

open K4 (Lot Simplex)

private theorem dot_mix_lin {K : ℕ} (W c p : Lot K) (s : ℝ) :
    dot W (K4.mix s c p) = s * dot W c + (1 - s) * dot W p := by
  unfold dot K4.mix
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  ring

/-- If `dot W > 0` at every positive point of `Simplex ∩ G` (`G` open), then `dot W ≥ 0` on
all of `Simplex ∩ G`.
Sketch. Let `p ∈ Simplex ∩ G` and suppose `dot W p < 0`. Let `c := fun _ => 1/K ∈ Simplex`
(`0 < K`). `exists_mix_mem_open hG hp c` gives `s₀`. For `s ∈ (0, s₀)`, `q_s := K4.mix s c p`
is in `G`, in the simplex (`K4.mix_mem_simplex`) and has positive coordinates
(`s / K + (1 - s) * p k > 0`). So `0 < dot W q_s = s * dot W c + (1 - s) * dot W p`
(`dot_eq_dotProduct`, linearity). Choose `s > 0` below `s₀` and below
`-dot W p / (|dot W c| - dot W p + 1)` (any `s` with `s * (dot W c - dot W p) < - dot W p`);
then the right side is `< 0`, contradiction. -/
theorem nonneg_of_relOpen {K : ℕ} (hK : 0 < K) {G : Set (Lot K)} (hG : IsOpen G) {W : Lot K}
    (h : ∀ p ∈ Simplex K ∩ G, (∀ k, 0 < p k) → 0 < dot W p) :
    ∀ p ∈ Simplex K ∩ G, 0 ≤ dot W p := by
  intro p hp
  by_contra hneg
  rw [not_le] at hneg
  set c : Lot K := fun _ => 1 / (K : ℝ) with hc_def
  have hKpos : (0 : ℝ) < K := by exact_mod_cast hK
  have hc : c ∈ Simplex K := by
    refine ⟨fun i => by simp only [c]; positivity, ?_⟩
    simp [c, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    field_simp
  obtain ⟨s₀, hs₀, hs₀1, hmem⟩ := exists_mix_mem_open hG hp.2 c
  set a := dot W p
  set b := dot W c
  set M : ℝ := |b - a| + 1
  have hM : 0 < M := by positivity
  set s : ℝ := min (s₀ / 2) ((-a) / (2 * M))
  have hs_pos : 0 < s := lt_min (by linarith) (div_pos (by linarith) (by positivity))
  have hs_lt : s < s₀ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hs1 : s < 1 := lt_of_lt_of_le hs_lt hs₀1
  have hs_le : s ≤ (-a) / (2 * M) := min_le_right _ _
  have hq : K4.mix s c p ∈ Simplex K ∩ G :=
    ⟨K4.mix_mem_simplex hc hp.1 hs_pos.le hs1.le, hmem s hs_pos.le hs_lt⟩
  have hpos : ∀ k, 0 < K4.mix s c p k := by
    intro k
    show 0 < s * c k + (1 - s) * p k
    have hpk : 0 ≤ p k := hp.1.1 k
    have hck : 0 < c k := by simp [c]; positivity
    have h1 : 0 < s * c k := mul_pos hs_pos hck
    have h2 : 0 ≤ (1 - s) * p k := mul_nonneg (by linarith) hpk
    linarith
  have key := h _ hq hpos
  rw [dot_mix_lin] at key
  have h1 : s * (b - a) ≤ s * |b - a| := mul_le_mul_of_nonneg_left (le_abs_self _) hs_pos.le
  have h2 : s * M ≤ (-a) / 2 := by
    have := mul_le_mul_of_nonneg_right hs_le hM.le
    calc s * M ≤ (-a) / (2 * M) * M := this
      _ = (-a) / 2 := by field_simp
  have h3 : s * |b - a| ≤ s * M := mul_le_mul_of_nonneg_left (by simp [M]) hs_pos.le
  nlinarith

end Q3L
