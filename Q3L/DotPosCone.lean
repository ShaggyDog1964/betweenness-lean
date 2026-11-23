/-
`dot_pos_of_cone` (Lemma 84(3)).
-/
import Q3L.Statement
import Q3L.DotEq
import K4.DotFosd

namespace Q3L

open K4 (Lot Simplex tail)

/-- Lemma 84(3): a strictly increasing `W` is strictly positive on every nonzero weak-FOSD
direction.
Sketch (avoids Abel summation by reusing `K4.dot_lt_of_strictFOSD`). Let `c = fun _ => 1/K`
(the barycenter, in `Simplex K` since `0 < K`). Pick `ε > 0` so small that
`ε * |d k| ≤ 1/K` for all `k` (e.g. `ε = 1 / (K * (1 + ∑ k, |d k|))`). Then
`q := c + ε • d ∈ Simplex K` (entries `≥ 0`; sum `1 + ε * ∑ d = 1` because `∑ d = 0`,
the first conjunct of `FOSDCone`). Tails are additive: `tail q k = tail c k + ε * tail d k ≥
tail c k` (`Finset.sum_add_distrib`, `Finset.mul_sum`), so `K4.FOSD q c`; and `q ≠ c`
because `d ≠ 0` and `ε ≠ 0`. Hence `K4.StrictFOSD q c` and `K4.dot_lt_of_strictFOSD` gives
`dot W c < dot W q = dot W c + ε * dot W d` (`dot_eq_dotProduct`, linearity), so
`0 < dot W d`. -/
theorem dot_pos_of_cone {K : ℕ} (hK : 0 < K) {W d : Lot K} (hW : StrictMono W)
    (hd : d ∈ FOSDCone K) (hd0 : d ≠ 0) : 0 < dot W d := by
  obtain ⟨hsum, htail⟩ := hd
  have hKpos : (0 : ℝ) < K := by exact_mod_cast hK
  set S : ℝ := ∑ k, |d k| with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg (fun k _ => abs_nonneg (d k))
  set ε : ℝ := 1 / ((K : ℝ) * (1 + S)) with hε
  have hden : 0 < (K : ℝ) * (1 + S) := by positivity
  have hεpos : 0 < ε := by positivity
  set c : Lot K := fun _ => 1 / (K : ℝ) with hc
  set q : Lot K := c + ε • d with hq
  have hcS : c ∈ Simplex K := by
    refine ⟨fun i => by simp only [hc]; positivity, ?_⟩
    simp [hc, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    field_simp
  have hqS : q ∈ Simplex K := by
    refine ⟨fun i => ?_, ?_⟩
    · have h1 : |d i| ≤ S := by
        rw [hS]
        exact Finset.single_le_sum (f := fun k => |d k|) (fun k _ => abs_nonneg (d k))
          (Finset.mem_univ i)
      have h2 : ε * |d i| ≤ ε * S := mul_le_mul_of_nonneg_left h1 hεpos.le
      have h3 : ε * S ≤ 1 / (K : ℝ) := by
        rw [hε, div_mul_eq_mul_div, one_mul, div_le_div_iff₀ hden hKpos]
        nlinarith
      have h4 : -(ε * |d i|) ≤ ε * d i := by
        have := neg_abs_le (d i)
        nlinarith
      simp only [hq, hc, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      linarith
    · have : ∑ i, q i = ∑ i, c i + ε * ∑ i, d i := by
        simp only [hq, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
          Finset.mul_sum]
      rw [this, hsum, mul_zero, add_zero]
      exact hcS.2
  have hF : K4.StrictFOSD q c := by
    refine ⟨fun k => ?_, ?_⟩
    · have : K4.tail q k = K4.tail c k + ε * K4.tail d k := by
        simp only [K4.tail, hq, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
          Finset.sum_add_distrib, Finset.mul_sum]
      rw [this]
      have := htail k
      nlinarith
    · intro h
      apply hd0
      have h' : ε • d = 0 := by
        have : c + ε • d = c + 0 := by rw [add_zero]; exact h
        exact add_left_cancel this
      exact (smul_eq_zero.mp h').resolve_left hεpos.ne'
  have hlt := K4.dot_lt_of_strictFOSD hW hqS hcS hF
  have hlin : K4.dot W q = K4.dot W c + ε * dot W d := by
    simp only [K4.dot, dot, hq, Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_add,
      Finset.sum_add_distrib, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl (fun k _ => by ring)
  rw [hlin] at hlt
  have : 0 < ε * dot W d := by linarith
  exact pos_of_mul_pos_right this hεpos.le

end Q3L
