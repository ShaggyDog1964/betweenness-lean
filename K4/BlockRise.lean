import K4.Defs
import K4.Menelaus
import K4.EdgeRatioLt
import K4.SprefCongr
import K4.EdgeLotsEq
import K4.RLotMem

namespace K4

/-- One block forces the `R`-edge ratio to rise by more than `2^(G-4)`.
Levels `A = lotP a` and `A' = lotP (a+4)`; `b, c, d` (resp. `b', c', d'`) are the ratios of
the indifferent points of `A` (resp. `A'`) on edges `(1,2)`, `(1,3)`, `(0,3)`.
Sketch. `menelaus` at level `A` (with `hP` = reflexive indifference of `A = rLot 0 2 (2^a)`,
from `hR.complete`) gives `2^a * c = b * d`; at `A'`, `2^(a+4) * c' = b' * d'`.
`b < 2^e`: `spref_congr` turns `hAD` into `SPref (rLot 1 2 b) (rLot 1 2 (2^e))`, then
`edge_ratio_lt`. `2^(e+G) < b'`: same from `hDA`. `d < d'`: same from `hAA` on edge
`(0,3)`. Then `16 c' = b' d' / 2^a > 2^(e+G) d / 2^a = 2^G (2^e d / 2^a) > 2^G (b d / 2^a)
= 2^G c` (all quantities positive; `nlinarith`/`gcongr`). Rewrites:
`edge_lots_eq_rLot`; memberships `rLot_mem_simplex`. -/
theorem block_rise {K : ℕ} (hK : 4 ≤ K) {R : Rel K} (hR : IsBetweennessPref R) (a e G : ℕ)
    {b c d b' c' d' : ℝ} (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (hb' : 0 < b') (hc' : 0 < c') (hd' : 0 < d')
    (hAD : SPref R (lotP K a) (lotQ K e)) (hDA : SPref R (lotQ K (e + G)) (lotP K (a + 4)))
    (hAA : SPref R (lotP K a) (lotP K (a + 4)))
    (hQ : Indiff R (rLot K 1 2 b) (lotP K a)) (hR3 : Indiff R (rLot K 1 3 c) (lotP K a))
    (hS : Indiff R (rLot K 0 3 d) (lotP K a))
    (hQ' : Indiff R (rLot K 1 2 b') (lotP K (a + 4)))
    (hR3' : Indiff R (rLot K 1 3 c') (lotP K (a + 4)))
    (hS' : Indiff R (rLot K 0 3 d') (lotP K (a + 4))) :
    (2 : ℝ) ^ G * c < 16 * c' := by
  obtain ⟨hPa, -, -⟩ := edge_lots_eq_rLot K a
  obtain ⟨hPa4, -, -⟩ := edge_lots_eq_rLot K (a + 4)
  obtain ⟨-, hQe, -⟩ := edge_lots_eq_rLot K e
  obtain ⟨-, hQeG, -⟩ := edge_lots_eq_rLot K (e + G)
  rw [hPa] at hAD hAA hQ hR3 hS
  rw [hPa4] at hDA hAA hQ' hR3' hS'
  rw [hQe] at hAD
  rw [hQeG] at hDA
  have h0K : 0 < K := by omega
  have h1K : 1 < K := by omega
  have h2K : 2 < K := by omega
  have h3K : 3 < K := by omega
  have hpa : (0 : ℝ) < 2 ^ a := by positivity
  have hpa4 : (0 : ℝ) < 2 ^ (a + 4) := by positivity
  have hpe : (0 : ℝ) < 2 ^ e := by positivity
  have hpeG : (0 : ℝ) < 2 ^ (e + G) := by positivity
  have mA := rLot_mem_simplex (K := K) (i := 0) (j := 2) (by norm_num) h0K h2K hpa.le
  have mA' := rLot_mem_simplex (K := K) (i := 0) (j := 2) (by norm_num) h0K h2K hpa4.le
  have mQe := rLot_mem_simplex (K := K) (i := 1) (j := 2) (by norm_num) h1K h2K hpe.le
  have mQeG := rLot_mem_simplex (K := K) (i := 1) (j := 2) (by norm_num) h1K h2K hpeG.le
  have mb := rLot_mem_simplex (K := K) (i := 1) (j := 2) (by norm_num) h1K h2K hb.le
  have mb' := rLot_mem_simplex (K := K) (i := 1) (j := 2) (by norm_num) h1K h2K hb'.le
  have md := rLot_mem_simplex (K := K) (i := 0) (j := 3) (by norm_num) h0K h3K hd.le
  have md' := rLot_mem_simplex (K := K) (i := 0) (j := 3) (by norm_num) h0K h3K hd'.le
  have reflI : ∀ x ∈ Simplex K, Indiff R x x := fun x hx =>
    have h := (hR.complete x hx x hx).elim id id
    ⟨h, h⟩
  have symI : ∀ {x y : Lot K}, Indiff R x y → Indiff R y x := fun h => ⟨h.2, h.1⟩
  -- Menelaus
  have men1 : (2 : ℝ) ^ a * c = b * d :=
    menelaus hK hR mA hpa hb hc hd (reflI _ mA) hQ hR3 hS
  have men2 : (2 : ℝ) ^ (a + 4) * c' = b' * d' :=
    menelaus hK hR mA' hpa4 hb' hc' hd' (reflI _ mA') hQ' hR3' hS'
  -- b < 2^e
  have hb_lt : b < 2 ^ e := by
    have h := spref_congr hR mA mb mQe mQe (symI hQ) (reflI _ mQe) hAD
    exact edge_ratio_lt hR (by norm_num) h2K hb hpe h
  have hb'_gt : (2 : ℝ) ^ (e + G) < b' := by
    have h := spref_congr hR mQeG mQeG mA' mb' (reflI _ mQeG) (symI hQ') hDA
    exact edge_ratio_lt hR (by norm_num) h2K hpeG hb' h
  have hd_lt : d < d' := by
    have h := spref_congr hR mA md mA' md' (symI hS) (symI hS') hAA
    exact edge_ratio_lt hR (by norm_num) h3K hd hd' h
  -- arithmetic
  have hpG : (0 : ℝ) < 2 ^ G := by positivity
  rw [pow_add] at men2 hb'_gt
  have key : (2 : ℝ) ^ a * (2 ^ G * c) < 2 ^ a * (16 * c') := by
    have e1 : (2 : ℝ) ^ a * (2 ^ G * c) = 2 ^ G * (b * d) := by rw [← men1]; ring
    have e2 : (2 : ℝ) ^ a * (16 * c') = b' * d' := by rw [← men2]; norm_num; ring
    rw [e1, e2]
    have s1 : (2 : ℝ) ^ G * (b * d) < 2 ^ G * (2 ^ e * d) := by
      apply mul_lt_mul_of_pos_left _ hpG
      exact mul_lt_mul_of_pos_right hb_lt hd
    have s2 : (2 : ℝ) ^ G * (2 ^ e * d) < b' * d := by
      have : (2 : ℝ) ^ G * (2 ^ e * d) = (2 ^ e * 2 ^ G) * d := by ring
      rw [this]
      exact mul_lt_mul_of_pos_right hb'_gt hd
    have s3 : b' * d < b' * d' := mul_lt_mul_of_pos_left hd_lt hb'
    linarith
  exact lt_of_mul_lt_mul_left key hpa.le

end K4
