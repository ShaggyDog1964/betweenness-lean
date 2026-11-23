import Odds.Defs
import K4.Menelaus
import K4.EdgeRatioLt
import K4.SprefCongr
import K4.RLotMem

namespace Odds

open K4

/-- Base-free block rise. Levels `A = rLot 0 2 x`, `A' = rLot 0 2 x'`, ranked
`A ≻ D = rLot 1 2 y`, `D' = rLot 1 2 y' ≻ A'`, `A ≻ A'`; `p, c, d` (resp. `p', c', d'`)
are the ratios of the points indifferent to `A` (resp. `A'`) on edges `(1,2)`, `(1,3)`,
`(0,3)`. Conclusion: `y' x c < y x' c'`. (With `x = b^a, x' = b^(a+4), y = b^e,
y' = b^(e+G)` this is `b^G c < b^4 c'`.)
Sketch (same as `K4.block_rise`, without the base-2 rewrites). Memberships by
`K4.rLot_mem_simplex`; reflexive indifference `Indiff R z z` from `hR.complete`.
* `K4.menelaus` at `A` (with `Indiff R A A`): `x * c = p * d`; at `A'`: `x' * c' = p' * d'`.
* `p < y`: `K4.spref_congr hR` turns `hAD` into `SPref (rLot 1 2 p) (rLot 1 2 y)` (using
  `hQ` reversed and reflexivity of `D`), then `K4.edge_ratio_lt` (`1 < 2 < K`).
* `y' < p'`: same from `hDA` and `hQ'`.
* `d < d'`: same from `hAA`, `hS`, `hS'` on edge `(0,3)`.
* Arithmetic, all factors positive (`mul_lt_mul_of_pos_left/right` or `nlinarith`):
  `y' * x * c = y' * (p * d) < y' * (y * d) = y * (y' * d) < y * (p' * d) < y * (p' * d')
  = y * x' * c'`. -/
theorem block_rise_real {K : ℕ} (hK : 4 ≤ K) {R : Rel K} (hR : IsBetweennessPref R)
    {x x' y y' p c d p' c' d' : ℝ} (hx : 0 < x) (hx' : 0 < x') (hy : 0 < y) (hy' : 0 < y')
    (hp : 0 < p) (hc : 0 < c) (hd : 0 < d) (hp' : 0 < p') (hc' : 0 < c') (hd' : 0 < d')
    (hAD : SPref R (rLot K 0 2 x) (rLot K 1 2 y))
    (hDA : SPref R (rLot K 1 2 y') (rLot K 0 2 x'))
    (hAA : SPref R (rLot K 0 2 x) (rLot K 0 2 x'))
    (hQ : Indiff R (rLot K 1 2 p) (rLot K 0 2 x))
    (hR3 : Indiff R (rLot K 1 3 c) (rLot K 0 2 x))
    (hS : Indiff R (rLot K 0 3 d) (rLot K 0 2 x))
    (hQ' : Indiff R (rLot K 1 2 p') (rLot K 0 2 x'))
    (hR3' : Indiff R (rLot K 1 3 c') (rLot K 0 2 x'))
    (hS' : Indiff R (rLot K 0 3 d') (rLot K 0 2 x')) :
    y' * x * c < y * x' * c' := by
  have h0K : 0 < K := by omega
  have h1K : 1 < K := by omega
  have h2K : 2 < K := by omega
  have h3K : 3 < K := by omega
  have mA := rLot_mem_simplex (K := K) (i := 0) (j := 2) (by norm_num) h0K h2K hx.le
  have mA' := rLot_mem_simplex (K := K) (i := 0) (j := 2) (by norm_num) h0K h2K hx'.le
  have mQe := rLot_mem_simplex (K := K) (i := 1) (j := 2) (by norm_num) h1K h2K hy.le
  have mQeG := rLot_mem_simplex (K := K) (i := 1) (j := 2) (by norm_num) h1K h2K hy'.le
  have mb := rLot_mem_simplex (K := K) (i := 1) (j := 2) (by norm_num) h1K h2K hp.le
  have mb' := rLot_mem_simplex (K := K) (i := 1) (j := 2) (by norm_num) h1K h2K hp'.le
  have md := rLot_mem_simplex (K := K) (i := 0) (j := 3) (by norm_num) h0K h3K hd.le
  have md' := rLot_mem_simplex (K := K) (i := 0) (j := 3) (by norm_num) h0K h3K hd'.le
  have reflI : ∀ z ∈ Simplex K, Indiff R z z := fun z hz =>
    have h := (hR.complete z hz z hz).elim id id
    ⟨h, h⟩
  have symI : ∀ {u v : Lot K}, Indiff R u v → Indiff R v u := fun h => ⟨h.2, h.1⟩
  have men1 : x * c = p * d :=
    menelaus hK hR mA hx hp hc hd (reflI _ mA) hQ hR3 hS
  have men2 : x' * c' = p' * d' :=
    menelaus hK hR mA' hx' hp' hc' hd' (reflI _ mA') hQ' hR3' hS'
  have hp_lt : p < y := by
    have h := spref_congr hR mA mb mQe mQe (symI hQ) (reflI _ mQe) hAD
    exact edge_ratio_lt hR (by norm_num) h2K hp hy h
  have hp'_gt : y' < p' := by
    have h := spref_congr hR mQeG mQeG mA' mb' (reflI _ mQeG) (symI hQ') hDA
    exact edge_ratio_lt hR (by norm_num) h2K hy' hp' h
  have hd_lt : d < d' := by
    have h := spref_congr hR mA md mA' md' (symI hS) (symI hS') hAA
    exact edge_ratio_lt hR (by norm_num) h3K hd hd' h
  have e1 : y' * x * c = y' * (p * d) := by rw [← men1]; ring
  have e2 : y * x' * c' = y * (p' * d') := by rw [mul_assoc, men2]
  rw [e1, e2]
  have s1 : y' * (p * d) < y' * (y * d) :=
    mul_lt_mul_of_pos_left (mul_lt_mul_of_pos_right hp_lt hd) hy'
  have s2 : y' * (y * d) < y * (p' * d) := by
    have : y' * (y * d) = y * (y' * d) := by ring
    rw [this]
    exact mul_lt_mul_of_pos_left (mul_lt_mul_of_pos_right hp'_gt hd) hy
  have s3 : y * (p' * d) < y * (p' * d') :=
    mul_lt_mul_of_pos_left (mul_lt_mul_of_pos_left hd_lt hp') hy
  linarith

end Odds
