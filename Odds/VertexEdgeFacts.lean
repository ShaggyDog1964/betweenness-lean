import Odds.Defs
import K4.FosdShift
import K4.VtxMem
import K4.RLotMem

namespace Odds

open K4

private lemma spref_of_shift' {K : ℕ} {R : Rel K} (hR : IsBetweennessPref R) {i j : ℕ}
    (hij : i < j) (hj : j < K) {p q : Lot K} (hp : p ∈ Simplex K) (hq : q ∈ Simplex K)
    {δ : ℝ} (hδ : 0 < δ) (heq : q = p + δ • (vtx K j - vtx K i)) : SPref R q p := by
  apply hR.strictMono q hq p hp
  rw [heq]
  exact strictFOSD_shift hij hj p hδ

/-- Base-free vertex comparisons for edge lotteries of any positive ratio `x`:
`vtx 2 ≻ rLot 0 2 x` and `rLot 1 3 x ≻ vtx 1`.
Sketch: copy the last two cases of `K4.vertex_facts` (file `K4/VertexFacts.lean`, including
its private helper `spref_of_shift`) with `2^c` replaced by `x`: `hR.strictMono` applied to
`K4.strictFOSD_shift` and the identities (funext, `split_ifs`, `field_simp; ring`)
`vtx 2 = rLot 0 2 x + (x/(x+1)) • (vtx 2 - vtx 0)` (shift `0 → 2`, `δ = x/(x+1) > 0`) and
`rLot 1 3 x = vtx 1 + (1/(x+1)) • (vtx 3 - vtx 1)` (shift `1 → 3`, `δ = 1/(x+1) > 0`).
Memberships: `K4.vtx_mem_simplex`, `K4.rLot_mem_simplex`. -/
theorem vertex_edge_facts {K : ℕ} (hK : 4 ≤ K) {R : Rel K} (hR : IsBetweennessPref R)
    {x : ℝ} (hx : 0 < x) :
    SPref R (vtx K 2) (rLot K 0 2 x) ∧ SPref R (rLot K 1 3 x) (vtx K 1) := by
  have hx1 : x + 1 ≠ 0 := by positivity
  refine ⟨?_, ?_⟩
  · refine spref_of_shift' hR (i := 0) (j := 2) (δ := x / (x + 1)) (by norm_num)
      (by omega) (rLot_mem_simplex (by norm_num) (by omega) (by omega) hx.le)
      (vtx_mem_simplex (by omega)) (by positivity) ?_
    funext k
    simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, vtx, rLot]
    split_ifs <;> first | omega | (field_simp; ring)
  · refine spref_of_shift' hR (i := 1) (j := 3) (δ := 1 / (x + 1)) (by norm_num)
      (by omega) (vtx_mem_simplex (by omega))
      (rLot_mem_simplex (by norm_num) (by omega) (by omega) hx.le) (by positivity) ?_
    funext k
    simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, vtx, rLot]
    split_ifs <;> first | omega | (field_simp; ring)

end Odds
