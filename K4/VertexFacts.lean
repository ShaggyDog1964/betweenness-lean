import K4.Defs
import K4.FosdShift
import K4.VtxMem
import K4.RLotMem
import K4.EdgeLotsEq

namespace K4

private lemma spref_of_shift {K : ℕ} {R : Rel K} (hR : IsBetweennessPref R) {i j : ℕ}
    (hij : i < j) (hj : j < K) {p q : Lot K} (hp : p ∈ Simplex K) (hq : q ∈ Simplex K)
    {δ : ℝ} (hδ : 0 < δ) (heq : q = p + δ • (vtx K j - vtx K i)) : SPref R q p := by
  apply hR.strictMono q hq p hp
  rw [heq]
  exact strictFOSD_shift hij hj p hδ

/-- Vertex comparisons forced by strict FOSD.
Sketch: each is `hR.strictMono` applied to a `strictFOSD_shift` identity (funext):
`vtx 3 = vtx 2 + 1 • (vtx 3 - vtx 2)`; `vtx 1 = vtx 0 + 1 • (vtx 1 - vtx 0)`;
`vtx 2 = lotP c + (2^c/(2^c+1)) • (vtx 2 - vtx 0)`;
`lotR c = vtx 1 + (1/(2^c+1)) • (vtx 3 - vtx 1)`.
Memberships: `vtx_mem_simplex`, `rLot_mem_simplex` via `edge_lots_eq_rLot`. -/
theorem vertex_facts {K : ℕ} (hK : 4 ≤ K) {R : Rel K} (hR : IsBetweennessPref R) :
    SPref R (vtx K 3) (vtx K 2) ∧ SPref R (vtx K 1) (vtx K 0) ∧
      (∀ c : ℕ, SPref R (vtx K 2) (lotP K c)) ∧ (∀ c : ℕ, SPref R (lotR K c) (vtx K 1)) := by
  refine ⟨?_, ?_, fun c => ?_, fun c => ?_⟩
  · refine spref_of_shift hR (i := 2) (j := 3) (by norm_num) (by omega)
      (vtx_mem_simplex (by omega)) (vtx_mem_simplex (by omega)) one_pos ?_
    funext k
    simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, vtx]
    split_ifs <;> first | omega | norm_num
  · refine spref_of_shift hR (i := 0) (j := 1) (by norm_num) (by omega)
      (vtx_mem_simplex (by omega)) (vtx_mem_simplex (by omega)) one_pos ?_
    funext k
    simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, vtx]
    split_ifs <;> first | omega | norm_num
  · have hx : (0 : ℝ) < 2 ^ c := by positivity
    have hx1 : (2 : ℝ) ^ c + 1 ≠ 0 := by positivity
    rw [(edge_lots_eq_rLot K c).1]
    refine spref_of_shift hR (i := 0) (j := 2) (δ := 2 ^ c / (2 ^ c + 1)) (by norm_num)
      (by omega) (rLot_mem_simplex (by norm_num) (by omega) (by omega) hx.le)
      (vtx_mem_simplex (by omega)) (by positivity) ?_
    funext k
    simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, vtx, rLot]
    split_ifs <;> first | omega | (field_simp; ring)
  · have hx : (0 : ℝ) < 2 ^ c := by positivity
    have hx1 : (2 : ℝ) ^ c + 1 ≠ 0 := by positivity
    rw [(edge_lots_eq_rLot K c).2.2]
    refine spref_of_shift hR (i := 1) (j := 3) (δ := 1 / (2 ^ c + 1)) (by norm_num)
      (by omega) (vtx_mem_simplex (by omega))
      (rLot_mem_simplex (by norm_num) (by omega) (by omega) hx.le) (by positivity) ?_
    funext k
    simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, vtx, rLot]
    split_ifs <;> first | omega | (field_simp; ring)

end K4
