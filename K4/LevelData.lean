import K4.Defs
import K4.EdgeIndiff
import K4.VertexFacts
import K4.SprefTrans
import K4.VtxMem

namespace K4

/-- A level strictly between `vtx 1` and `vtx 2` has indifferent points on the three edges
`(1,2)`, `(1,3)`, `(0,3)`.
Sketch: three applications of `exists_edge_indiff`:
edge `(1,2)`: `h2`, `h1` directly;
edge `(1,3)`: `SPref (vtx 3) l` from `vtx 3 ≻ vtx 2` (`vertex_facts`) and `h2` by
`spref_trans`; and `h1`;
edge `(0,3)`: `SPref (vtx 3) l` as above; `SPref l (vtx 0)` from `h1` and `vtx 1 ≻ vtx 0`
(`vertex_facts`) by `spref_trans`. -/
theorem level_data {K : ℕ} (hK : 4 ≤ K) {R : Rel K} (hR : IsBetweennessPref R) {l : Lot K}
    (hl : l ∈ Simplex K) (h2 : SPref R (vtx K 2) l) (h1 : SPref R l (vtx K 1)) :
    ∃ b c d : ℝ, 0 < b ∧ 0 < c ∧ 0 < d ∧ Indiff R (rLot K 1 2 b) l ∧
      Indiff R (rLot K 1 3 c) l ∧ Indiff R (rLot K 0 3 d) l := by
  obtain ⟨h32, h10, -, -⟩ := vertex_facts hK hR
  have m0 : vtx K 0 ∈ Simplex K := vtx_mem_simplex (by omega)
  have m1 : vtx K 1 ∈ Simplex K := vtx_mem_simplex (by omega)
  have m2 : vtx K 2 ∈ Simplex K := vtx_mem_simplex (by omega)
  have m3 : vtx K 3 ∈ Simplex K := vtx_mem_simplex (by omega)
  have h3 : SPref R (vtx K 3) l := K4.spref_trans hR m3 m2 hl h32 h2
  have h0 : SPref R l (vtx K 0) := K4.spref_trans hR hl m1 m0 h1 h10
  obtain ⟨b, hb, hbI⟩ := exists_edge_indiff hR (i := 1) (j := 2) (by norm_num) (by omega) hl h2 h1
  obtain ⟨c, hc, hcI⟩ := exists_edge_indiff hR (i := 1) (j := 3) (by norm_num) (by omega) hl h3 h1
  obtain ⟨d, hd, hdI⟩ := exists_edge_indiff hR (i := 0) (j := 3) (by norm_num) (by omega) hl h3 h0
  exact ⟨b, c, d, hb, hc, hd, hbI, hcI, hdI⟩

end K4
