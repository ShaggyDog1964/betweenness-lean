import Odds.Defs
import Odds.EdgeLotsBEq
import Odds.SprefFactsB
import Odds.VertexEdgeFacts
import Odds.BlockRiseReal
import Odds.BudgetB
import K4.LevelData
import K4.EdgeRatioLt
import K4.SprefCongr
import K4.SprefTrans
import K4.RLotMem
import K4.VtxMem

namespace Odds

open K4

/-- NON-REPRESENTABILITY of `X_J^b` for every real `b > 1`.
Sketch: follow `K4.racetrack_not_representable` (file `K4/NotRepresentable.lean`) line by
line, with these substitutions.
* Rewrite every family lottery as an `rLot` via `edge_lotsB_eq_rLot` (ratio `b^c`, positive
  since `b > 0`); memberships by `K4.rLot_mem_simplex`.
* `racetrackB_spref_facts` replaces `K4.racetrack_spref_facts`.
* The base-dependent vertex facts come from `vertex_edge_facts` with `x = b^c`:
  `vtx 2 ≻ A` and `R[v0 + Jβ] ≻ vtx 1`. Then `K4.level_data` (needs `vtx 2 ≻ A` and
  `A ≻ vtx 1`, the latter by `K4.spref_trans` through `R[v0+Jβ]`) gives positive ratios
  `(p, c, d)` at each `A_i = P[a_i]` and `A'_i = P[a_i + 4]`; choose them as functions of
  `i` (`choose` on `∀ i, ∃ x, i < J → …`, exactly as in K4).
* `hblock`: `block_rise_real` with `x = b^(a_i)`, `x' = b^(a_i+4)`, `y = b^(d_i)`,
  `y' = b^(d_i + G)`, `G = parG J = 4J+4`, gives
  `b^(d_i+G) * b^(a_i) * c < b^(d_i) * b^(a_i+4) * c'`. With `pow_add` cancel the positive
  `b^(d_i) * b^(a_i)` to get `b^G c < b^4 c'`; `b^G = b^4 * b^β` (`parG J = 4 + parBeta J`)
  then gives `b^β c < c'` after cancelling `b^4 > 0`.
* `hgap`, `hstart`, `hend`: exactly as in K4 (`K4.spref_congr` + `K4.edge_ratio_lt` on edge
  `(1,3)`), with `2^v0` replaced by `b^v0` etc.
* Close with `budget_contradictionB b (by linarith) J (parBeta J) (parV0 J) hJ cA cA'`. -/
theorem racetrackB_not_representable {K : ℕ} (hK : 4 ≤ K) {b : ℝ} (hb : 1 < b) (J : ℕ)
    (hJ : 1 ≤ J) : ¬ Representable (racetrackListB b K J) := by
  intro hRep
  obtain ⟨R, hR, h0, hblk, hgap⟩ := racetrackB_spref_facts b J hJ hRep
  have hb0 : 0 < b := by linarith
  have eP : ∀ c : ℕ, lotPB b K c = rLot K 0 2 (b ^ c) := fun c => (edge_lotsB_eq_rLot b K c).1
  have eQ : ∀ c : ℕ, lotQB b K c = rLot K 1 2 (b ^ c) := fun c => (edge_lotsB_eq_rLot b K c).2.1
  have eR : ∀ c : ℕ, lotRB b K c = rLot K 1 3 (b ^ c) := fun c => (edge_lotsB_eq_rLot b K c).2.2
  simp only [eP, eQ, eR] at h0 hblk hgap
  have h0K : 0 < K := by omega
  have h1K : 1 < K := by omega
  have h2K : 2 < K := by omega
  have h3K : 3 < K := by omega
  have bpos : ∀ c : ℕ, (0 : ℝ) < b ^ c := fun c => pow_pos hb0 c
  have memP : ∀ c : ℕ, rLot K 0 2 (b ^ c) ∈ Simplex K := fun c =>
    rLot_mem_simplex (by norm_num) h0K h2K (bpos c).le
  have memR : ∀ c : ℕ, rLot K 1 3 (b ^ c) ∈ Simplex K := fun c =>
    rLot_mem_simplex (by norm_num) h1K h3K (bpos c).le
  have mv1 : vtx K 1 ∈ Simplex K := vtx_mem_simplex (by omega)
  have lvl : ∀ c : ℕ, SPref R (rLot K 0 2 (b ^ c)) (rLot K 1 3 (b ^ (parV0 J + J * parBeta J))) →
      ∃ p c' d : ℝ, 0 < p ∧ 0 < c' ∧ 0 < d ∧ Indiff R (rLot K 1 2 p) (rLot K 0 2 (b ^ c)) ∧
        Indiff R (rLot K 1 3 c') (rLot K 0 2 (b ^ c)) ∧
        Indiff R (rLot K 0 3 d) (rLot K 0 2 (b ^ c)) := by
    intro c hc
    exact level_data hK hR (memP c) (vertex_edge_facts hK hR (bpos c)).1
      (K4.spref_trans hR (memP c) (memR _) mv1 hc
        (vertex_edge_facts hK hR (bpos (parV0 J + J * parBeta J))).2)
  have ex : ∀ i : ℕ, ∃ x : ℝ × ℝ × ℝ × ℝ × ℝ × ℝ, i < J →
      (0 < x.1 ∧ 0 < x.2.1 ∧ 0 < x.2.2.1 ∧
        Indiff R (rLot K 1 2 x.1) (rLot K 0 2 (b ^ expA J i)) ∧
        Indiff R (rLot K 1 3 x.2.1) (rLot K 0 2 (b ^ expA J i)) ∧
        Indiff R (rLot K 0 3 x.2.2.1) (rLot K 0 2 (b ^ expA J i))) ∧
      (0 < x.2.2.2.1 ∧ 0 < x.2.2.2.2.1 ∧ 0 < x.2.2.2.2.2 ∧
        Indiff R (rLot K 1 2 x.2.2.2.1) (rLot K 0 2 (b ^ (expA J i + 4))) ∧
        Indiff R (rLot K 1 3 x.2.2.2.2.1) (rLot K 0 2 (b ^ (expA J i + 4))) ∧
        Indiff R (rLot K 0 3 x.2.2.2.2.2) (rLot K 0 2 (b ^ (expA J i + 4)))) := by
    intro i
    by_cases hi : i < J
    · obtain ⟨-, -, -, h4, h5⟩ := hblk i hi
      obtain ⟨b1, c1, d1, p1, p2, p3, i1, i2, i3⟩ := lvl _ h5
      obtain ⟨b2, c2, d2, q1, q2, q3, j1, j2, j3⟩ := lvl _ h4
      exact ⟨(b1, c1, d1, b2, c2, d2), fun _ =>
        ⟨⟨p1, p2, p3, i1, i2, i3⟩, ⟨q1, q2, q3, j1, j2, j3⟩⟩⟩
    · exact ⟨(1, 1, 1, 1, 1, 1), fun h => absurd h hi⟩
  choose x hx using ex
  set cA : ℕ → ℝ := fun i => if i < J then (x i).2.1 else 1 with hcA
  set cA' : ℕ → ℝ := fun i => (x i).2.2.2.2.1 with hcA'
  have symI : ∀ {p q : Lot K}, Indiff R p q → Indiff R q p := fun h => ⟨h.2, h.1⟩
  have cAeq : ∀ i, i < J → cA i = (x i).2.1 := fun i hi => by simp [hcA, hi]
  have mr13 : ∀ {y : ℝ}, 0 < y → rLot K 1 3 y ∈ Simplex K := fun hy =>
    rLot_mem_simplex (by norm_num) h1K h3K hy.le
  apply budget_contradictionB b hb0 J (parBeta J) (parV0 J) hJ cA cA'
  · intro i
    by_cases hi : i < J
    · rw [cAeq i hi]; exact (hx i hi).1.2.1
    · simp [hcA, hi]
  · intro i hi
    obtain ⟨⟨p1, p2, p3, i1, i2, i3⟩, ⟨q1, q2, q3, j1, j2, j3⟩⟩ := hx i hi
    obtain ⟨hAD, hDA, hAA, -, -⟩ := hblk i hi
    have key := block_rise_real hK hR (bpos _) (bpos _) (bpos _) (bpos _) p1 p2 p3 q1 q2 q3
      hAD hDA hAA i1 i2 i3 j1 j2 j3
    rw [cAeq i hi]
    show b ^ parBeta J * (x i).2.1 < (x i).2.2.2.2.1
    have eG : parG J = 4 + parBeta J := by simp only [parG, parBeta]; omega
    rw [eG, pow_add, pow_add, pow_add] at key
    have hd := bpos (expD J i)
    have ha := bpos (expA J i)
    have h4 := bpos 4
    have hpos : 0 < b ^ expD J i * b ^ expA J i * b ^ 4 := by positivity
    have e1 : b ^ expD J i * (b ^ 4 * b ^ parBeta J) * b ^ expA J i * (x i).2.1 =
        (b ^ expD J i * b ^ expA J i * b ^ 4) * (b ^ parBeta J * (x i).2.1) := by ring
    have e2 : b ^ expD J i * (b ^ expA J i * b ^ 4) * (x i).2.2.2.2.1 =
        (b ^ expD J i * b ^ expA J i * b ^ 4) * (x i).2.2.2.2.1 := by ring
    rw [e1, e2] at key
    exact lt_of_mul_lt_mul_left key hpos.le
  · intro i hi
    have hg := hgap i hi
    obtain ⟨-, ⟨-, q2, -, -, j2, -⟩⟩ := hx i (by omega)
    obtain ⟨⟨-, p2, -, -, i2, -⟩, -⟩ := hx (i + 1) hi
    have h := spref_congr hR (memP _) (mr13 q2) (memP _) (mr13 p2) (symI j2) (symI i2) hg
    rw [cAeq (i + 1) hi]
    exact edge_ratio_lt hR (by norm_num) h3K q2 p2 h
  · obtain ⟨⟨-, p2, -, -, i2, -⟩, -⟩ := hx 0 (by omega)
    have mR := memR (parV0 J)
    have reflR : Indiff R (rLot K 1 3 (b ^ parV0 J)) (rLot K 1 3 (b ^ parV0 J)) :=
      have h := (hR.complete _ mR _ mR).elim id id
      ⟨h, h⟩
    have h := spref_congr hR mR mR (memP _) (mr13 p2) reflR (symI i2) h0
    rw [cAeq 0 (by omega)]
    exact edge_ratio_lt hR (by norm_num) h3K (bpos _) p2 h
  · obtain ⟨-, ⟨-, q2, -, -, j2, -⟩⟩ := hx (J - 1) (by omega)
    obtain ⟨-, -, -, h4, -⟩ := hblk (J - 1) (by omega)
    have mR := memR (parV0 J + J * parBeta J)
    have reflR : Indiff R (rLot K 1 3 (b ^ (parV0 J + J * parBeta J)))
        (rLot K 1 3 (b ^ (parV0 J + J * parBeta J))) :=
      have h := (hR.complete _ mR _ mR).elim id id
      ⟨h, h⟩
    have h := spref_congr hR (memP _) (mr13 q2) mR mR (symI j2) reflR h4
    exact edge_ratio_lt hR (by norm_num) h3K q2 (bpos _) h

end Odds
