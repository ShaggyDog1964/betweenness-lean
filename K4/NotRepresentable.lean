import K4.Defs
import K4.SprefFacts
import K4.LevelData
import K4.BlockRise
import K4.Budget
import K4.EdgeRatioLt
import K4.SprefCongr
import K4.SprefTrans
import K4.VertexFacts
import K4.EdgeLotsEq
import K4.RLotMem

namespace K4

/-- NON-REPRESENTABILITY of `X_J` (the racetrack budget argument).
Sketch. Get `R` and the comparisons from `racetrack_spref_facts`. For each `b < J` the
levels `A_b = lotP (expA J b)` and `A'_b = lotP (expA J b + 4)` satisfy
`SPref (vtx 2) A` (`vertex_facts`) and `SPref A (vtx 1)` (via `A ≻ R[v0+Jβ] ≻ vtx 1`,
`spref_trans`, `vertex_facts`). `level_data` gives ratios; choose them as functions of `b`
(state `∀ b, ∃ …, b < J → …` and use `choose`, or `Classical.choose` under `dite`):
`cA b`, `cA' b` are the `(1,3)`-edge ratios at `A_b`, `A'_b`.
* `hblock`: `block_rise` with `a = expA J b`, `e = expD J b`, `G = parG J = 4J+4` gives
  `2^(4J+4) cA b < 16 cA' b`, i.e. `2^(parBeta J) cA b < cA' b`.
* `hgap`: `SPref A'_b A_{b+1}` transported by `spref_congr` to
  `SPref (rLot 1 3 (cA' b)) (rLot 1 3 (cA (b+1)))`, then `edge_ratio_lt`.
* `hstart`: `SPref (lotR v0) A_0`, `lotR v0 = rLot 1 3 (2^v0)` (`edge_lots_eq_rLot`),
  transport, `edge_ratio_lt`: `2^v0 < cA 0`.
* `hend`: `SPref A'_{J-1} (lotR (v0 + Jβ))` similarly gives `cA' (J-1) < 2^(v0 + Jβ)`.
`budget_contradiction (β := parBeta J) (v0 := parV0 J)` closes the goal.
(Mathematically: with `ν` the log of the `(1,3)` ratio, Menelaus `α + ν = σ + ω` forces
`ν` to rise by more than `G - g = β` across each block and never fall, but the two `R`
lotteries cap the total rise at `Jβ`.) -/
theorem racetrack_not_representable {K : ℕ} (hK : 4 ≤ K) (J : ℕ) (hJ : 1 ≤ J) :
    ¬ Representable (racetrackList K J) := by
  intro hRep
  obtain ⟨R, hR, h0, hblk, hgap⟩ := racetrack_spref_facts J hJ hRep
  obtain ⟨-, -, hv2, hv1⟩ := vertex_facts hK hR
  have h0K : 0 < K := by omega
  have h1K : 1 < K := by omega
  have h2K : 2 < K := by omega
  have h3K : 3 < K := by omega
  have memP : ∀ c : ℕ, lotP K c ∈ Simplex K := fun c => by
    rw [(edge_lots_eq_rLot K c).1]
    exact rLot_mem_simplex (by norm_num) h0K h2K (by positivity)
  have memR : ∀ c : ℕ, lotR K c ∈ Simplex K := fun c => by
    rw [(edge_lots_eq_rLot K c).2.2]
    exact rLot_mem_simplex (by norm_num) h1K h3K (by positivity)
  have mv1 : vtx K 1 ∈ Simplex K := vtx_mem_simplex (by omega)
  have lvl : ∀ c : ℕ, SPref R (lotP K c) (lotR K (parV0 J + J * parBeta J)) →
      ∃ b c' d : ℝ, 0 < b ∧ 0 < c' ∧ 0 < d ∧ Indiff R (rLot K 1 2 b) (lotP K c) ∧
        Indiff R (rLot K 1 3 c') (lotP K c) ∧ Indiff R (rLot K 0 3 d) (lotP K c) := by
    intro c hc
    exact level_data hK hR (memP c) (hv2 c)
      (K4.spref_trans hR (memP c) (memR _) mv1 hc (hv1 _))
  have ex : ∀ b : ℕ, ∃ x : ℝ × ℝ × ℝ × ℝ × ℝ × ℝ, b < J →
      (0 < x.1 ∧ 0 < x.2.1 ∧ 0 < x.2.2.1 ∧
        Indiff R (rLot K 1 2 x.1) (lotP K (expA J b)) ∧
        Indiff R (rLot K 1 3 x.2.1) (lotP K (expA J b)) ∧
        Indiff R (rLot K 0 3 x.2.2.1) (lotP K (expA J b))) ∧
      (0 < x.2.2.2.1 ∧ 0 < x.2.2.2.2.1 ∧ 0 < x.2.2.2.2.2 ∧
        Indiff R (rLot K 1 2 x.2.2.2.1) (lotP K (expA J b + 4)) ∧
        Indiff R (rLot K 1 3 x.2.2.2.2.1) (lotP K (expA J b + 4)) ∧
        Indiff R (rLot K 0 3 x.2.2.2.2.2) (lotP K (expA J b + 4))) := by
    intro b
    by_cases hb : b < J
    · obtain ⟨-, -, -, h4, h5⟩ := hblk b hb
      obtain ⟨b1, c1, d1, p1, p2, p3, i1, i2, i3⟩ := lvl _ h5
      obtain ⟨b2, c2, d2, q1, q2, q3, j1, j2, j3⟩ := lvl _ h4
      exact ⟨(b1, c1, d1, b2, c2, d2), fun _ =>
        ⟨⟨p1, p2, p3, i1, i2, i3⟩, ⟨q1, q2, q3, j1, j2, j3⟩⟩⟩
    · exact ⟨(1, 1, 1, 1, 1, 1), fun h => absurd h hb⟩
  choose x hx using ex
  set cA : ℕ → ℝ := fun b => if b < J then (x b).2.1 else 1 with hcA
  set cA' : ℕ → ℝ := fun b => (x b).2.2.2.2.1 with hcA'
  have symI : ∀ {p q : Lot K}, Indiff R p q → Indiff R q p := fun h => ⟨h.2, h.1⟩
  have cAeq : ∀ b, b < J → cA b = (x b).2.1 := fun b hb => by simp [hcA, hb]
  have mr13 : ∀ {y : ℝ}, 0 < y → rLot K 1 3 y ∈ Simplex K := fun hy =>
    rLot_mem_simplex (by norm_num) h1K h3K hy.le
  apply budget_contradiction J (parBeta J) (parV0 J) hJ cA cA'
  · intro i
    by_cases hi : i < J
    · rw [cAeq i hi]; exact (hx i hi).1.2.1
    · simp [hcA, hi]
  · intro i hi
    obtain ⟨⟨p1, p2, p3, i1, i2, i3⟩, ⟨q1, q2, q3, j1, j2, j3⟩⟩ := hx i hi
    obtain ⟨hAD, hDA, hAA, -, -⟩ := hblk i hi
    have := block_rise hK hR (expA J i) (expD J i) (parG J) p1 p2 p3 q1 q2 q3
      hAD hDA hAA i1 i2 i3 j1 j2 j3
    rw [cAeq i hi]
    have e : (2 : ℝ) ^ parG J = 2 ^ parBeta J * 16 := by
      simp only [parG, parBeta, pow_add]; norm_num
    rw [e] at this
    show (2 : ℝ) ^ parBeta J * (x i).2.1 < (x i).2.2.2.2.1
    nlinarith
  · intro i hi
    have hg := hgap i hi
    obtain ⟨-, ⟨-, q2, -, -, j2, -⟩⟩ := hx i (by omega)
    obtain ⟨⟨-, p2, -, -, i2, -⟩, -⟩ := hx (i + 1) hi
    have h := spref_congr hR (memP _) (mr13 q2) (memP _) (mr13 p2) (symI j2) (symI i2) hg
    rw [cAeq (i + 1) hi]
    exact edge_ratio_lt hR (by norm_num) h3K q2 p2 h
  · obtain ⟨⟨-, p2, -, -, i2, -⟩, -⟩ := hx 0 (by omega)
    have hpos : (0 : ℝ) < 2 ^ parV0 J := by positivity
    have mR := memR (parV0 J)
    rw [(edge_lots_eq_rLot K (parV0 J)).2.2] at h0 mR
    have reflR : Indiff R (rLot K 1 3 ((2 : ℝ) ^ parV0 J)) (rLot K 1 3 ((2 : ℝ) ^ parV0 J)) :=
      have h := (hR.complete _ mR _ mR).elim id id
      ⟨h, h⟩
    have h := spref_congr hR mR mR (memP _) (mr13 p2) reflR (symI i2) h0
    rw [cAeq 0 (by omega)]
    exact edge_ratio_lt hR (by norm_num) h3K hpos p2 h
  · obtain ⟨-, ⟨-, q2, -, -, j2, -⟩⟩ := hx (J - 1) (by omega)
    obtain ⟨-, -, -, h4, -⟩ := hblk (J - 1) (by omega)
    have hpos : (0 : ℝ) < 2 ^ (parV0 J + J * parBeta J) := by positivity
    have mR := memR (parV0 J + J * parBeta J)
    rw [(edge_lots_eq_rLot K (parV0 J + J * parBeta J)).2.2] at h4 mR
    have reflR : Indiff R (rLot K 1 3 ((2 : ℝ) ^ (parV0 J + J * parBeta J)))
        (rLot K 1 3 ((2 : ℝ) ^ (parV0 J + J * parBeta J))) :=
      have h := (hR.complete _ mR _ mR).elim id id
      ⟨h, h⟩
    have h := spref_congr hR (memP _) (mr13 q2) mR mR (symI j2) reflR h4
    exact edge_ratio_lt hR (by norm_num) h3K q2 hpos h

end K4
