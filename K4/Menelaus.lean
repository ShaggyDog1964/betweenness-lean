import K4.Defs
import K4.FosdShift
import K4.RLotMem
import K4.MixMem

namespace K4

/-- Menelaus lemma. If the four edge points `P = rLot 0 2 a`, `Q = rLot 1 2 b`,
`R' = rLot 1 3 c`, `S = rLot 0 3 d` (all ratios positive) are all indifferent to a common
level `l`, then `a * c = b * d`.
Sketch. Put `y = b/c`, `w = (a + y)/(d + 1)`, `N = a + b + 1 + y` (so `N = b+1+w(d+1)`).
`M1 = mix t1 P R'` with `t1 = (a+1)/N` equals `(a, b, 1, y, 0, …)/N`; `M2 = mix t2 Q S` with
`t2 = (b+1)/N` equals `(w d, b, 1, w, 0, …)/N` (funext + `field_simp`; `t1, t2 ∈ (0,1)`).
Hence `M1 = M2 + (δ/N) • (vtx 3 - vtx 0)` with `δ = y - w`.
`P ∼ R'` and `Q ∼ S` (through `l`, `hR.trans`), so `hR.btw_indiff` gives `M1 ∼ P ∼ l` and
`M2 ∼ Q ∼ l`, hence `M1 ∼ M2`. If `δ > 0`, `strictFOSD_shift` (0 < 3 < K) and
`hR.strictMono` give `SPref R M1 M2`, a contradiction; if `δ < 0` symmetrically
`SPref R M2 M1`. So `δ = 0`, i.e. `y d = a`, i.e. `b d = a c`.
Memberships: `rLot_mem_simplex`, `mix_mem_simplex`. -/
theorem menelaus {K : ℕ} (hK : 4 ≤ K) {R : Rel K} (hR : IsBetweennessPref R) {l : Lot K}
    (hl : l ∈ Simplex K) {a b c d : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (hP : Indiff R (rLot K 0 2 a) l) (hQ : Indiff R (rLot K 1 2 b) l)
    (hRl : Indiff R (rLot K 1 3 c) l) (hS : Indiff R (rLot K 0 3 d) l) :
    a * c = b * d := by
  have h0K : 0 < K := by omega
  have h1K : 1 < K := by omega
  have h2K : 2 < K := by omega
  have h3K : 3 < K := by omega
  have hPm : rLot K 0 2 a ∈ Simplex K := rLot_mem_simplex (by norm_num) h0K h2K ha.le
  have hQm : rLot K 1 2 b ∈ Simplex K := rLot_mem_simplex (by norm_num) h1K h2K hb.le
  have hRm : rLot K 1 3 c ∈ Simplex K := rLot_mem_simplex (by norm_num) h1K h3K hc.le
  have hSm : rLot K 0 3 d ∈ Simplex K := rLot_mem_simplex (by norm_num) h0K h3K hd.le
  set y : ℝ := b / c with hy
  set w : ℝ := (a + y) / (d + 1) with hw
  set N : ℝ := a + b + 1 + y with hN
  have hy0 : 0 < y := div_pos hb hc
  have hw0 : 0 < w := div_pos (by linarith) (by linarith)
  have hN0 : 0 < N := by rw [hN]; linarith
  set t1 : ℝ := (a + 1) / N with ht1
  set t2 : ℝ := (b + 1) / N with ht2
  have ht1I : t1 ∈ Set.Ioo (0 : ℝ) 1 := by
    refine ⟨div_pos (by linarith) hN0, ?_⟩
    rw [ht1, div_lt_one hN0, hN]; linarith
  have ht2I : t2 ∈ Set.Ioo (0 : ℝ) 1 := by
    refine ⟨div_pos (by linarith) hN0, ?_⟩
    rw [ht2, div_lt_one hN0, hN]; linarith
  set M1 := mix t1 (rLot K 0 2 a) (rLot K 1 3 c) with hM1
  set M2 := mix t2 (rLot K 1 2 b) (rLot K 0 3 d) with hM2
  have hM1m : M1 ∈ Simplex K := mix_mem_simplex hPm hRm ht1I.1.le ht1I.2.le
  have hM2m : M2 ∈ Simplex K := mix_mem_simplex hQm hSm ht2I.1.le ht2I.2.le
  set δ : ℝ := (y - w) / N with hδ
  have hc1 : c + 1 ≠ 0 := by linarith
  have hd1 : d + 1 ≠ 0 := by linarith
  have ha1 : a + 1 ≠ 0 := by linarith
  have hb1 : b + 1 ≠ 0 := by linarith
  have hcne : c ≠ 0 := hc.ne'
  have hNne : N ≠ 0 := hN0.ne'
  have hshift : M1 = M2 + δ • (vtx K 3 - vtx K 0) := by
    funext k
    simp only [hM1, hM2, mix, rLot, vtx, Pi.add_apply, Pi.smul_apply, Pi.sub_apply,
      smul_eq_mul]
    by_cases k0 : k.val = 0
    · simp only [k0]
      norm_num
      rw [hδ, ht1, ht2, hw, hN, hy]
      field_simp
      ring
    by_cases k1 : k.val = 1
    · simp only [k1]
      norm_num
      rw [ht1, ht2, hN, hy]
      field_simp
      ring
    by_cases k2 : k.val = 2
    · simp only [k2]
      norm_num
      rw [ht1, ht2, hN, hy]
      field_simp
    by_cases k3 : k.val = 3
    · simp only [k3]
      norm_num
      rw [hδ, ht1, ht2, hw, hN, hy]
      field_simp
      ring
    · simp [k0, k1, k2, k3]
  have hshift' : M2 = M1 + (-δ) • (vtx K 3 - vtx K 0) := by
    rw [hshift]
    funext k
    simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    ring
  -- indifferences
  have hPR : Indiff R (rLot K 0 2 a) (rLot K 1 3 c) :=
    ⟨hR.trans _ hPm _ hl _ hRm hP.1 hRl.2, hR.trans _ hRm _ hl _ hPm hRl.1 hP.2⟩
  have hQS : Indiff R (rLot K 1 2 b) (rLot K 0 3 d) :=
    ⟨hR.trans _ hQm _ hl _ hSm hQ.1 hS.2, hR.trans _ hSm _ hl _ hQm hS.1 hQ.2⟩
  have hM1P : Indiff R M1 (rLot K 0 2 a) := hR.btw_indiff _ hPm _ hRm t1 ht1I hPR
  have hM2Q : Indiff R M2 (rLot K 1 2 b) := hR.btw_indiff _ hQm _ hSm t2 ht2I hQS
  have hM1l : Indiff R M1 l :=
    ⟨hR.trans _ hM1m _ hPm _ hl hM1P.1 hP.1, hR.trans _ hl _ hPm _ hM1m hP.2 hM1P.2⟩
  have hM2l : Indiff R M2 l :=
    ⟨hR.trans _ hM2m _ hQm _ hl hM2Q.1 hQ.1, hR.trans _ hl _ hQm _ hM2m hQ.2 hM2Q.2⟩
  have h12 : R M1 M2 := hR.trans _ hM1m _ hl _ hM2m hM1l.1 hM2l.2
  have h21 : R M2 M1 := hR.trans _ hM2m _ hl _ hM1m hM2l.1 hM1l.2
  have hδ0 : δ = 0 := by
    rcases lt_trichotomy δ 0 with hneg | hz | hpos
    · exfalso
      have hF : StrictFOSD M2 M1 := by
        rw [hshift']
        exact strictFOSD_shift (by norm_num) h3K M1 (by linarith)
      have hF' : StrictFOSD M2 M1 := hF
      have := hR.strictMono _ hM2m _ hM1m hF'
      exact this.2 h12
    · exact hz
    · exfalso
      have hF : StrictFOSD M1 M2 := by
        rw [hshift]
        exact strictFOSD_shift (by norm_num) h3K M2 hpos
      have := hR.strictMono _ hM1m _ hM2m hF
      exact this.2 h21
  have hyw : y = w := by
    rw [hδ, div_eq_zero_iff] at hδ0
    rcases hδ0 with h | h
    · linarith
    · exact absurd h hNne
  rw [hw, hy] at hyw
  field_simp at hyw
  linarith

end K4
