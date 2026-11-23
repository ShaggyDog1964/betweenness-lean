import Q2CL.Defs
import Q2CL.ContourConvex

namespace Q2CL

open K4 Filter Topology

private lemma lh_mem {p q : Lot 4} (hp : p ∈ Simplex 4) (hq : q ∈ Simplex 4) {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) : a • p + b • q ∈ Simplex 4 := by
  refine ⟨fun i => ?_, ?_⟩
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    exact add_nonneg (mul_nonneg ha (hp.1 i)) (mul_nonneg hb (hq.1 i))
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hp.2, hq.2]
    linarith

private lemma lh_mix_mem {p q : Lot 4} (hp : p ∈ Simplex 4) (hq : q ∈ Simplex 4) {t : ℝ}
    (h0 : 0 ≤ t) (h1 : t ≤ 1) : mix t p q ∈ Simplex 4 :=
  lh_mem hp hq h0 (by linarith) (by ring)

private lemma lh_between {R : Rel 4} (hR : IsBetweennessPref R) {p q : Lot 4}
    (hp : p ∈ Simplex 4) (hq : q ∈ Simplex 4) {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1)
    (hpq : R p q) : R (mix t p q) q ∧ R p (mix t p q) := by
  have hm : mix t p q ∈ Simplex 4 := lh_mix_mem hp hq ht.1.le ht.2.le
  by_cases hqp : R q p
  · have h := hR.btw_indiff p hp q hq t ht ⟨hpq, hqp⟩
    exact ⟨hR.trans _ hm _ hp _ hq h.1 hpq, h.2⟩
  · have h := hR.btw_strict p hp q hq t ht ⟨hpq, hqp⟩
    exact ⟨h.2.1, h.1.1⟩

private lemma lh_swap (t : ℝ) (p q : Lot 4) : mix t p q = mix (1 - t) q p := by
  ext i; simp only [mix, Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring

private lemma lh_dot_mix (W p q : Lot 4) (t : ℝ) :
    dot W (mix t p q) = t * dot W p + (1 - t) * dot W q := by
  simp only [dot, mix, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Fin.sum_univ_four]; ring

private lemma lh_upper_convex {R : Rel 4} (hR : IsBetweennessPref R) {r p q : Lot 4}
    (hr : r ∈ Simplex 4) (hp : p ∈ Simplex 4) (hq : q ∈ Simplex 4)
    (hpr : SPref R p r) (hqr : SPref R q r) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    SPref R (mix t p q) r := by
  rcases ht0.eq_or_lt with rfl | ht0'
  · simpa [mix] using hqr
  rcases ht1.eq_or_lt with rfl | ht1'
  · simpa [mix] using hpr
  have hm := lh_mix_mem hp hq ht0 ht1
  have hat : t ∈ Set.Ioo (0 : ℝ) 1 := ⟨ht0', ht1'⟩
  rcases hR.complete p hp q hq with hpq | hqp
  · have h := (lh_between hR hp hq hat hpq).1
    exact ⟨hR.trans _ hm _ hq _ hr h hqr.1, fun h' => hqr.2 (hR.trans _ hr _ hm _ hq h' h)⟩
  · have hat' : 1 - t ∈ Set.Ioo (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
    rw [lh_swap] at hm ⊢
    have h := (lh_between hR hq hp hat' hqp).1
    exact ⟨hR.trans _ hm _ hp _ hr h hpr.1, fun h' => hpr.2 (hR.trans _ hr _ hm _ hp h' h)⟩

private lemma lh_lower_convex {R : Rel 4} (hR : IsBetweennessPref R) {r p q : Lot 4}
    (hr : r ∈ Simplex 4) (hp : p ∈ Simplex 4) (hq : q ∈ Simplex 4)
    (hpr : SPref R r p) (hqr : SPref R r q) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    SPref R r (mix t p q) := by
  rcases ht0.eq_or_lt with rfl | ht0'
  · simpa [mix] using hqr
  rcases ht1.eq_or_lt with rfl | ht1'
  · simpa [mix] using hpr
  have hm := lh_mix_mem hp hq ht0 ht1
  have hat : t ∈ Set.Ioo (0 : ℝ) 1 := ⟨ht0', ht1'⟩
  rcases hR.complete p hp q hq with hpq | hqp
  · have h := (lh_between hR hp hq hat hpq).2
    exact ⟨hR.trans _ hr _ hp _ hm hpr.1 h, fun h' => hpr.2 (hR.trans _ hp _ hm _ hr h h')⟩
  · have hat' : 1 - t ∈ Set.Ioo (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
    rw [lh_swap] at hm ⊢
    have h := (lh_between hR hq hp hat' hqp).2
    exact ⟨hR.trans _ hr _ hq _ hm hqr.1 h, fun h' => hqr.2 (hR.trans _ hq _ hm _ hr h h')⟩

private lemma lh_simplex_closed : IsClosed (Simplex 4) := by
  have : Simplex 4 = (⋂ i, {p : Lot 4 | 0 ≤ p i}) ∩ {p | ∑ i, p i = 1} := by
    ext p; simp [Simplex]
  rw [this]
  exact (isClosed_iInter fun i => isClosed_le continuous_const (continuous_apply i)).inter
    (isClosed_eq (continuous_finsetSum _ fun i _ => continuous_apply i) continuous_const)

private lemma lh_lower_closed {R : Rel 4} (hR : IsBetweennessPref R) {r : Lot 4}
    (hr : r ∈ Simplex 4) : IsClosed {p : Lot 4 | p ∈ Simplex 4 ∧ R r p} := by
  have h := lh_simplex_closed.isClosedMap_subtype_val _ (hR.closed_lower r hr)
  convert h using 1
  ext p; constructor
  · rintro ⟨hp, h⟩; exact ⟨⟨p, hp⟩, h, rfl⟩
  · rintro ⟨q, hq, rfl⟩; exact ⟨q.2, hq⟩

private lemma lh_upper_closed {R : Rel 4} (hR : IsBetweennessPref R) {r : Lot 4}
    (hr : r ∈ Simplex 4) : IsClosed {p : Lot 4 | p ∈ Simplex 4 ∧ R p r} := by
  have h := lh_simplex_closed.isClosedMap_subtype_val _ (hR.closed_upper r hr)
  convert h using 1
  ext p; constructor
  · rintro ⟨hp, h⟩; exact ⟨⟨p, hp⟩, h, rfl⟩
  · rintro ⟨q, hq, rfl⟩; exact ⟨q.2, hq⟩

private lemma lh_seg_limit {C : Set (Lot 4)} (hC : IsClosed C) (p q : Lot 4)
    (h : ∀ t : ℝ, 0 < t → t ≤ 1 → mix t q p ∈ C) : p ∈ C := by
  have hc : Continuous (fun t : ℝ => mix t q p) := by unfold mix; fun_prop
  have h0 : mix 0 q p = p := by simp [mix]
  have ht : Tendsto (fun n : ℕ => mix (1 / ((n : ℝ) + 1)) q p) atTop (𝓝 p) := by
    have := (hc.tendsto 0).comp tendsto_one_div_add_atTop_nhds_zero_nat
    rwa [h0] at this
  apply hC.mem_of_tendsto ht
  refine Filter.Eventually.of_forall fun n => h _ (by positivity) ?_
  rw [div_le_one (by positivity)]
  linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]

private lemma lh_open_up {R : Rel 4} (hR : IsBetweennessPref R) {r p q : Lot 4}
    (hr : r ∈ Simplex 4) (hp : p ∈ Simplex 4) (hq : q ∈ Simplex 4) (hpr : SPref R p r) :
    ∃ t : ℝ, 0 < t ∧ t ≤ 1 ∧ SPref R (mix t q p) r := by
  by_contra hcon
  push Not at hcon
  have : p ∈ {z : Lot 4 | z ∈ Simplex 4 ∧ R r z} := by
    apply lh_seg_limit (lh_lower_closed hR hr) p q
    intro t h0 h1
    have hm := lh_mix_mem hq hp h0.le h1
    refine ⟨hm, ?_⟩
    by_contra hn
    rcases hR.complete _ hm r hr with h | h
    · exact hcon t h0 h1 ⟨h, hn⟩
    · exact hn h
  exact hpr.2 this.2

private lemma lh_open_down {R : Rel 4} (hR : IsBetweennessPref R) {r p q : Lot 4}
    (hr : r ∈ Simplex 4) (hp : p ∈ Simplex 4) (hq : q ∈ Simplex 4) (hpr : SPref R r p) :
    ∃ t : ℝ, 0 < t ∧ t ≤ 1 ∧ SPref R r (mix t q p) := by
  by_contra hcon
  push Not at hcon
  have : p ∈ {z : Lot 4 | z ∈ Simplex 4 ∧ R z r} := by
    apply lh_seg_limit (lh_upper_closed hR hr) p q
    intro t h0 h1
    have hm := lh_mix_mem hq hp h0.le h1
    refine ⟨hm, ?_⟩
    by_contra hn
    rcases hR.complete r hr _ hm with h | h
    · exact hcon t h0 h1 ⟨h, hn⟩
    · exact hn h
  exact hpr.2 this.2

/-- Projection onto the affine hyperplane `∑ = 1` along `(1,1,1,1)`. -/
private noncomputable def lhPr (q : Lot 4) : Lot 4 := fun i => q i - (∑ j, q j - 1) / 4

private lemma lhPr_of_mem {p : Lot 4} (hp : p ∈ Simplex 4) : lhPr p = p := by
  funext i; simp [lhPr, hp.2]

private lemma lhPr_sum (q : Lot 4) : ∑ i, lhPr q i = 1 := by
  simp only [lhPr, Fin.sum_univ_four]; ring

private lemma lhPr_comb (q1 q2 : Lot 4) {a b : ℝ} (hab : a + b = 1) :
    lhPr (a • q1 + b • q2) = a • lhPr q1 + b • lhPr q2 := by
  funext i
  simp only [lhPr, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Fin.sum_univ_four]
  linear_combination (-1 / 4 : ℝ) * hab

private lemma lhPr_cont : Continuous lhPr := by
  unfold lhPr
  exact continuous_pi fun i => (continuous_apply i).sub
    (((continuous_finsetSum _ fun j _ => continuous_apply j).sub continuous_const).div_const 4)

private lemma lh_sep {R : Rel 4} (hR : IsBetweennessPref R) {r : Lot 4} (hr : r ∈ Simplex 4) :
    ∃ W : Lot 4,
      (∀ a ∈ Simplex 4, (∀ i, 0 < a i) → SPref R a r → 0 < dot W a) ∧
      (∀ b ∈ Simplex 4, SPref R r b → dot W b ≤ 0) := by
  set L := {p : Lot 4 | p ∈ Simplex 4 ∧ R r p} with hL
  set S : Set (Lot 4) := {q | (∀ i, 0 < lhPr q i) ∧ lhPr q ∉ L} with hS
  set T : Set (Lot 4) := {p | p ∈ Simplex 4 ∧ SPref R r p} with hT
  have hPmem : ∀ q, (∀ i, 0 < lhPr q i) → lhPr q ∈ Simplex 4 :=
    fun q h => ⟨fun i => (h i).le, lhPr_sum q⟩
  have hSo : IsOpen S := by
    have h1 : IsOpen {q : Lot 4 | ∀ i, 0 < lhPr q i} := by
      simp only [Set.ofPred_forall]
      exact isOpen_iInter_of_finite fun i =>
        isOpen_lt continuous_const ((continuous_apply i).comp lhPr_cont)
    exact h1.inter ((lh_lower_closed hR hr).isOpen_compl.preimage lhPr_cont)
  have key : ∀ q ∈ S, SPref R (lhPr q) r := fun q hq => by
    have hm := hPmem q hq.1
    rcases hR.complete _ hm r hr with h | h
    · exact ⟨h, fun h' => hq.2 ⟨hm, h'⟩⟩
    · exact absurd ⟨hm, h⟩ hq.2
  have hSc : Convex ℝ S := by
    intro q1 hq1 q2 hq2 a b ha hb hab
    show (∀ i, 0 < lhPr (a • q1 + b • q2) i) ∧ lhPr (a • q1 + b • q2) ∉ L
    rw [lhPr_comb q1 q2 hab]
    have hb' : b = 1 - a := by linarith
    subst hb'
    have hm : SPref R (mix a (lhPr q1) (lhPr q2)) r :=
      lh_upper_convex hR hr (hPmem _ hq1.1) (hPmem _ hq2.1) (key _ hq1) (key _ hq2) ha
        (by linarith)
    refine ⟨fun i => ?_, fun h => hm.2 h.2⟩
    have h1 := hq1.1 i
    have h2 := hq2.1 i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rcases (show a ≤ 1 by linarith).lt_or_eq with ha1 | ha1
    · nlinarith [mul_pos (sub_pos.2 ha1) h2, mul_nonneg ha h1.le]
    · subst ha1; simpa using h1
  have hTc : Convex ℝ T := by
    intro p1 hp1 p2 hp2 a b ha hb hab
    have hb' : b = 1 - a := by linarith
    subst hb'
    exact ⟨lh_mix_mem hp1.1 hp2.1 ha (by linarith),
      lh_lower_convex hR hr hp1.1 hp2.1 hp1.2 hp2.2 ha (by linarith)⟩
  have hdisj : Disjoint S T := Set.disjoint_left.mpr fun q hqS hqT =>
    hqS.2 (by rw [lhPr_of_mem hqT.1]; exact ⟨hqT.1, hqT.2.1⟩)
  obtain ⟨f, u, hfS, hfT⟩ := geometric_hahn_banach_open hSc hSo hTc hdisj
  refine ⟨fun k => u - f (fun j => if k = j then 1 else 0), ?_, ?_⟩
  all_goals
    have hdot : ∀ p ∈ Simplex 4,
        dot (fun k => u - f (fun j => if k = j then 1 else 0)) p = u - f p := by
      intro p hp
      have hs : p 0 + p 1 + p 2 + p 3 = 1 := by simpa [Fin.sum_univ_four] using hp.2
      have hf := LinearMap.pi_apply_eq_sum_univ f.toLinearMap p
      simp only [ContinuousLinearMap.coe_coe, Fin.sum_univ_four, smul_eq_mul] at hf
      simp only [dot, Fin.sum_univ_four]
      rw [hf]
      linear_combination u * hs
  · intro a ha hpos har
    have haS : a ∈ S := by
      refine ⟨fun i => by rw [lhPr_of_mem ha]; exact hpos i, ?_⟩
      rw [lhPr_of_mem ha]
      exact fun h => har.2 h.2
    rw [hdot a ha]
    linarith [hfS a haS]
  · intro b hb hrb
    rw [hdot b hb]
    linarith [hfT b ⟨hb, hrb⟩]

private lemma lh_zero_t {A B : ℝ} (hA : 0 ≤ A) (hB : B < 0) :
    ∃ s : ℝ, 0 < s ∧ s ≤ 1 ∧ (0 < A → s < 1) ∧ s * A + (1 - s) * B = 0 := by
  have hd : 0 < A - B := by linarith
  refine ⟨-B / (A - B), div_pos (by linarith) hd, ?_, fun hA' => ?_, ?_⟩
  · rw [div_le_one hd]; linarith
  · rw [div_lt_one hd]; linarith
  · have : -B / (A - B) * (A - B) = -B := div_mul_cancel₀ _ hd.ne'
    linear_combination this

private noncomputable def lhMove (p : Lot 4) (k j : Fin 4) : Lot 4 :=
  fun i => if i = k then 0 else if i = j then p j + p k else p i

private lemma lhMove_spec {p : Lot 4} (hp : p ∈ Simplex 4) {k j : Fin 4} (hkj : k < j)
    (hpk : 0 < p k) (W : Lot 4) :
    lhMove p k j ∈ Simplex 4 ∧ StrictFOSD (lhMove p k j) p ∧
      dot W (lhMove p k j) = dot W p + p k * (W j - W k) := by
  have h0 := hp.1 0
  have h1 := hp.1 1
  have h2 := hp.1 2
  have h3 := hp.1 3
  have hs : p 0 + p 1 + p 2 + p 3 = 1 := by simpa [Fin.sum_univ_four] using hp.2
  have hne : k ≠ j := hkj.ne
  refine ⟨⟨fun i => ?_, ?_⟩, ⟨fun m => ?_, fun h => ?_⟩, ?_⟩
  · simp only [lhMove]; split_ifs <;> linarith [hp.1 i, hp.1 j, hp.1 k]
  · fin_cases k <;> fin_cases j <;> simp at hkj <;>
      simp [lhMove, Fin.sum_univ_four] <;> linarith
  · fin_cases k <;> fin_cases j <;> simp at hkj <;> fin_cases m <;>
      simp [tail, lhMove, Fin.sum_univ_four, Finset.sum_filter] <;> linarith
  · have := congrFun h k
    simp [lhMove] at this
    linarith
  · fin_cases k <;> fin_cases j <;> simp at hkj <;>
      simp [lhMove, dot, Fin.sum_univ_four] <;> ring

/-- Lemma 34: for `x ≻ r ≻ y` the indifference set of `r` is a hyperplane section of the
simplex with a strictly increasing normal vector. -/
theorem level_hyperplane {R : Rel 4} (hR : IsBetweennessPref R) {x r y : Lot 4}
    (hx : x ∈ Simplex 4) (hr : r ∈ Simplex 4) (hy : y ∈ Simplex 4)
    (hxr : SPref R x r) (hry : SPref R r y) :
    ∃ W : Lot 4, StrictMono W ∧
      ∀ p ∈ Simplex 4, (SPref R p r ↔ 0 < dot W p) ∧ (SPref R r p ↔ dot W p < 0) := by
  obtain ⟨W, hWS, hWT⟩ := lh_sep hR hr
  set e : Fin 4 → Lot 4 := fun k j => if k = j then 1 else 0 with he_def
  have he : ∀ k, e k ∈ Simplex 4 := by
    intro k
    refine ⟨fun j => by simp only [e]; split_ifs <;> norm_num, ?_⟩
    simp [e]
  have hWe : ∀ k, dot W (e k) = W k := by
    intro k; simp [dot, e]
  have hpos : ∀ p ∈ Simplex 4, (∀ k, 0 ≤ W k) → 0 ≤ dot W p := fun p hp h =>
    Finset.sum_nonneg fun k _ => mul_nonneg (h k) (hp.1 k)
  have hneg : ∀ p ∈ Simplex 4, (∀ k, W k ≤ 0) → dot W p ≤ 0 := fun p hp h =>
    Finset.sum_nonpos fun k _ => mul_nonpos_of_nonpos_of_nonneg (h k) (hp.1 k)
  set c : Lot 4 := fun _ => 1 / 4 with hc_def
  have hc : c ∈ Simplex 4 := ⟨fun _ => by norm_num [c], by simp [c]⟩
  obtain ⟨t0, ht0, ht1, hq0⟩ := lh_open_up hR hr hx hc hxr
  set q0 := mix t0 c x with hq0_def
  have hq0m : q0 ∈ Simplex 4 := lh_mix_mem hc hx ht0.le ht1
  have hq0pos : ∀ i, 0 < q0 i := fun i => by
    simp only [q0, mix, Pi.add_apply, Pi.smul_apply, smul_eq_mul, c]
    nlinarith [hx.1 i, mul_nonneg (sub_nonneg.2 ht1) (hx.1 i)]
  have hWq0 : 0 < dot W q0 := hWS q0 hq0m hq0pos hq0
  -- `dot W ≥ 0` on the strict upper set
  have hA1 : ∀ p ∈ Simplex 4, SPref R p r → 0 ≤ dot W p := by
    intro p hp hpr
    by_contra hn
    push Not at hn
    obtain ⟨s, hs0, hs1, -, hs⟩ := lh_zero_t hWq0.le hn
    have hm := lh_mix_mem hq0m hp hs0.le hs1
    have hpos' : ∀ i, 0 < mix s q0 p i := fun i => by
      simp only [mix, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      nlinarith [mul_pos hs0 (hq0pos i), mul_nonneg (sub_nonneg.2 hs1) (hp.1 i)]
    have := hWS _ hm hpos' (lh_upper_convex hR hr hq0m hp hq0 hpr hs0.le hs1)
    rw [lh_dot_mix] at this
    linarith
  -- `dot W < 0` on the strict lower set
  have hB : ∀ p ∈ Simplex 4, SPref R r p → dot W p < 0 := by
    intro p hp hrp
    rcases (hWT p hp hrp).lt_or_eq with h | h
    · exact h
    exfalso
    have hk : ∀ k, W k ≤ 0 := by
      intro k
      obtain ⟨t, ht0, ht1, ht⟩ := lh_open_down hR hr hp (he k) hrp
      have := hWT _ (lh_mix_mem (he k) hp ht0.le ht1) ht
      rw [lh_dot_mix, hWe, h] at this
      nlinarith
    linarith [hneg q0 hq0m hk]
  have hy0 := hB y hy hry
  -- `dot W > 0` on the strict upper set
  have hA : ∀ p ∈ Simplex 4, SPref R p r → 0 < dot W p := by
    intro p hp hpr
    rcases (hA1 p hp hpr).lt_or_eq with h | h
    · exact h
    exfalso
    have hk : ∀ k, 0 ≤ W k := by
      intro k
      obtain ⟨t, ht0, ht1, ht⟩ := lh_open_up hR hr hp (he k) hpr
      have := hA1 _ (lh_mix_mem (he k) hp ht0.le ht1) ht
      rw [lh_dot_mix, hWe, ← h] at this
      nlinarith
    linarith [hpos y hy hk]
  have hx0 := hA x hx hxr
  -- indifferent points lie on the hyperplane
  have hC : ∀ p ∈ Simplex 4, R p r → R r p → dot W p = 0 := by
    intro p hp h1 h2
    rcases lt_trichotomy (dot W p) 0 with h | h | h
    · exfalso
      have hxp : SPref R x p :=
        ⟨hR.trans _ hx _ hr _ hp hxr.1 h2, fun h' => hxr.2 (hR.trans _ hr _ hp _ hx h2 h')⟩
      obtain ⟨s, hs0, -, hs1, hs⟩ := lh_zero_t hx0.le h
      have hst := hR.btw_strict x hx p hp s ⟨hs0, hs1 hx0⟩ hxp
      have hm := lh_mix_mem hx hp hs0.le (hs1 hx0).le
      have hmr : SPref R (mix s x p) r :=
        ⟨hR.trans _ hm _ hp _ hr hst.2.1 h1,
          fun h' => hst.2.2 (hR.trans _ hp _ hr _ hm h1 h')⟩
      have := hA _ hm hmr
      rw [lh_dot_mix] at this
      linarith
    · exact h
    · exfalso
      have hpy : SPref R p y :=
        ⟨hR.trans _ hp _ hr _ hy h1 hry.1, fun h' => hry.2 (hR.trans _ hy _ hp _ hr h' h1)⟩
      obtain ⟨s, hs0, -, hs1, hs⟩ := lh_zero_t h.le hy0
      have hst := hR.btw_strict p hp y hy s ⟨hs0, hs1 h⟩ hpy
      have hm := lh_mix_mem hp hy hs0.le (hs1 h).le
      have hmr : SPref R r (mix s p y) :=
        ⟨hR.trans _ hr _ hp _ hm h2 hst.1.1,
          fun h' => hst.1.2 (hR.trans _ hm _ hr _ hp h' h2)⟩
      have := hB _ hm hmr
      rw [lh_dot_mix] at this
      linarith
  -- points on the hyperplane are indifferent
  have hI : ∀ p ∈ Simplex 4, dot W p = 0 → R p r ∧ R r p := by
    intro p hp h0
    rcases hR.complete p hp r hr with h | h
    · by_contra hn
      linarith [hA p hp ⟨h, fun h' => hn ⟨h, h'⟩⟩]
    · by_contra hn
      linarith [hB p hp ⟨h, fun h' => hn ⟨h', h⟩⟩]
  refine ⟨W, ?_, fun p hp => ⟨⟨hA p hp, fun h => ?_⟩, ⟨hB p hp, fun h => ?_⟩⟩⟩
  · intro k j hkj
    obtain ⟨p, hp, hp0, hpk⟩ : ∃ p ∈ Simplex 4, dot W p = 0 ∧ 0 < p k := by
      rcases le_or_gt 0 (W k) with hk | hk
      · obtain ⟨s, hs0, hs1, -, hs⟩ := lh_zero_t hk hy0
        refine ⟨mix s (e k) y, lh_mix_mem (he k) hy hs0.le hs1,
          by rw [lh_dot_mix, hWe]; exact hs, ?_⟩
        simp only [mix, Pi.add_apply, Pi.smul_apply, smul_eq_mul, e, ↓reduceIte, mul_one]
        nlinarith [hy.1 k, mul_nonneg (sub_nonneg.2 hs1) (hy.1 k)]
      · obtain ⟨s, hs0, hs1, -, hs⟩ := lh_zero_t (A := -W k) (B := -dot W x)
          (by linarith) (by linarith)
        refine ⟨mix s (e k) x, lh_mix_mem (he k) hx hs0.le hs1,
          by rw [lh_dot_mix, hWe]; linarith, ?_⟩
        simp only [mix, Pi.add_apply, Pi.smul_apply, smul_eq_mul, e, ↓reduceIte, mul_one]
        nlinarith [hx.1 k, mul_nonneg (sub_nonneg.2 hs1) (hx.1 k)]
    obtain ⟨h1, h2⟩ := hI p hp hp0
    obtain ⟨hq, hfosd, hdq⟩ := lhMove_spec hp hkj hpk W
    have hqp := hR.strictMono _ hq p hp hfosd
    have hqr : SPref R (lhMove p k j) r :=
      ⟨hR.trans _ hq _ hp _ hr hqp.1 h1, fun h => hqp.2 (hR.trans _ hp _ hr _ hq h1 h)⟩
    have := hA _ hq hqr
    rw [hdq, hp0] at this
    by_contra hn
    push Not at hn
    nlinarith
  · rcases hR.complete p hp r hr with h1 | h1
    · by_cases h2 : R r p
      · linarith [hC p hp h1 h2]
      · exact ⟨h1, h2⟩
    · by_cases h2 : R p r
      · linarith [hC p hp h2 h1]
      · linarith [hB p hp ⟨h1, h2⟩]
  · rcases hR.complete r hr p hp with h1 | h1
    · by_cases h2 : R p r
      · linarith [hC p hp h2 h1]
      · exact ⟨h1, h2⟩
    · by_cases h2 : R r p
      · linarith [hC p hp h1 h2]
      · linarith [hA p hp ⟨h1, h2⟩]

end Q2CL
