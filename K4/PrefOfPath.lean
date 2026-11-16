import K4.Defs
import K4.DotFosd
import K4.MixMem

namespace K4

/-- A monotone continuous path of strictly increasing weight vectors defines a betweenness
preference: rank `p` by the unique root `τ(p)` of `τ ↦ dot (Φ τ) p` (smaller root = better).
Sketch. For `p ∈ Simplex`, `f p τ := dot (Φ τ) p` is continuous in `τ` (`hcont`) and strictly
increasing (`hinc`, `p ≥ 0`, `∑ p = 1`), negative somewhere and positive somewhere, so it has
a unique root `τ p` (IVT `intermediate_value_Icc`; set `τ p := 0` off the simplex) and
`0 ≤ f p s ↔ τ p ≤ s`. Define `R q r :↔ τ q ≤ τ r`.
complete/trans: from `≤`. closed_upper: `{q | τ q ≤ τ r} = {q | 0 ≤ dot (Φ (τ r)) q}`,
closed as preimage of a continuous linear map under `Subtype.val`; closed_lower similarly
with `≤ 0`. strictMono: `StrictFOSD q r` gives `f q (τ r) > f r (τ r) = 0`
(`dot_lt_of_strictFOSD`, `hcoord`) so `τ q < τ r`. btw_strict: `τ q < τ r`; `f` is affine in
`p` (`dot` of `mix` = `t * dot + (1-t) * dot`); `f (mix) (τ q) = (1-t) f r (τ q) < 0` and
`f (mix) (τ r) = t f q (τ r) > 0`, so `τ q < τ mix < τ r` (`mix_mem_simplex`). btw_indiff:
`f mix (τ q) = 0`. Final clause: `0 < f p τ` gives `τ p < τ`, `f q τ < 0` gives `τ < τ q`. -/
theorem pref_of_path {K : ℕ} (Φ : ℝ → Lot K) (hcont : Continuous Φ)
    (hcoord : ∀ τ, StrictMono (Φ τ))
    (hinc : ∀ τ τ' : ℝ, τ < τ' → ∀ k, Φ τ k < Φ τ' k)
    (hlow : ∀ p ∈ Simplex K, ∃ τ, dot (Φ τ) p < 0)
    (hhigh : ∀ p ∈ Simplex K, ∃ τ, 0 < dot (Φ τ) p) :
    ∃ R : Rel K, IsBetweennessPref R ∧
      ∀ p ∈ Simplex K, ∀ q ∈ Simplex K, ∀ τ : ℝ,
        0 < dot (Φ τ) p → dot (Φ τ) q < 0 → SPref R p q := by
  classical
  -- strict monotonicity in τ
  have hmono : ∀ p ∈ Simplex K, StrictMono (fun s => dot (Φ s) p) := by
    intro p hp s s' hss'
    obtain ⟨k, hk⟩ : ∃ k, 0 < p k := by
      by_contra hc
      push_neg at hc
      have : ∑ i, p i = 0 := Finset.sum_eq_zero (fun i _ => le_antisymm (hc i) (hp.1 i))
      rw [hp.2] at this; exact one_ne_zero this
    unfold dot
    apply Finset.sum_lt_sum
    · intro i _
      exact mul_le_mul_of_nonneg_right (hinc s s' hss' i).le (hp.1 i)
    · exact ⟨k, Finset.mem_univ _, mul_lt_mul_of_pos_right (hinc s s' hss' k) hk⟩
  have hcontf : ∀ p : Lot K, Continuous (fun s => dot (Φ s) p) := by
    intro p
    unfold dot
    exact continuous_finset_sum _ (fun k _ =>
      ((continuous_apply k).comp hcont).mul continuous_const)
  have hroot : ∀ p ∈ Simplex K, ∃ s, dot (Φ s) p = 0 := by
    intro p hp
    obtain ⟨a, ha⟩ := hlow p hp
    obtain ⟨b, hb⟩ := hhigh p hp
    have hab : a ≤ b := by
      by_contra h
      push_neg at h
      have := hmono p hp h
      simp only at this
      linarith
    have := intermediate_value_Icc hab (hcontf p).continuousOn
      (show (0 : ℝ) ∈ Set.Icc (dot (Φ a) p) (dot (Φ b) p) from ⟨ha.le, hb.le⟩)
    obtain ⟨s, _, hs⟩ := this
    exact ⟨s, hs⟩
  let τ : Lot K → ℝ := fun p => if h : p ∈ Simplex K then Classical.choose (hroot p h) else 0
  have hτ : ∀ p ∈ Simplex K, dot (Φ (τ p)) p = 0 := by
    intro p hp
    simp only [τ, dif_pos hp]
    exact Classical.choose_spec (hroot p hp)
  have kle : ∀ p ∈ Simplex K, ∀ s, (0 ≤ dot (Φ s) p ↔ τ p ≤ s) := by
    intro p hp s
    have := (hmono p hp).le_iff_le (a := τ p) (b := s)
    simp only [hτ p hp] at this
    exact this
  have klt : ∀ p ∈ Simplex K, ∀ s, (0 < dot (Φ s) p ↔ τ p < s) := by
    intro p hp s
    have := (hmono p hp).lt_iff_lt (a := τ p) (b := s)
    simp only [hτ p hp] at this
    exact this
  have kle' : ∀ p ∈ Simplex K, ∀ s, (dot (Φ s) p ≤ 0 ↔ s ≤ τ p) := by
    intro p hp s
    have := (hmono p hp).le_iff_le (a := s) (b := τ p)
    simp only [hτ p hp] at this
    exact this
  have klt' : ∀ p ∈ Simplex K, ∀ s, (dot (Φ s) p < 0 ↔ s < τ p) := by
    intro p hp s
    have := (hmono p hp).lt_iff_lt (a := s) (b := τ p)
    simp only [hτ p hp] at this
    exact this
  have hdotmix : ∀ (w q r : Lot K) (t : ℝ),
      dot w (mix t q r) = t * dot w q + (1 - t) * dot w r := by
    intro w q r t
    unfold dot
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    simp only [mix, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hcontq : ∀ w : Lot K, Continuous (fun q : Simplex K => dot w q.1) := by
    intro w
    unfold dot
    exact continuous_finset_sum _ (fun k _ =>
      continuous_const.mul ((continuous_apply k).comp continuous_subtype_val))
  have hspref : ∀ q r : Lot K, SPref (fun a b => τ a ≤ τ b) q r ↔ τ q < τ r := by
    intro q r
    simp only [SPref, not_le]
    constructor
    · exact fun h => h.2
    · exact fun h => ⟨h.le, h⟩
  refine ⟨fun a b => τ a ≤ τ b, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · intro q _ r _; exact le_total _ _
  · intro q _ r _ s _ h1 h2; exact le_trans h1 h2
  · intro r _
    have : {q : Simplex K | τ q.1 ≤ τ r} = {q : Simplex K | 0 ≤ dot (Φ (τ r)) q.1} := by
      ext q; simp only [Set.mem_setOf_eq]; exact (kle q.1 q.2 _).symm
    show IsClosed {q : Simplex K | τ q.1 ≤ τ r}
    rw [this]
    exact isClosed_le continuous_const (hcontq _)
  · intro r _
    have : {q : Simplex K | τ r ≤ τ q.1} = {q : Simplex K | dot (Φ (τ r)) q.1 ≤ 0} := by
      ext q; simp only [Set.mem_setOf_eq]; exact (kle' q.1 q.2 _).symm
    show IsClosed {q : Simplex K | τ r ≤ τ q.1}
    rw [this]
    exact isClosed_le (hcontq _) continuous_const
  · intro q hq r hr h
    rw [hspref]
    have := dot_lt_of_strictFOSD (hcoord (τ r)) hq hr h
    rw [hτ r hr] at this
    exact (klt q hq _).1 this
  · intro q hq r hr t ht h
    rw [hspref] at h
    have hm := mix_mem_simplex hq hr ht.1.le ht.2.le
    rw [hspref, hspref]
    constructor
    · apply (klt' _ hm _).1
      rw [hdotmix, hτ q hq]
      have := (klt' r hr (τ q)).2 h
      have h1 : 0 < 1 - t := by linarith [ht.2]
      nlinarith
    · apply (klt _ hm _).1
      rw [hdotmix, hτ r hr]
      have := (klt q hq (τ r)).2 h
      nlinarith [ht.1]
  · intro q hq r hr t ht h
    have heq : τ q = τ r := le_antisymm h.1 h.2
    have hm := mix_mem_simplex hq hr ht.1.le ht.2.le
    have hz : dot (Φ (τ q)) (mix t q r) = 0 := by
      rw [hdotmix, hτ q hq, heq, hτ r hr]; ring
    exact ⟨(kle _ hm _).1 hz.ge, (kle' _ hm _).1 hz.le⟩
  · intro p hp q hq s h1 h2
    rw [hspref]
    exact lt_trans ((klt p hp s).1 h1) ((klt' q hq s).1 h2)

end K4
