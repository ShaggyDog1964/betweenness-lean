/-
`sep_relOpen` (part of the proof of Lemma 34: separating two disjoint relatively open convex
subsets of the simplex).
-/
import Q3L.Statement
import Q3L.DotEq

namespace Q3L

open K4 (Lot Simplex)

private noncomputable def piS {K : ℕ} (z : Lot K) : Lot K :=
  fun k => z k + (1 - ∑ i, z i) / K

private lemma piS_cont {K : ℕ} : Continuous (piS (K := K)) := by
  unfold piS
  refine continuous_pi fun k => ?_
  exact (continuous_apply k).add
    ((continuous_const.sub (continuous_finset_sum _ fun i _ => continuous_apply i)).div_const _)

private lemma piS_sum {K : ℕ} (hK : 0 < K) (z : Lot K) : ∑ k, piS z k = 1 := by
  unfold piS
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  have : (K : ℝ) ≠ 0 := by exact_mod_cast hK.ne'
  field_simp
  ring

private lemma piS_fix {K : ℕ} {p : Lot K} (hp : p ∈ Simplex K) : piS p = p := by
  funext k; unfold piS; rw [hp.2]; simp

private lemma piS_affine {K : ℕ} (z z' : Lot K) (a b : ℝ) (hab : a + b = 1) :
    piS (a • z + b • z') = a • piS z + b • piS z' := by
  funext k
  simp only [piS, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
    ← Finset.mul_sum]
  have hb : b = 1 - a := by linarith
  subst hb
  ring

private lemma piS_mem {K : ℕ} (hK : 0 < K) {z : Lot K} (h : ∀ k, 0 < piS z k) :
    piS z ∈ Simplex K := ⟨fun k => (h k).le, piS_sum hK z⟩

private lemma conv_O {K : ℕ} (hK : 0 < K) {G : Set (Lot K)} (hS : Convex ℝ (Simplex K ∩ G)) :
    Convex ℝ {z : Lot K | piS z ∈ G ∧ ∀ k, 0 < piS z k} := by
  intro z hz z' hz' a b ha hb hab
  refine ⟨?_, ?_⟩
  · show piS (a • z + b • z') ∈ G
    rw [piS_affine z z' a b hab]
    exact (hS ⟨piS_mem hK hz.2, hz.1⟩ ⟨piS_mem hK hz'.2, hz'.1⟩ ha hb hab).2
  · intro k
    rw [piS_affine z z' a b hab]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have h1 := hz.2 k
    have h2 := hz'.2 k
    rcases ha.lt_or_eq with ha' | ha'
    · have := mul_pos ha' h1; have := mul_nonneg hb h2.le; linarith
    · have hb' : b = 1 := by rw [← ha'] at hab; linarith
      rw [← ha', hb']; simp [h2]

private lemma open_O {K : ℕ} {G : Set (Lot K)} (hG : IsOpen G) :
    IsOpen {z : Lot K | piS z ∈ G ∧ ∀ k, 0 < piS z k} := by
  have hP : IsOpen {p : Lot K | ∀ k, 0 < p k} := by
    have : {p : Lot K | ∀ k, 0 < p k} = ⋂ k, {p : Lot K | 0 < p k} := by ext; simp
    rw [this]
    exact isOpen_iInter_of_finite fun k => isOpen_lt continuous_const (continuous_apply k)
  exact (hG.inter hP).preimage piS_cont

/-- Two disjoint convex sets `Simplex ∩ G`, `Simplex ∩ G'` (`G, G'` open) are separated by a
linear form `dot W`, strictly on their points with all coordinates positive.
Sketch. Let `𝟙 = fun _ => (1:ℝ)` and `π z := z + ((1 - ∑ k, z k) / K) • 𝟙` (uses `K ≠ 0`):
`π` is continuous, affine (`π (a • z + b • z') = a • π z + b • π z'` when `a + b = 1`), lands
in `{∑ = 1}`, and fixes simplex points. Let `Pos := {p | ∀ k, 0 < p k}` (open: finite
intersection of open half-spaces, `isOpen_iInter_of_finite`, `isOpen_lt`). Put
`O := π ⁻¹' (G ∩ Pos)` and `O' := π ⁻¹' (G' ∩ Pos)`.
* Open: preimages of open sets under continuous `π`.
* `π z ∈ Pos` already implies `π z ∈ Simplex K` (sum is `1`). So `z ∈ O ↔ π z ∈
  (Simplex ∩ G) ∩ Pos`; convexity of `O` follows from affinity of `π`, `hS` and convexity of
  `Pos`; likewise `O'`.
* Disjoint: a common `z` puts `π z` in both `Simplex ∩ G` and `Simplex ∩ G'`.
`geometric_hahn_banach_open_open` gives a continuous linear `f` and `u` with `f a < u` on `O`
and `u < f b` on `O'`. Put `W k := u - f (Pi.single k 1)`. For `p ∈ Simplex K`,
`dot W p = u * ∑ p - f (∑ k, p k • Pi.single k 1) = u - f p` (`pi_eq_sum_univ`, `map_sum`).
If moreover `p ∈ G`, `p ∈ Pos`, then `π p = p` so `p ∈ O` and `dot W p = u - f p > 0`;
similarly `dot W p < 0` on `Simplex ∩ G' ∩ Pos`. -/
theorem sep_relOpen {K : ℕ} (hK : 0 < K) {G G' : Set (Lot K)} (hG : IsOpen G)
    (hG' : IsOpen G') (hS : Convex ℝ (Simplex K ∩ G)) (hT : Convex ℝ (Simplex K ∩ G'))
    (hdisj : Disjoint (Simplex K ∩ G) (Simplex K ∩ G')) :
    ∃ W : Lot K, (∀ p ∈ Simplex K ∩ G, (∀ k, 0 < p k) → 0 < dot W p) ∧
      (∀ p ∈ Simplex K ∩ G', (∀ k, 0 < p k) → dot W p < 0) := by
  have hd : Disjoint {z : Lot K | piS z ∈ G ∧ ∀ k, 0 < piS z k}
      {z : Lot K | piS z ∈ G' ∧ ∀ k, 0 < piS z k} := by
    rw [Set.disjoint_left]
    intro z hz hz'
    exact Set.disjoint_left.mp hdisj ⟨piS_mem hK hz.2, hz.1⟩ ⟨piS_mem hK hz'.2, hz'.1⟩
  obtain ⟨f, u, hf, hf'⟩ := geometric_hahn_banach_open_open (conv_O hK hS) (open_O hG)
    (conv_O hK hT) (open_O hG') hd
  have key : ∀ p ∈ Simplex K, dot (fun k => u - f (Pi.single k 1)) p = u - f p := by
    intro p hp
    have hpe : p = ∑ k, p k • (Pi.single k (1:ℝ) : Lot K) := by
      funext j; simp [Finset.sum_apply, Pi.single_apply]
    conv_rhs => rw [hpe]
    rw [map_sum]
    simp only [map_smul, smul_eq_mul, dot, sub_mul, Finset.sum_sub_distrib, ← Finset.sum_mul,
      ← Finset.mul_sum]
    rw [hp.2]
    simp [mul_comm]
  refine ⟨fun k => u - f (Pi.single k 1), ?_, ?_⟩
  · intro p hp hpos
    rw [key p hp.1]
    have : p ∈ {z : Lot K | piS z ∈ G ∧ ∀ k, 0 < piS z k} := by
      simp only [Set.mem_ofPred_eq, piS_fix hp.1]; exact ⟨hp.2, hpos⟩
    linarith [hf p this]
  · intro p hp hpos
    rw [key p hp.1]
    have : p ∈ {z : Lot K | piS z ∈ G' ∧ ∀ k, 0 < piS z k} := by
      simp only [Set.mem_ofPred_eq, piS_fix hp.1]; exact ⟨hp.2, hpos⟩
    linarith [hf' p this]

end Q3L
