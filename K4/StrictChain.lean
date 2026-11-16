import K4.Defs

namespace K4

private lemma dot_add_const {K : ℕ} (w p : Lot K) (c : ℝ) (hp : p ∈ Simplex K) :
    dot (fun k => w k + c) p = dot w p + c := by
  unfold dot
  simp only [add_mul, Finset.sum_add_distrib]
  rw [← Finset.mul_sum, hp.2, mul_one]

/-- A weakly increasing separating chain can be made strictly increasing while keeping the
strict separations.
Sketch. Let `M > 0` be the minimum over `i + 1 < m` of `-dot (W i) (g (i+1))` (finite min,
`Finset.exists_min_image` on `Finset.range m`; if `m ≤ 1` take `M = 1`), and
`ε = M / (2 * (m + 1))`. Put `W' i = W i + (ε * i) • (fun _ => 1)`. On the simplex
`dot (W' i) p = dot (W i) p + ε * i` (since `∑ p = 1`). So
`dot (W' i) (g i) ≥ dot (W i) (g i) > 0` and
`dot (W' i) (g (i+1)) ≤ -M + ε * m < 0` for `i + 1 < m`. `StrictMono (W' i)`: adding a
constant. Strict step: `W' (i+1) k - W' i k = (W (i+1) k - W i k) + ε ≥ ε > 0`. -/
theorem strict_chain_of_weak {K : ℕ} (W : ℕ → Lot K) (g : ℕ → Lot K) (m : ℕ)
    (hg : ∀ i, i < m → g i ∈ Simplex K)
    (hW : ∀ i, StrictMono (W i)) (hmono : ∀ i, W i ≤ W (i + 1))
    (hsep : ∀ i, i + 1 < m → 0 < dot (W i) (g i) ∧ dot (W i) (g (i + 1)) < 0) :
    ∃ W' : ℕ → Lot K, (∀ i, StrictMono (W' i)) ∧ (∀ i k, W' i k < W' (i + 1) k) ∧
      (∀ i, i + 1 < m → 0 < dot (W' i) (g i) ∧ dot (W' i) (g (i + 1)) < 0) := by
  classical
  let f : ℕ → ℝ := fun i => if i + 1 < m then -dot (W i) (g (i + 1)) else 1
  have hf : ∀ i, 0 < f i := by
    intro i
    by_cases h : i + 1 < m
    · simp only [f, h, ↓reduceIte]; linarith [(hsep i h).2]
    · simp only [f, h, ↓reduceIte]; norm_num
  have hne : (Finset.range (m + 1)).Nonempty := ⟨0, by simp⟩
  let M : ℝ := (Finset.range (m + 1)).inf' hne f
  have hM : 0 < M := by
    rw [Finset.lt_inf'_iff]
    intro i _; exact hf i
  have hMle : ∀ i, i < m + 1 → M ≤ f i := fun i hi =>
    Finset.inf'_le _ (Finset.mem_range.mpr hi)
  have hm1 : (0 : ℝ) < 2 * ((m : ℝ) + 1) := by positivity
  set ε : ℝ := M / (2 * ((m : ℝ) + 1)) with hε
  have hεpos : 0 < ε := div_pos hM hm1
  refine ⟨fun i k => W i k + ε * i, ?_, ?_, ?_⟩
  · intro i a b hab
    have := hW i hab
    simp only
    linarith
  · intro i k
    have h1 : W i k ≤ W (i + 1) k := hmono i k
    simp only [Nat.cast_add, Nat.cast_one]
    nlinarith
  · intro i hi
    have hgi := hg i (by omega)
    have hgi1 := hg (i + 1) hi
    obtain ⟨h1, h2⟩ := hsep i hi
    have hi0 : (0 : ℝ) ≤ (i : ℝ) := Nat.cast_nonneg i
    rw [dot_add_const _ _ _ hgi, dot_add_const _ _ _ hgi1]
    refine ⟨by nlinarith, ?_⟩
    have hfi : f i = -dot (W i) (g (i + 1)) := by simp only [f, hi, ↓reduceIte]
    have hMf := hMle i (by omega)
    have him : (i : ℝ) + 1 < (m : ℝ) + 1 := by
      have : ((i + 1 : ℕ) : ℝ) < (m : ℝ) := by exact_mod_cast hi
      push_cast at this; linarith
    have hεi : ε * i < M := by
      have : ε * (2 * ((m : ℝ) + 1)) = M := by
        rw [hε]; field_simp
      nlinarith
    linarith

end K4
