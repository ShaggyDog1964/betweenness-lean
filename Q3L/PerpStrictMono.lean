/-
`exists_perp_strictMono` (Lemma 85, direction ⇒).
-/
import Q3L.Statement
import Q3L.DotEq
import K4.Defs

namespace Q3L

open K4 (Lot Simplex tail)

/-- Standard basis vector. -/
private noncomputable def ebas {K : ℕ} (i : Fin K) : Lot K := fun l => if i = l then 1 else 0

private lemma gen_mem {K : ℕ} (i j : Fin K) (hij : j.val = i.val + 1) :
    (ebas j - ebas i) ∈ FOSDCone K ∧
      dot (fun k : Fin K => (k.val : ℝ)) (ebas j - ebas i) = 1 := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · simp [ebas, Finset.sum_sub_distrib]
  · intro k
    unfold tail
    simp only [ebas, Pi.sub_apply, Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.mem_filter,
      Finset.mem_univ, true_and]
    by_cases h1 : k ≤ i
    · have h2 : k ≤ j := by rw [Fin.le_def] at *; omega
      simp [h1, h2]
    · by_cases h2 : k ≤ j <;> simp [h1, h2]
  · unfold dot
    simp only [ebas, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    rw [hij]; push_cast; ring

/-- Lemma 85 (⇒): if a subspace `V` meets the weak-FOSD cone only in `0`, some strictly
increasing `w` is orthogonal to `V`. (No hypothesis `V ⊆ H₀` is needed.)
Proof: separate `convexHull {e_{j+1} - e_j}` (compact, inside the cone, on `dot ι = 1`)
from the closed subspace `V` by Hahn–Banach; `w k := - f e_k`. -/
theorem exists_perp_strictMono {K : ℕ} (V : Submodule ℝ (Lot K))
    (hV : ∀ d ∈ V, d ∈ FOSDCone K → d = 0) :
    ∃ w : Lot K, StrictMono w ∧ ∀ v ∈ V, dot w v = 0 := by
  set G : Set (Lot K) := {d | ∃ i j : Fin K, j.val = i.val + 1 ∧ d = ebas j - ebas i} with hG
  have hGfin : G.Finite := by
    apply (Set.finite_range (fun p : Fin K × Fin K => ebas p.2 - ebas p.1)).subset
    rintro d ⟨i, j, -, rfl⟩
    exact ⟨(i, j), rfl⟩
  set S : Set (Lot K) := {d | d ∈ FOSDCone K ∧ dot (fun k : Fin K => (k.val : ℝ)) d = 1}
  have hSconv : Convex ℝ S := by
    intro x hx y hy a b ha hb hab
    obtain ⟨⟨hx1, hx2⟩, hx3⟩ := hx
    obtain ⟨⟨hy1, hy2⟩, hy3⟩ := hy
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
        ← Finset.mul_sum, hx1, hy1]; ring
    · intro k
      have : tail (a • x + b • y) k = a * tail x k + b * tail y k := by
        unfold tail
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
          ← Finset.mul_sum]
      rw [this]
      have := hx2 k; have := hy2 k
      positivity
    · rw [dot_eq_dotProduct] at *
      rw [dotProduct_add, dotProduct_smul, dotProduct_smul, hx3, hy3]
      simp [hab]
  have hGS : G ⊆ S := by
    rintro d ⟨i, j, hij, rfl⟩
    exact gen_mem i j hij
  have hCS : convexHull ℝ G ⊆ S := convexHull_min hGS hSconv
  have hdisj : Disjoint (convexHull ℝ G) (V : Set (Lot K)) := by
    rw [Set.disjoint_left]
    intro d hdC hdV
    obtain ⟨hd1, hd2⟩ := hCS hdC
    have h0 := hV d hdV hd1
    subst h0
    simp [dot] at hd2
  obtain ⟨f, u, v', hfu, huv, hvf⟩ := geometric_hahn_banach_compact_closed
    (convex_convexHull ℝ G) (hGfin.isCompact_convexHull (𝕜 := ℝ)) V.convex
    (Submodule.closed_of_finiteDimensional V) hdisj
  have hv'neg : v' < 0 := by simpa using hvf 0 V.zero_mem
  have hfV : ∀ x ∈ V, f x = 0 := by
    intro x hx
    by_contra hne
    have := hvf ((v' / f x) • x) (V.smul_mem _ hx)
    rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ hne] at this
    exact lt_irrefl _ this
  have hfsum : ∀ x : Lot K, f x = ∑ k, f (ebas k) * x k := by
    intro x
    have hx : x = ∑ k, x k • ebas k := by
      ext l
      simp [ebas, Finset.sum_apply]
    conv_lhs => rw [hx]
    rw [map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_smul, smul_eq_mul, mul_comm]
  refine ⟨fun k => - f (ebas k), ?_, ?_⟩
  · have hstep : ∀ i j : Fin K, j.val = i.val + 1 → - f (ebas i) < - f (ebas j) := by
      intro i j hij
      have hmem : ebas j - ebas i ∈ convexHull ℝ G := subset_convexHull ℝ G ⟨i, j, hij, rfl⟩
      have := hfu _ hmem
      rw [map_sub] at this
      linarith
    cases K with
    | zero => intro a; exact a.elim0
    | succ n =>
      rw [Fin.strictMono_iff_lt_succ]
      intro i
      exact hstep _ _ (by simp)
  · intro x hx
    unfold dot
    have := hfV x hx
    rw [hfsum x] at this
    simp only [neg_mul, Finset.sum_neg_distrib, this, neg_zero]

end Q3L
