import K4.Defs
import K4.StrictChain
import K4.PathOfChain
import K4.PrefOfPath
import K4.PairwiseRangeChain
import K4.SprefTrans

namespace K4

/-- SUFFICIENCY of the chain condition (the "Afriat" direction of `betw_lp.py`): a weakly
increasing chain of strictly increasing weight vectors, the `i`-th strictly separating entry
`i` (above) from entry `i+1` (below), makes the list representable.
Sketch: `strict_chain_of_weak` gives `W'`; `path_of_strict_chain W' m` gives `Φ` with
`Φ i = W' i`; `pref_of_path` gives `R` and, at `τ = i`, `SPref R (g i) (g (i+1))` for
`i + 1 < m`. `pairwise_range_of_chain` with `S = Simplex K` and transitivity from
`spref_trans` gives `((List.range m).map g).Pairwise (SPref R)`. -/
theorem representable_of_chain {K : ℕ} (W : ℕ → Lot K) (g : ℕ → Lot K) (m : ℕ)
    (hg : ∀ i, i < m → g i ∈ Simplex K)
    (hW : ∀ i, StrictMono (W i)) (hmono : ∀ i, W i ≤ W (i + 1))
    (hsep : ∀ i, i + 1 < m → 0 < dot (W i) (g i) ∧ dot (W i) (g (i + 1)) < 0) :
    Representable ((List.range m).map g) := by
  obtain ⟨W', hW', hstep, hsep'⟩ := strict_chain_of_weak W g m hg hW hmono hsep
  obtain ⟨Φ, hcont, hcoord, hinc, hlow, hhigh, hΦ⟩ := path_of_strict_chain W' m hW' hstep
  obtain ⟨R, hR, hfin⟩ := pref_of_path Φ hcont hcoord hinc hlow hhigh
  refine ⟨R, hR, ?_⟩
  refine pairwise_range_of_chain (Simplex K) (SPref R)
    (fun a ha b hb c hc hab hbc => spref_trans hR ha hb hc hab hbc) g m hg ?_
  intro i hi
  have hΦi : Φ (i : ℝ) = W' i := hΦ i (by omega)
  obtain ⟨h1, h2⟩ := hsep' i hi
  exact hfin (g i) (hg i (by omega)) (g (i + 1)) (hg (i + 1) hi) (i : ℝ)
    (by rw [hΦi]; exact h1) (by rw [hΦi]; exact h2)

end K4
