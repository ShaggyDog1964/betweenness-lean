import K4.Defs

namespace K4

/-- Strict preference is invariant under replacing both sides by indifferent lotteries.
Sketch: `R a' a`, `R a b`, `R b b'` give `R a' b'` (two uses of `hR.trans`). If `R b' a'`,
then `R b b'`, `R b' a'`, `R a' a` give `R b a`, contradicting `h.2`. -/
theorem spref_congr {K : ℕ} {R : Rel K} (hR : IsBetweennessPref R) {a a' b b' : Lot K}
    (ha : a ∈ Simplex K) (ha' : a' ∈ Simplex K) (hb : b ∈ Simplex K) (hb' : b' ∈ Simplex K)
    (haa : Indiff R a a') (hbb : Indiff R b b') (h : SPref R a b) : SPref R a' b' := by
  refine ⟨hR.trans a' ha' b hb b' hb' (hR.trans a' ha' a ha b hb haa.2 h.1) hbb.1, fun hba => ?_⟩
  exact h.2 (hR.trans b hb a' ha' a ha (hR.trans b hb b' hb' a' ha' hbb.1 hba) haa.2)

end K4
