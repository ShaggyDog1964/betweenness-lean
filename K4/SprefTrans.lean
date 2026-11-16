import K4.Defs

namespace K4

/-- Strict preference is transitive on the simplex.
Sketch: `R a c` from `hab.1`, `hbc.1` by `hR.trans`. If `R c a`, then `R b c` and `R c a`
give `R b a` by `hR.trans`, contradicting `hab.2`. -/
theorem spref_trans {K : ℕ} {R : Rel K} (hR : IsBetweennessPref R) {a b c : Lot K}
    (ha : a ∈ Simplex K) (hb : b ∈ Simplex K) (hc : c ∈ Simplex K)
    (hab : SPref R a b) (hbc : SPref R b c) : SPref R a c := by
  refine ⟨hR.trans a ha b hb c hc hab.1 hbc.1, fun hca => ?_⟩
  exact hab.2 (hR.trans b hb c hc a ha hbc.1 hca)

end K4
