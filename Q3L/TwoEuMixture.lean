/-
`mixture_of_two_eu`: `½[u] + ½[u']` is a mixture of EU and of betweenness
preferences.
-/
import Q3L.Statement
import Q3L.EuBtw

namespace Q3L

open K4 (Lot IsBetweennessPref)

open Classical in
/-- If `ρ = ½[u] + ½[u']` on menus of `X`, with `u, u'` strictly increasing and both EU
relations strict on `X`, then `ρ` is a mixture of EU preferences and of betweenness
preferences.
Sketch. Use `n = 2`, `R := ![euRel u, euRel u']`, `w := ![1/2, 1/2]`. Each `R i` is
`IsEUPref` (witness `u` resp. `u'`; the iff is `Iff.rfl`) and `IsBetweennessPref`
(`euRel_isBetweenness`), and strict on `X` (`hsu`, `hsu'`). Weights are `≥ 0` with sum `1`
(`Fin.sum_univ_two`). The mixture formula is `hρ` after `Fin.sum_univ_two` and
`Matrix.cons_val_zero`, `Matrix.cons_val_one`, `Matrix.head_cons`. Do it once with a class `C`
satisfied by both relations and instantiate at `IsEUPref` and `IsBetweennessPref`. -/
theorem mixture_of_two_eu {K : ℕ} {X : Finset (Lot K)} {u u' : Lot K} (hu : StrictMono u)
    (hu' : StrictMono u') (hsu : StrictOn (euRel u) X) (hsu' : StrictOn (euRel u') X)
    (ρ : RandomChoiceRule X)
    (hρ : ∀ A ⊆ X, A.Nonempty → ∀ x ∈ A, ρ.p x A =
      (if IsMaxIn (euRel u) x A then 1 / 2 else 0) +
        (if IsMaxIn (euRel u') x A then 1 / 2 else 0)) :
    IsMixture IsEUPref X ρ ∧ IsMixture IsBetweennessPref X ρ := by
  have key : ∀ C : K4.Rel K → Prop, C (euRel u) → C (euRel u') → IsMixture C X ρ := by
    intro C hC hC'
    refine ⟨2, ![euRel u, euRel u'], ![1/2, 1/2], ?_, ?_, ?_, ?_⟩
    · intro i
      fin_cases i
      · exact ⟨hC, hsu⟩
      · exact ⟨hC', hsu'⟩
    · intro i
      fin_cases i <;> norm_num
    · rw [Fin.sum_univ_two]; norm_num
    · intro A hA hne x hx
      rw [Fin.sum_univ_two, hρ A hA hne x hx]
      rfl
  exact ⟨key _ ⟨u, hu, fun _ _ _ _ => Iff.rfl⟩ ⟨u', hu', fun _ _ _ _ => Iff.rfl⟩,
    key _ (euRel_isBetweenness hu) (euRel_isBetweenness hu')⟩

end Q3L
