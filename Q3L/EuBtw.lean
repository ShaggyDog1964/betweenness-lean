/-
`euRel_isBetweenness`: EU with strictly increasing utility is in BT
(`setting.tex`), in general dimension.
-/
import Q3L.Statement
import Q3L.DotEq
import K4.DotFosd

namespace Q3L

open K4 (Lot Simplex IsBetweennessPref)

/-- The EU relation of a strictly increasing `u` is a betweenness preference.
Sketch. `euRel u p q := dot u q ≤ dot u p`. complete: `le_total`. trans: `le_trans`.
closed_upper r: `{q : Simplex K | dot u r ≤ dot u q.1}` is the preimage of `Set.Ici` under
the continuous map `q ↦ dot u q.1` (`continuous_finset_sum`, `continuous_apply`,
`continuous_subtype_val`), so `isClosed_le`. closed_lower likewise.
strictMono: `K4.dot_lt_of_strictFOSD hu hq hr h : K4.dot u r < K4.dot u q`, which is
`dot u r < dot u q` definitionally; `SPref` is `≤ ∧ ¬ ≥`.
btw_strict / btw_indiff: `dot u (K4.mix t q r) = t * dot u q + (1 - t) * dot u r`
(`dot_eq_dotProduct`, `dotProduct_add`, `dotProduct_smul`), strictly between the two values
when they differ and `t ∈ (0,1)`, and equal to both when they agree (`nlinarith`). -/
theorem euRel_isBetweenness {K : ℕ} {u : Lot K} (hu : StrictMono u) :
    IsBetweennessPref (euRel u) := by
  have hdotmix : ∀ (q r : Lot K) (t : ℝ),
      dot u (K4.mix t q r) = t * dot u q + (1 - t) * dot u r := by
    intro q r t
    unfold dot
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    simp only [K4.mix, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hcontq : Continuous (fun q : Simplex K => dot u q.1) := by
    unfold dot
    exact continuous_finset_sum _ (fun k _ =>
      continuous_const.mul ((continuous_apply k).comp continuous_subtype_val))
  have hspref : ∀ q r : Lot K, K4.SPref (euRel u) q r ↔ dot u r < dot u q := by
    intro q r
    simp only [K4.SPref, euRel, not_le]
    exact ⟨fun h => h.2, fun h => ⟨h.le, h⟩⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro q _ r _; exact le_total _ _
  · intro q _ r _ s _ h1 h2; exact le_trans h2 h1
  · intro r _
    exact isClosed_le continuous_const hcontq
  · intro r _
    exact isClosed_le hcontq continuous_const
  · intro q hq r hr h
    rw [hspref]
    exact K4.dot_lt_of_strictFOSD hu hq hr h
  · intro q _ r _ t ht h
    rw [hspref] at h
    rw [hspref, hspref, hdotmix]
    have h1 : 0 < 1 - t := by linarith [ht.2]
    have h0 := ht.1
    constructor <;> nlinarith
  · intro q _ r _ t _ h
    have heq : dot u q = dot u r := le_antisymm h.2 h.1
    have hz : dot u (K4.mix t q r) = dot u q := by
      rw [hdotmix, heq]; ring
    simp only [K4.Indiff, euRel, hz, le_refl, and_self]

end Q3L
