/-
`exists_generic_dir` (Claim B in the proof of Theorem 36(2), in linear form).
-/
import Q3L.Statement
import Q3L.DotEq

namespace Q3L

open K4 (Lot)

private lemma gd_self_pos {K : ℕ} {x : Lot K} (hx : x ≠ 0) : 0 < x ⬝ᵥ x :=
  lt_of_le_of_ne (Finset.sum_nonneg fun i _ => mul_self_nonneg _)
    (fun h => hx (dotProduct_self_eq_zero.1 h.symm))

private lemma gd_cont {K : ℕ} (d : Lot K) : Continuous fun v : Lot K => v ⬝ᵥ d := by
  unfold dotProduct; fun_prop

private lemma gd_dense {K : ℕ} {d : Lot K} (hd : d ≠ 0) :
    Dense {v : Lot K | v ⬝ᵥ d ≠ 0} := by
  let s : Submodule ℝ (Lot K) :=
    { carrier := {v | v ⬝ᵥ d = 0}
      add_mem' := by
        intro a b ha hb
        simp only [Set.mem_setOf_eq] at *
        rw [add_dotProduct, ha, hb, add_zero]
      zero_mem' := by simp
      smul_mem' := by
        intro c a ha
        simp only [Set.mem_setOf_eq] at *
        rw [smul_dotProduct, ha, smul_zero] }
  have hint : interior (s : Set (Lot K)) = ∅ := by
    by_contra hne
    have htop := s.eq_top_of_nonempty_interior' (Set.nonempty_iff_ne_empty.2 hne)
    have hmem : d ∈ s := htop ▸ Submodule.mem_top
    exact (gd_self_pos hd).ne' hmem
  exact interior_eq_empty_iff_dense_compl.1 hint

/-- For independent `p, q` and a finite `X`, some `v` has `v·p > 0`, `v·q > 0` and is
injective on `X`.
Sketch. `O := {v | 0 < dot v p ∧ 0 < dot v q}` is open (continuity of `v ↦ dot v p`,
`isOpen_lt`). It is nonempty: there is `v₀` with `dot v₀ p = 1 = dot v₀ q` — e.g. extend the
basis `![p, q]` of `span {p, q}` to a linear functional (`LinearIndependent` gives a
`Basis` of the span; `LinearMap.exists_extend` / `Module.Dual` extension), and set
`v₀ k := ℓ (Pi.single k 1)`, so `dot v₀ z = ℓ z`; or solve the 2×2 Gram system, whose
determinant `‖p‖²‖q‖² - (p·q)² > 0` by strict Cauchy–Schwarz.
For distinct `x, y ∈ X`, `Z_{xy} := {v | dot v (x - y) = 0}` is closed with empty interior: if
it contained a ball around `v`, then `dot (v + ε • Pi.single k 1) (x - y) = 0` gives
`(x - y) k = 0` for all `k`, i.e. `x = y`. So each `Z_{xy}ᶜ` is open and dense
(`interior_eq_empty_iff_dense_compl`), the finite intersection `D` of them is dense
(`dense_biInter_of_isOpen` over the finite set `X ×ˢ X` filtered by `≠`, or induction with
`Dense.inter_of_isOpen_left`), and `Dense.inter_open_nonempty` gives `v ∈ O ∩ D`. Then
`dot v x - dot v y = dot v (x - y) ≠ 0` (`dot_eq_dotProduct`, `dotProduct_sub`). -/
theorem exists_generic_dir {K : ℕ} {p q : Lot K} (hpq : LinearIndependent ℝ ![p, q])
    (X : Finset (Lot K)) :
    ∃ v : Lot K, 0 < dot v p ∧ 0 < dot v q ∧
      ∀ x ∈ X, ∀ y ∈ X, x ≠ y → dot v x ≠ dot v y := by
  classical
  simp only [dot_eq_dotProduct]
  have hq : q ≠ 0 := by
    intro h
    have := (LinearIndependent.pair_iff.1 hpq) 0 1 (by simp [h])
    simp at this
  set a := p ⬝ᵥ p
  set b := q ⬝ᵥ q
  set c := p ⬝ᵥ q
  have hb : 0 < b := gd_self_pos hq
  have hx : b • p - c • q ≠ 0 := by
    intro h
    have := (LinearIndependent.pair_iff.1 hpq) b (-c) (by rw [← h]; simp [sub_eq_add_neg])
    exact hb.ne' this.1
  have hxx := gd_self_pos hx
  have hcomm : q ⬝ᵥ p = c := dotProduct_comm _ _
  have hG : 0 < a * b - c * c := by
    have e : (b • p - c • q) ⬝ᵥ (b • p - c • q) = b * (a * b - c * c) := by
      simp only [sub_dotProduct, dotProduct_sub, smul_dotProduct, dotProduct_smul, smul_eq_mul]
      rw [hcomm]; ring
    rw [e] at hxx
    exact pos_of_mul_pos_right hxx hb.le
  set v₀ : Lot K := (b - c) • p + (a - c) • q
  have h0p : v₀ ⬝ᵥ p = a * b - c * c := by
    simp only [v₀, add_dotProduct, smul_dotProduct, smul_eq_mul]; rw [hcomm]; ring
  have h0q : v₀ ⬝ᵥ q = a * b - c * c := by
    simp only [v₀, add_dotProduct, smul_dotProduct, smul_eq_mul]; ring
  let O : Set (Lot K) := {v | 0 < v ⬝ᵥ p ∧ 0 < v ⬝ᵥ q}
  have hO : IsOpen O :=
    (isOpen_lt continuous_const (gd_cont p)).inter (isOpen_lt continuous_const (gd_cont q))
  have hOne : O.Nonempty := ⟨v₀, by simp only [O, Set.mem_setOf_eq, h0p, h0q]; exact ⟨hG, hG⟩⟩
  let S : Set (Lot K × Lot K) := ↑((X ×ˢ X).filter fun z => z.1 ≠ z.2)
  let D : Set (Lot K) := ⋂ z ∈ S, {v | v ⬝ᵥ (z.1 - z.2) ≠ 0}
  have hD : Dense D := by
    refine dense_biInter_of_isOpen (fun z _ => isOpen_ne_fun (gd_cont _) continuous_const)
      (Finset.countable_toSet _) (fun z hz => gd_dense ?_)
    have hz' : z.1 ≠ z.2 := (Finset.mem_filter.1 hz).2
    exact sub_ne_zero.2 hz'
  obtain ⟨v, hvO, hvD⟩ :=hD.inter_open_nonempty O hO hOne
  refine ⟨v, hvO.1, hvO.2, fun x hx y hy hxy => ?_⟩
  have hmem : (x, y) ∈ S := by
    simp only [S, Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_product]
    exact ⟨⟨hx, hy⟩, hxy⟩
  have := Set.mem_iInter₂.1 hvD (x, y) hmem
  simp only [Set.mem_setOf_eq, dotProduct_sub] at this
  exact sub_ne_zero.1 this

end Q3L
