import K4.Defs
import K4.MixMem

namespace K4

/-- Intermediate value theorem on a segment, from closed contour sets and completeness.
Sketch: let `φ : Icc 0 1 → Simplex K`, `t ↦ mix t q r` (continuous, lands in the simplex by
`mix_mem_simplex`). `A = φ⁻¹ {x | R x l}` and `B = φ⁻¹ {x | R l x}` are closed
(`hR.closed_upper`, `hR.closed_lower`), cover `Icc 0 1` (`hR.complete`), `1 ∈ A`
(`mix 1 q r = q`), `0 ∈ B` (`mix 0 q r = r`). `Icc 0 1` is preconnected
(`isPreconnected_Icc`, `isPreconnected_closed_iff`), so `A ∩ B` is nonempty; a common
point `t` gives `Indiff R (mix t q r) l`. -/
theorem exists_indiff_on_segment {K : ℕ} {R : Rel K} (hR : IsBetweennessPref R)
    {q r l : Lot K} (hq : q ∈ Simplex K) (hr : r ∈ Simplex K) (hl : l ∈ Simplex K)
    (hql : R q l) (hlr : R l r) : ∃ t ∈ Set.Icc (0 : ℝ) 1, Indiff R (mix t q r) l := by
  have : PreconnectedSpace (Set.Icc (0 : ℝ) 1) :=
    Subtype.preconnectedSpace isPreconnected_Icc
  let φ : Set.Icc (0 : ℝ) 1 → Simplex K := fun t =>
    ⟨mix t.1 q r, mix_mem_simplex hq hr t.2.1 t.2.2⟩
  have hφ : Continuous φ := by
    apply Continuous.subtype_mk
    unfold mix
    fun_prop
  have hA : IsClosed (φ ⁻¹' {x : Simplex K | R x.1 l}) :=
    (hR.closed_upper l hl).preimage hφ
  have hB : IsClosed (φ ⁻¹' {x : Simplex K | R l x.1}) :=
    (hR.closed_lower l hl).preimage hφ
  have hcov : (Set.univ : Set (Set.Icc (0 : ℝ) 1)) ⊆
      φ ⁻¹' {x : Simplex K | R x.1 l} ∪ φ ⁻¹' {x : Simplex K | R l x.1} := by
    intro t _
    exact hR.complete _ (φ t).2 l hl
  have h1 : (⟨1, by simp⟩ : Set.Icc (0 : ℝ) 1) ∈ φ ⁻¹' {x : Simplex K | R x.1 l} := by
    show R (mix 1 q r) l
    have : mix 1 q r = q := by simp [mix]
    rw [this]; exact hql
  have h0 : (⟨0, by simp⟩ : Set.Icc (0 : ℝ) 1) ∈ φ ⁻¹' {x : Simplex K | R l x.1} := by
    show R l (mix 0 q r)
    have : mix 0 q r = r := by simp [mix]
    rw [this]; exact hlr
  obtain ⟨t, -, htA, htB⟩ :=
    (isPreconnected_closed_iff.mp isPreconnected_univ) _ _ hA hB hcov
      ⟨_, Set.mem_univ _, h1⟩ ⟨_, Set.mem_univ _, h0⟩
  exact ⟨t.1, t.2, htA, htB⟩

end K4
