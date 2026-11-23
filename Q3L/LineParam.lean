/-
`line_param`: a collinear `X` is parametrized by a line.
-/
import Q3L.Statement

namespace Q3L

open K4 (Lot)

/-- If `dim V ≤ 1`, all points of `X` are `x₀ + φ(x) d` for one base point `x₀`, one
direction `d` and a real parameter `φ`. (Then `φ` is automatically injective on `X`: equal
parameters give equal points.)
Sketch. If `X = ∅` take anything. Else fix `x₀ ∈ X`. `dirSpace X` has `finrank ≤ 1`, so
it is spanned by one vector: `finrank_le_one_iff` on the module `↥(dirSpace X)` gives `v`
with every element a multiple of `v`; put `d := (v : Lot K)`. For `x ∈ X`,
`x - x₀ ∈ dirSpace X` (`vsub_mem_vectorSpan`), so `x - x₀ = c • d`; define
`φ x := if h : x ∈ X then Classical.choose (…) else 0` (or `choose` on
`∀ x, ∃ c, x ∈ X → x = x₀ + c • d`). -/
theorem line_param {K : ℕ} {X : Finset (Lot K)}
    (hdim : Module.finrank ℝ (dirSpace X) ≤ 1) :
    ∃ (x0 d : Lot K) (φ : Lot K → ℝ), ∀ x ∈ X, x = x0 + φ x • d := by
  classical
  rcases X.eq_empty_or_nonempty with hX | ⟨x0, hx0⟩
  · exact ⟨0, 0, fun _ => 0, by simp [hX]⟩
  obtain ⟨v, hv⟩ := finrank_le_one_iff.mp hdim
  have key : ∀ x, ∃ c : ℝ, x ∈ X → x = x0 + c • (v : Lot K) := by
    intro x
    by_cases hx : x ∈ X
    · have hmem : x - x0 ∈ dirSpace X :=
        vsub_mem_vectorSpan ℝ (show x ∈ (↑X : Set (Lot K)) from hx)
          (show x0 ∈ (↑X : Set (Lot K)) from hx0)
      obtain ⟨c, hc⟩ := hv ⟨x - x0, hmem⟩
      refine ⟨c, fun _ => ?_⟩
      have hc' : c • (v : Lot K) = x - x0 := by
        have := congrArg Subtype.val hc
        simpa using this
      rw [hc']; abel
    · exact ⟨0, fun h => absurd h hx⟩
  choose φ hφ using key
  exact ⟨x0, v, φ, fun x hx => hφ x hx⟩

end Q3L
