/-
`linIndep_swap`: the second order `a ≻ c ≻ b` also comes from an independent
pair, and `a, b, c` are distinct.
-/
import Q3L.Statement

namespace Q3L

open K4 (Lot)

/-- If `a - b, b - c` are independent, so are `a - c, c - b`, and `a, b, c` are distinct.
Sketch. `LinearIndependent.pair_iff`. For the pair: `s • (a - c) + t • (c - b) =
s • (a - b) + (s - t) • (b - c)` (`module`/`abel`), so `s = 0` and `s - t = 0`.
Distinctness: `a = b` makes the first vector `0` (take `s = 1, t = 0`); `b = c` makes the
second `0`; `a = c` gives `1 • (a - b) + 1 • (b - c) = 0`. -/
theorem linIndep_swap {K : ℕ} {a b c : Lot K} (h : LinearIndependent ℝ ![a - b, b - c]) :
    LinearIndependent ℝ ![a - c, c - b] ∧ a ≠ b ∧ b ≠ c ∧ a ≠ c := by
  rw [LinearIndependent.pair_iff] at h
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [LinearIndependent.pair_iff]
    intro s t hst
    have key : s • (a - b) + (s - t) • (b - c) = 0 := by
      rw [← hst]; module
    obtain ⟨h1, h2⟩ := h s (s - t) key
    exact ⟨h1, by linarith⟩
  · rintro rfl
    have := (h 1 0 (by simp)).1
    norm_num at this
  · rintro rfl
    have := (h 0 1 (by simp)).2
    norm_num at this
  · rintro rfl
    have := (h 1 1 (by simp)).1
    norm_num at this

end Q3L
