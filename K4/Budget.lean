import K4.Defs

namespace K4

private lemma budget_claim (J β v0 : ℕ) (cA cA' : ℕ → ℝ)
    (hblock : ∀ i, i < J → (2 : ℝ) ^ β * cA i < cA' i)
    (hgap : ∀ i, i + 1 < J → cA' i < cA (i + 1))
    (hstart : (2 : ℝ) ^ v0 < cA 0) :
    ∀ i, i < J → (2 : ℝ) ^ (v0 + i * β) < cA i := by
  intro i
  induction i with
  | zero => intro _; simpa using hstart
  | succ k ih =>
    intro hk
    have h1 := ih (by omega)
    have h2 := hblock k (by omega)
    have h3 := hgap k hk
    have hp : (0 : ℝ) < 2 ^ β := by positivity
    have : (2 : ℝ) ^ (v0 + (k + 1) * β) = 2 ^ β * 2 ^ (v0 + k * β) := by
      rw [← pow_add]; congr 1; ring
    rw [this]
    calc (2 : ℝ) ^ β * 2 ^ (v0 + k * β) < 2 ^ β * cA k := mul_lt_mul_of_pos_left h1 hp
      _ < cA' k := h2
      _ < cA (k + 1) := h3

/-- The racetrack budget is exhausted: `J` disjoint rises by factors `> 2^β`, with no
fall in between, cannot fit between `2^v0` and `2^(v0 + Jβ)`.
Sketch: by induction on `i < J`, `2^(v0 + i β) < cA i` (base `hstart`; step
`cA (i+1) > cA' i > 2^β cA i > 2^(v0 + (i+1) β)` by `hgap`, `hblock`, `pow_add`).
At `i = J - 1`: `cA' (J-1) > 2^β cA (J-1) > 2^(v0 + J β)`, contradicting `hend`
(`J - 1 + 1 = J` since `1 ≤ J`). -/
theorem budget_contradiction (J β v0 : ℕ) (hJ : 1 ≤ J) (cA cA' : ℕ → ℝ)
    (hpos : ∀ i, 0 < cA i)
    (hblock : ∀ i, i < J → (2 : ℝ) ^ β * cA i < cA' i)
    (hgap : ∀ i, i + 1 < J → cA' i < cA (i + 1))
    (hstart : (2 : ℝ) ^ v0 < cA 0)
    (hend : cA' (J - 1) < (2 : ℝ) ^ (v0 + J * β)) : False := by
  have h1 := budget_claim J β v0 cA cA' hblock hgap hstart (J - 1) (by omega)
  have h2 := hblock (J - 1) (by omega)
  have hp : (0 : ℝ) < 2 ^ β := by positivity
  have : (2 : ℝ) ^ (v0 + J * β) = 2 ^ β * 2 ^ (v0 + (J - 1) * β) := by
    rw [← pow_add]; congr 1
    obtain ⟨m, rfl⟩ : ∃ m, J = m + 1 := ⟨J - 1, by omega⟩
    simp only [Nat.add_sub_cancel]; ring
  have h3 := mul_lt_mul_of_pos_left h1 hp
  rw [this] at hend
  linarith

end K4
