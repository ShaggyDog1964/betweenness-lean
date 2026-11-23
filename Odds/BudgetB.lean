import Odds.Defs

namespace Odds

/-- Base-`b` racetrack budget: `J` disjoint rises by factors `> b^β`, with no fall in
between, cannot fit between `b^v0` and `b^(v0 + Jβ)`. Only `b > 0` is used.
Sketch: copy `K4.budget_contradiction` (file `K4/Budget.lean`, with its private
`budget_claim`) replacing `2` by `b` (positivity of `b ^ β` from `pow_pos hb`). By induction
on `i < J`, `b^(v0 + i β) < cA i` (step: `cA (i+1) > cA' i > b^β cA i > b^β b^(v0 + iβ)
= b^(v0 + (i+1)β)`, `pow_add`). At `i = J - 1`: `cA' (J-1) > b^β cA (J-1) > b^(v0 + Jβ)`,
contradicting `hend`. -/
theorem budget_contradictionB (b : ℝ) (hb : 0 < b) (J β v0 : ℕ) (hJ : 1 ≤ J)
    (cA cA' : ℕ → ℝ)
    (hpos : ∀ i, 0 < cA i)
    (hblock : ∀ i, i < J → b ^ β * cA i < cA' i)
    (hgap : ∀ i, i + 1 < J → cA' i < cA (i + 1))
    (hstart : b ^ v0 < cA 0)
    (hend : cA' (J - 1) < b ^ (v0 + J * β)) : False := by
  have hbβ : 0 < b ^ β := pow_pos hb β
  have claim : ∀ i, i < J → b ^ (v0 + i * β) < cA i := by
    intro i
    induction i with
    | zero => intro _; simpa using hstart
    | succ k ih =>
      intro hk
      have h1 := ih (by omega)
      have h2 := hblock k (by omega)
      have h3 := hgap k hk
      have h4 : b ^ (v0 + (k + 1) * β) = b ^ β * b ^ (v0 + k * β) := by
        rw [← pow_add]; congr 1; ring
      rw [h4]
      have := mul_lt_mul_of_pos_left h1 hbβ
      linarith
  have h1 := claim (J - 1) (by omega)
  have h2 := hblock (J - 1) (by omega)
  have h4 : b ^ (v0 + J * β) = b ^ β * b ^ (v0 + (J - 1) * β) := by
    rw [← pow_add]; congr 1
    obtain ⟨m, rfl⟩ : ∃ m, J = m + 1 := ⟨J - 1, by omega⟩
    simp only [Nat.add_sub_cancel]; ring
  have := mul_lt_mul_of_pos_left h1 hbβ
  linarith

end Odds
