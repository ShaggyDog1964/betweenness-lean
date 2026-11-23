/-
`nested_min_up`: Lemma 44(1), up-closed case.
-/
import Q3L.Statement
import Q3L.NestedMin

namespace Q3L

open K4 (Lot)

open Classical in
/-- Lemma 44(1), up-closed version.
Sketch. Apply `nested_min_down` with labels `fun i => - η i`: `-η j ≤ -η i ↔ η i ≤ η j`
(`neg_le_neg_iff`), so up-closed for `η` is down-closed for `-η`. -/
theorem nested_min_up {K n : ℕ} (w : Fin n → ℝ) (hw0 : ∀ i, 0 ≤ w i)
    (hw1 : ∑ i, w i = 1) (η : Fin n → ℝ) (S : Finset (Lot K)) (P : Lot K → Fin n → Prop)
    (hP : ∀ c ∈ S, ∀ i j, η i ≤ η j → P c i → P c j) :
    (∑ i, if (∀ c ∈ S, P c i) then w i else 0) =
      minOr1 S (fun c => ∑ i, if P c i then w i else 0) := by
  exact nested_min_down w hw0 hw1 (fun i => - η i) S P
    (fun c hc i j h => hP c hc i j (neg_le_neg_iff.mp h))

end Q3L
