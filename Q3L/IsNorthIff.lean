/-
`isNorth_iff`: `IsNorth` reads off the unique `β` coefficient.
-/
import Q3L.Statement

namespace Q3L

open K4 (Lot)

/-- With `d0, g` independent and `x - y = α d0 + β g`, `y` is north of `x` iff `β > 0`.
Sketch. (⇐) `⟨α, β, h, hβ⟩`. (⇒) From `⟨α', β', h', hβ'⟩`,
`(α - α') • d0 + (β - β') • g = 0` (subtract `h'` from `h`); `LinearIndependent.pair_iff`
gives `β = β'`, so `0 < β`. -/
theorem isNorth_iff {K : ℕ} {d0 g x y : Lot K} (hind : LinearIndependent ℝ ![d0, g])
    {α β : ℝ} (h : x - y = α • d0 + β • g) : IsNorth d0 g x y ↔ 0 < β := by
  constructor
  · rintro ⟨α', β', h', hβ'⟩
    have h0 : (α - α') • d0 + (β - β') • g = 0 := by
      rw [sub_smul, sub_smul]
      have : α • d0 + β • g = α' • d0 + β' • g := h.symm.trans h'
      rw [show α • d0 - α' • d0 + (β • g - β' • g)
          = (α • d0 + β • g) - (α' • d0 + β' • g) by abel, this, sub_self]
    have := (LinearIndependent.pair_iff.mp hind) _ _ h0
    have hb : β = β' := by linarith [this.2]
    rw [hb]; exact hβ'
  · intro hβ
    exact ⟨α, β, h, hβ⟩

end Q3L
