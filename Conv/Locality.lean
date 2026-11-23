import Conv.Upper
import Conv.Lower

/-!
# Locality iff a Carathéodory bound

For `n ≥ 2`, R(UCC C) is `n`-local iff `C` has Carathéodory bound `n - 1`
(`locality_stmt`); hence R(UCC C) is local for some `n` iff some finite Carathéodory bound
exists (`local_iff_finite_stmt`).
-/

namespace Conv

universe u

variable {α : Type u} {C : Set (Set α)}

/-- A Carathéodory bound persists under enlarging the bound. -/
theorem caraBound_mono {c d : ℕ} (h : CaraBound C c) (hcd : c ≤ d) : CaraBound C d := by
  intro A p hp
  obtain ⟨B, hBA, hBc, hpB⟩ := h A p hp
  exact ⟨B, hBA, hBc.trans hcd, hpB⟩

/-- For `n ≥ 2`: `n`-locality iff Carathéodory bound `n - 1`.
Sketch: (←) the upper bound with `c = n - 1 ≥ 1`. (→) shrink a representation to a minimal
`B`; if `card B ≥ n` then `card B ≥ 2` and `card B`-locality (from `n`-locality by
monotonicity) contradicts the lower bound. -/
theorem locality : locality_stmt.{u} := by
  intro α C hC n hn
  constructor
  · intro hloc A p hp
    obtain ⟨B, hBA, hpB, hmin⟩ := exists_minimal hp
    refine ⟨B, hBA, ?_, hpB⟩
    by_contra hlt
    exact not_isLocal_of_minimal hC hpB hmin (by omega) (isLocal_mono hloc (by omega))
  · intro hcb
    have := isLocal_of_caraBound hC (by omega) hcb
    rwa [Nat.sub_add_cancel (by omega : 1 ≤ n)] at this

/-- R(UCC C) is local for some `n` iff some finite Carathéodory bound exists. -/
theorem local_iff_finite : local_iff_finite_stmt.{u} := by
  intro α C hC
  constructor
  · rintro ⟨n, hn⟩
    exact ⟨max n 2 - 1,
      (locality α C hC (max n 2) (le_max_right _ _)).1 (isLocal_mono hn (le_max_left _ _))⟩
  · rintro ⟨c, hc⟩
    exact ⟨max c 1 + 1,
      isLocal_of_caraBound hC (le_max_right _ _) (caraBound_mono hc (le_max_left _ _))⟩

end Conv
