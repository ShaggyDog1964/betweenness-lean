import K4.Defs

namespace K4

/-- Lift of a balanced monotone log-tilt sequence `(u, s, v, w)` to monotone exponents.
Sketch (explicit): with `Δu t = u (t+1) - u t ≥ 0` etc., define
`L3 i = s 0 + ∑ t ∈ Finset.range i, min (Δu t) (Δs t)`, `L2 i = L3 i - s i`,
`L1 i = L3 i - u i`, `L4 i = L2 i + v i`. The three identities hold by definition.
Steps (`monotone_nat_of_le_succ`, `antitone_nat_of_succ_le`, `Finset.sum_range_succ`):
`L3`: `+ min Δu Δs ≥ 0`. `L2`: `min Δu Δs - Δs ≤ 0`. `L1`: `min Δu Δs - Δu ≤ 0`.
`L4`: `min Δu Δs - Δs + Δv`, which is `Δv ≥ 0` if `Δs ≤ Δu`, else `Δu - Δs + Δv = Δw ≥ 0`
(balance `hbal` at `t` and `t+1`). -/
theorem lift_usvw (u s v w : ℕ → ℤ) (hu : Monotone u) (hs : Monotone s) (hv : Monotone v)
    (hw : Monotone w) (hbal : ∀ i, u i + v i = s i + w i) :
    ∃ L1 L2 L3 L4 : ℕ → ℤ, Antitone L1 ∧ Antitone L2 ∧ Monotone L3 ∧ Monotone L4 ∧
      ∀ i, L3 i - L1 i = u i ∧ L3 i - L2 i = s i ∧ L4 i - L2 i = v i := by
  set D : ℕ → ℤ := fun t => min (u (t+1) - u t) (s (t+1) - s t) with hD
  set L3 : ℕ → ℤ := fun i => ∑ t ∈ Finset.range i, D t with hL3
  have hL3s : ∀ n, L3 (n+1) = L3 n + D n := fun n => by
    simp only [hL3, Finset.sum_range_succ]
  refine ⟨fun i => L3 i - u i, fun i => L3 i - s i, L3, fun i => L3 i - s i + v i,
    ?_, ?_, ?_, ?_, ?_⟩
  · refine antitone_nat_of_succ_le fun n => ?_
    have h1 := hL3s n
    have h2 : D n ≤ u (n+1) - u n := min_le_left _ _
    show _ ≤ _; omega
  · refine antitone_nat_of_succ_le fun n => ?_
    have h1 := hL3s n
    have h2 : D n ≤ s (n+1) - s n := min_le_right _ _
    show _ ≤ _; omega
  · refine monotone_nat_of_le_succ fun n => ?_
    have h1 := hL3s n
    have a := hu (Nat.le_add_right n 1)
    have b := hs (Nat.le_add_right n 1)
    have h2 : 0 ≤ D n := le_min (by omega) (by omega)
    omega
  · refine monotone_nat_of_le_succ fun n => ?_
    have h1 := hL3s n
    have a := hv (Nat.le_add_right n 1)
    have b := hw (Nat.le_add_right n 1)
    have c1 := hbal n
    have c2 := hbal (n+1)
    have hDn : D n = min (u (n+1) - u n) (s (n+1) - s n) := rfl
    show _ ≤ _
    rcases le_total (u (n+1) - u n) (s (n+1) - s n) with h | h
    · rw [min_eq_left h] at hDn; omega
    · rw [min_eq_right h] at hDn; omega
  · intro i
    refine ⟨by ring, by ring, by ring⟩

end K4
