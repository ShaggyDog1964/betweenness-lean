import Q2CL.Defs

namespace Q2CL

open K4

private lemma floor_eq_close {η a b : ℝ} (hη : 0 < η) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (h : ⌊a / η⌋₊ = ⌊b / η⌋₊) : |a - b| < η := by
  have h1 := Nat.floor_le (div_nonneg ha hη.le)
  have h2 := Nat.lt_floor_add_one (a / η)
  have h3 := Nat.floor_le (div_nonneg hb hη.le)
  have h4 := Nat.lt_floor_add_one (b / η)
  rw [h] at h1 h2
  have e1 : a = (a / η) * η := by field_simp
  have e2 : b = (b / η) * η := by field_simp
  rw [abs_lt]
  constructor
  · rw [e1, e2]; nlinarith
  · rw [e1, e2]; nlinarith

/-- Theorem 31(1) (packing): a δ-separated list of distinct lotteries in Δ³ has at most
`(3/δ + 1)^3` entries. -/
theorem packing (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (L : List (Lot 4)) (hL : L.Nodup)
    (hmem : ∀ x ∈ L, x ∈ Simplex 4) (hsep : SepGe δ L) :
    (L.length : ℝ) ≤ (3 / δ + 1) ^ 3 := by
  set η : ℝ := δ / 3 with hηdef
  have hη : 0 < η := by positivity
  set N : ℕ := ⌊1 / η⌋₊ + 1 with hN
  let b : Lot 4 → ℕ × ℕ × ℕ := fun x => (⌊x 1 / η⌋₊, ⌊x 2 / η⌋₊, ⌊x 3 / η⌋₊)
  let T : Finset (ℕ × ℕ × ℕ) :=
    Finset.range N ×ˢ Finset.range N ×ˢ Finset.range N
  have coord : ∀ x ∈ L, ∀ i : Fin 4, 0 ≤ x i ∧ x i ≤ 1 := by
    intro x hx i
    obtain ⟨hnn, hs⟩ := hmem x hx
    rw [Fin.sum_univ_four] at hs
    refine ⟨hnn i, ?_⟩
    have := hnn 0; have := hnn 1; have := hnn 2; have := hnn 3
    fin_cases i <;> simp <;> linarith
  have inN : ∀ x ∈ L, ∀ i : Fin 4, ⌊x i / η⌋₊ < N := by
    intro x hx i
    have := coord x hx i
    have : ⌊x i / η⌋₊ ≤ ⌊1 / η⌋₊ :=
      Nat.floor_le_floor (div_le_div_of_nonneg_right this.2 hη.le)
    omega
  have hmaps : Set.MapsTo b (L.toFinset : Set (Lot 4)) (T : Set (ℕ × ℕ × ℕ)) := by
    intro x hx
    have hx' : x ∈ L := by simpa using hx
    simp only [T, b, Finset.coe_product, Set.mem_prod, Finset.coe_range, Set.mem_Iio]
    exact ⟨inN x hx' 1, inN x hx' 2, inN x hx' 3⟩
  have hinj : Set.InjOn b (L.toFinset : Set (Lot 4)) := by
    intro x hx y hy hxy
    have hx' : x ∈ L := by simpa using hx
    have hy' : y ∈ L := by simpa using hy
    simp only [b, Prod.mk.injEq] at hxy
    obtain ⟨e1, e2, e3⟩ := hxy
    have c1 := floor_eq_close hη (coord x hx' 1).1 (coord y hy' 1).1 e1
    have c2 := floor_eq_close hη (coord x hx' 2).1 (coord y hy' 2).1 e2
    have c3 := floor_eq_close hη (coord x hx' 3).1 (coord y hy' 3).1 e3
    have sx := (hmem x hx').2
    have sy := (hmem y hy').2
    rw [Fin.sum_univ_four] at sx sy
    by_contra hne
    obtain ⟨i, hi⟩ := hsep x hx' y hy' hne
    rw [abs_lt] at c1 c2 c3
    fin_cases i
    · simp at hi
      have : x 0 - y 0 = -(x 1 - y 1) - (x 2 - y 2) - (x 3 - y 3) := by linarith
      rw [this] at hi
      have : |-(x 1 - y 1) - (x 2 - y 2) - (x 3 - y 3)| < δ := by
        rw [abs_lt]; constructor <;> linarith
      linarith
    · simp at hi; rw [← abs_lt] at c1; linarith
    · simp at hi; rw [← abs_lt] at c2; linarith
    · simp at hi; rw [← abs_lt] at c3; linarith
  have hcard : L.toFinset.card ≤ T.card := Finset.card_le_card_of_injOn b hmaps hinj
  have hTc : T.card = N ^ 3 := by
    simp [T, Finset.card_product]; ring
  rw [List.toFinset_card_of_nodup hL, hTc] at hcard
  have hNle : (N : ℝ) ≤ 3 / δ + 1 := by
    rw [hN]; push_cast
    have := Nat.floor_le (show (0:ℝ) ≤ 1 / η by positivity)
    have h3 : 1 / η = 3 / δ := by rw [hηdef]; field_simp
    linarith
  calc (L.length : ℝ) ≤ ((N ^ 3 : ℕ) : ℝ) := by exact_mod_cast hcard
    _ = (N : ℝ) ^ 3 := by push_cast; ring
    _ ≤ (3 / δ + 1) ^ 3 := pow_le_pow_left₀ (by positivity) hNle 3

end Q2CL
