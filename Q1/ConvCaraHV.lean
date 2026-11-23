import Q1.ConvBridge
import Q1.ZzNotInR
import Q1.ZzCritical
import Q1.ZzNodup
import Q1.ZzLength

/-!
# Orthogonal convexity has no finite Carathéodory number

For each `c`, take the zigzag ranking with `n = c + 1`: `A` is the set of endpoints
`a_0, …, a_n` (the first `n + 1` entries) and `p = p_n` the last entry. The ranking is not
in R(HVQC), so it has an obstruction; deleting the last entry leaves a ranking in R(HVQC),
so the obstruction sits at the last index and `p ∈ hull A`. Any `B ⊆ A` with at most `c`
points misses some `a_k`; deleting position `k` leaves a ranking in R(HVQC), whose last
entry `p` is then outside the hull of the entries above it, which contain `B`.
-/

namespace Q1

/-- If `L` (length `m + 2`) has an obstruction but deleting its last entry removes every
obstruction, then the last entry lies in the hull of the others. -/
theorem p_mem_hull_zz {α : Type*} {C : Set (Set α)} {L : List α} {m : ℕ}
    (hlen : L.length = m + 2) (hnot : ¬ Conv.NoObstruction C L)
    (hlast : Conv.NoObstruction C (L.eraseIdx (m + 1))) :
    L[m + 1]'(by omega) ∈ Conv.hull C {x | x ∈ L.take (m + 1)} := by
  unfold Conv.NoObstruction at hnot
  push Not at hnot
  obtain ⟨j, hj, hj0, hmem⟩ := hnot
  by_cases hjm : j = m + 1
  · subst hjm; exact hmem
  · have hjlt : j < m + 1 := by omega
    have hjl : j < (L.eraseIdx (m + 1)).length := by
      rw [List.length_eraseIdx]; split <;> omega
    apply absurd _ (hlast j hjl hj0)
    rw [List.getElem_eraseIdx_of_lt hjl hjlt]
    have htake : (L.eraseIdx (m + 1)).take j = L.take j := by
      rw [List.eraseIdx_eq_take_drop_succ, List.take_append_of_le_length (by simp; omega),
        List.take_take, Nat.min_eq_left hjlt.le]
    rw [htake]; exact hmem

/-- If deleting position `k ≤ m` of `L` (length `m + 2`) removes every obstruction, then the
last entry is outside the hull of the first `m + 1` entries other than `L[k]`. -/
theorem p_not_mem_hull_erase {α : Type*} {C : Set (Set α)} {L : List α} {m k : ℕ}
    (hlen : L.length = m + 2) (hkm : k ≤ m) (hm : 1 ≤ m)
    (hk : Conv.NoObstruction C (L.eraseIdx k)) :
    L[m + 1]'(by omega) ∉
      Conv.hull C {x | x ∈ L.take (m + 1) ∧ x ≠ L[k]'(by omega)} := by
  have hml : m < (L.eraseIdx k).length := by
    rw [List.length_eraseIdx]; split <;> omega
  have h := hk m hml (by omega)
  rw [List.getElem_eraseIdx_of_ge hml hkm] at h
  intro hmem
  apply h
  refine Conv.hull_mono ?_ hmem
  rintro x ⟨hx, hxk⟩
  obtain ⟨i, hi, rfl⟩ := List.mem_take_iff_getElem.1 hx
  have hi' : i < m + 1 := by omega
  have hik : i ≠ k := fun h => hxk (by subst h; rfl)
  show L[i] ∈ (L.eraseIdx k).take m
  rcases Nat.lt_or_gt_of_ne hik with hlt | hgt
  · have hil : i < (L.eraseIdx k).length := by omega
    rw [List.mem_take_iff_getElem]
    exact ⟨i, by omega, List.getElem_eraseIdx_of_lt hil hlt⟩
  · have hil : i - 1 < (L.eraseIdx k).length := by omega
    rw [List.mem_take_iff_getElem]
    refine ⟨i - 1, by omega, ?_⟩
    rw [List.getElem_eraseIdx_of_ge hil (by omega)]
    congr 1; omega

/-- Orthogonal convexity has no finite Carathéodory bound. -/
theorem cara_HV : cara_HV_stmt := by
  classical
  intro c h
  have hC : Conv.IsConvexity (CH ∩ CV) := (Conv.join Pt CH CV convexity.1 convexity.2).1
  set n := c + 1 with hn
  set L := zigzagList n with hL
  have hlen : L.length = n + 2 := zigzagList_length n
  have hnot : ¬ Conv.NoObstruction (CH ∩ CV) L := fun hno =>
    zz_not_inR n ((inR_HVQC_iff L).2 (Conv.inR_of_noObstruction hC hno))
  have hcrit : ∀ k, k < L.length → Conv.NoObstruction (CH ∩ CV) (L.eraseIdx k) := fun k hk =>
    Conv.noObstruction_of_inR ((inR_HVQC_iff _).1 (zz_critical n k hk))
  set A : Finset Pt := (L.take (n + 1)).toFinset with hA
  have hAcoe : (↑A : Set Pt) = {x | x ∈ L.take (n + 1)} := by ext x; simp [hA]
  have hp := p_mem_hull_zz hlen hnot (hcrit (n + 1) (by omega))
  rw [← hAcoe] at hp
  obtain ⟨B, hBA, hBc, hpB⟩ := h A _ hp
  have hAcard : A.card = n + 1 := by
    rw [hA, List.toFinset_card_of_nodup ((zigzagList_nodup (by omega)).sublist
      (List.take_sublist _ _)), List.length_take, hlen]
    omega
  obtain ⟨a, haA, haB⟩ : ∃ a ∈ A, a ∉ B := by
    by_contra hcon
    push Not at hcon
    have := Finset.card_le_card hcon
    omega
  rw [hA, List.mem_toFinset] at haA
  obtain ⟨k, hk, rfl⟩ := List.mem_take_iff_getElem.1 haA
  have hkn : k ≤ n := by omega
  apply p_not_mem_hull_erase hlen hkn (by omega) (hcrit k (by omega))
  refine Conv.hull_mono ?_ hpB
  intro x hx
  refine ⟨?_, fun hxk => haB (hxk ▸ hx)⟩
  have := hBA hx
  rw [hA, List.mem_toFinset] at this
  exact this

end Q1
