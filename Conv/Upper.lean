import Conv.Char

/-!
# Upper bound: a Carathéodory bound gives locality

If `C` has Carathéodory bound `c ≥ 1`, then R(UCC C) is `(c+1)`-local.
-/

namespace Conv

universe u

variable {α : Type u} {C : Set (Set α)}

/-- R(UCC C) is `(c+1)`-local when `C` has Carathéodory bound `c ≥ 1`.
Sketch: if `L[j] ∈ hull (take j)`, `CaraBound` on `(L.take j).toFinset` gives `B` with
`card B ≤ c` and `L[j] ∈ hull B`; if `B = ∅` replace it by `{L[0]}` (this uses `c ≥ 1`).
The sublist `(L.take j).filter (· ∈ B) ++ [L[j]]` has length `card B + 1 ≤ c + 1` and an
obstruction at its last position, so it fails the test. -/
theorem isLocal_of_caraBound (hC : IsConvexity C) {c : ℕ} (hc : 1 ≤ c) (h : CaraBound C c) :
    IsLocal (UCC C) (c + 1) := by
  classical
  intro L hL hloc
  refine (char _ C hC L).2 fun j hj hj0 hmem => ?_
  set A : Finset α := (L.take j).toFinset with hAdef
  have hA : (↑A : Set α) = {x | x ∈ L.take j} := by
    ext x; simp [hAdef]
  rw [← hA] at hmem
  -- a nonempty small subset `B` of `A` with `L[j]` in its hull
  obtain ⟨B, hBA, hBne, hBc, hpB⟩ : ∃ B ⊆ A, B.Nonempty ∧ B.card ≤ c ∧ L[j] ∈ hull C ↑B := by
    obtain ⟨B, hBA, hBc, hpB⟩ := h A L[j] hmem
    rcases B.eq_empty_or_nonempty with rfl | hne
    · have h0 : L[0] ∈ A := by
        simp only [hAdef, List.mem_toFinset]
        exact List.mem_take_iff_getElem.2 ⟨0, by omega, rfl⟩
      refine ⟨{L[0]}, by simpa using h0, by simp, by simpa using hc, ?_⟩
      exact hull_mono (by simp) hpB
    · exact ⟨B, hBA, hne, hBc, hpB⟩
  set F := (L.take j).filter (· ∈ B) with hFdef
  have hmemF : ∀ x, x ∈ F ↔ x ∈ B := by
    intro x
    simp only [hFdef, List.mem_filter, decide_eq_true_eq]
    exact ⟨fun h => h.2, fun hx => ⟨by simpa [hAdef] using hBA hx, hx⟩⟩
  have hFnodup : F.Nodup := (hL.sublist (List.take_sublist j L)).filter _
  have hFlen : F.length = B.card := by
    rw [← List.toFinset_card_of_nodup hFnodup]
    congr 1
    ext x; simp [hmemF]
  have hFpos : 0 < F.length := by
    obtain ⟨b, hb⟩ := hBne
    exact List.length_pos_of_mem ((hmemF b).2 hb)
  -- the short sublist
  have hsub : (F ++ [L[j]]).Sublist L := by
    have hd : L.drop j = L[j] :: L.drop (j + 1) := List.drop_eq_getElem_cons hj
    have : (F ++ [L[j]]).Sublist (L.take j ++ L.drop j) := by
      exact (List.filter_sublist).append
        (List.singleton_sublist.2 (by rw [hd]; exact List.mem_cons_self ..))
    simpa using this
  have hin := hloc _ hsub (by simp; omega)
  have hno := (char _ C hC _).1 hin F.length (by simp) hFpos
  apply hno
  have hset : {x | x ∈ F} = (↑B : Set α) := by
    ext x; simp [hmemF]
  have htake : (F ++ [L[j]]).take F.length = F := by simp
  have hget : (F ++ [L[j]])[F.length]'(by simp) = L[j] := by simp
  rw [hget, htake, hset]
  exact hpB

end Conv
