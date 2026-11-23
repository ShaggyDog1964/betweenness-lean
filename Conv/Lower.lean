import Conv.Char

/-!
# Lower bound: a minimal hull representation defeats locality

If `p` lies in the hull of `B` but of no proper subset, and `card B ≥ 2`, then R(UCC C) is
not `card B`-local: the ranking `B.toList ++ [p]` passes every smaller test but fails.
-/

namespace Conv

universe u

variable {α : Type u} {C : Set (Set α)}

/-- Every hull representation shrinks to an inclusion-minimal one.
Sketch: among subsets of `A` whose hull contains `p`, take one of least cardinality. -/
theorem exists_minimal {A : Finset α} {p : α} (h : p ∈ hull C ↑A) :
    ∃ B ⊆ A, p ∈ hull C ↑B ∧ ∀ B' ⊂ B, p ∉ hull C ↑B' := by
  classical
  obtain ⟨B, hB, hmin⟩ := (A.powerset.filter fun B : Finset α => p ∈ hull C ↑B).exists_min_image
    Finset.card ⟨A, by simp [h]⟩
  simp only [Finset.mem_filter, Finset.mem_powerset] at hB hmin
  refine ⟨B, hB.1, hB.2, fun B' hB' hp => ?_⟩
  have := hmin B' ⟨hB'.subset.trans hB.1, hp⟩
  exact absurd (Finset.card_lt_card hB') (not_lt.2 this)

/-- Appending a point outside the hull of a nonempty obstruction-free list keeps it
obstruction-free. -/
theorem noObstruction_concat {l : List α} {p : α} (h : NoObstruction C l)
    (hp : 0 < l.length → p ∉ hull C {x | x ∈ l}) : NoObstruction C (l ++ [p]) := by
  intro j hj hj0
  simp only [List.length_append, List.length_singleton] at hj
  rcases Nat.lt_or_ge j l.length with hlt | hge
  · rw [List.getElem_append_left hlt, List.take_append_of_le_length hlt.le]
    exact h j hlt hj0
  · have hjl : j = l.length := by omega
    subst hjl
    simpa using hp hj0

/-- A sublist of `B.toList` has no obstruction when no `b ∈ B` lies in `hull (B.erase b)`. -/
theorem noObstruction_of_sublist_toList [DecidableEq α] {B : Finset α} {l : List α}
    (hl : l.Sublist B.toList) (hind : ∀ b ∈ B, b ∉ hull C ↑(B.erase b)) :
    NoObstruction C l := by
  intro j hj hj0 hmem
  have hnd : l.Nodup := B.nodup_toList.sublist hl
  have hx : l[j] ∈ B := Finset.mem_toList.1 (hl.subset (List.getElem_mem hj))
  apply hind _ hx
  refine hull_mono (fun e he => ?_) hmem
  obtain ⟨i, hi, rfl⟩ := List.mem_take_iff_getElem.1 he
  have hil : i < l.length := by omega
  refine Finset.mem_erase.2 ⟨fun heq => ?_, Finset.mem_toList.1 (hl.subset (List.getElem_mem hil))⟩
  have := (hnd.getElem_inj_iff).1 heq
  omega

/-- A minimal hull representation with at least two points defeats `card B`-locality.
Sketch: `p ∉ B` (else `p ∈ hull {p}` with `{p} ⊂ B`); no `b ∈ B` lies in
`hull (B.erase b)` (else `hull B = hull (B.erase b)` by absorption). The ranking
`B.toList ++ [p]` is nodup and has an obstruction at `p`. A sublist of length `≤ card B`
is `l₁` or `l₁ ++ [p]` with `l₁ <+ B.toList`; `l₁` has no obstruction, and in the second
case `l₁` misses some `y ∈ B`, so `p ∉ hull l₁ ⊆ hull (B.erase y)`. -/
theorem not_isLocal_of_minimal (hC : IsConvexity C) {B : Finset α} {p : α}
    (hB : p ∈ hull C ↑B) (hmin : ∀ B' ⊂ B, p ∉ hull C ↑B') (h2 : 2 ≤ B.card) :
    ¬ IsLocal (UCC C) B.card := by
  classical
  intro hloc
  have hpB : p ∉ B := by
    intro hp
    refine hmin {p} ?_ (by simpa using subset_hull C {p} rfl)
    refine Finset.ssubset_iff_subset_ne.2 ⟨by simpa using hp, fun heq => ?_⟩
    rw [← heq] at h2
    simp at h2
  have hind : ∀ b ∈ B, b ∉ hull C ↑(B.erase b) := by
    intro b hb hbh
    have hBe : (↑B : Set α) = insert b ↑(B.erase b) := by
      rw [← Finset.coe_insert, Finset.insert_erase hb]
    rw [hBe, mem_hull_insert_iff_absorb hC hbh] at hB
    exact hmin _ (Finset.erase_ssubset hb) hB
  have hset : {x | x ∈ B.toList} = (↑B : Set α) := by ext; simp
  have hnd : (B.toList ++ [p]).Nodup := by
    rw [List.nodup_append]
    refine ⟨B.nodup_toList, List.nodup_singleton p, ?_⟩
    intro a ha b hb
    simp only [List.mem_singleton] at hb
    subst hb
    rintro rfl
    exact hpB (Finset.mem_toList.1 ha)
  have hfail : ¬ InR (UCC C) (B.toList ++ [p]) := by
    intro hin
    have := (char _ C hC _).1 hin B.toList.length (by simp)
      (by rw [Finset.length_toList]; omega)
    apply this
    simpa [hset] using hB
  apply hfail
  refine hloc _ hnd fun L' hs hlen => (char _ C hC L').2 ?_
  obtain ⟨l₁, l₂, rfl, hl₁, hl₂⟩ := List.sublist_append_iff.1 hs
  have hno₁ := noObstruction_of_sublist_toList hl₁ hind
  rcases List.sublist_singleton.1 hl₂ with rfl | rfl
  · simpa using hno₁
  · refine noObstruction_concat hno₁ fun _ hp => ?_
    simp only [List.length_append, List.length_singleton] at hlen
    obtain ⟨y, hyB, hyl⟩ : ∃ y ∈ B, y ∉ l₁ := by
      by_contra hc
      push Not at hc
      have : B ⊆ l₁.toFinset := fun y hy => List.mem_toFinset.2 (hc y hy)
      have := (Finset.card_le_card this).trans (List.toFinset_card_le l₁)
      omega
    refine hmin _ (Finset.erase_ssubset hyB) (hull_mono (fun e he => ?_) hp)
    have he' : e ∈ B := Finset.mem_toList.1 (hl₁.subset he)
    exact Finset.mem_erase.2 ⟨fun h => hyl (h ▸ he), he'⟩

end Conv
