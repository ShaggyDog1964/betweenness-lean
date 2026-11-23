/-
# Q1 sanity checks for `Q1/Statement.lean` (not part of the target)

Machine-checked non-vacuity facts about the definitions:
* `HQC`, `VQC`, `HVQC` are satisfiable (the total-indifference preference).
* Every ranking with at most 2 entries is in R(HVQC), hence in R(HQC) and R(VQC).
* `¬ IsLocal HQC 2` and `¬ IsLocal VQC 2`: the second conjuncts of `hqc_stmt` and
  `vqc_stmt` are proved here. (So those parts are not vacuous and are true.)
* `#eval` of the zigzag family at `n = 4` matches the example in Section 5 of `Q1/Statement.lean`.
-/
import Q1.Statement

namespace Q1

/-- Total indifference. -/
def indiffRel : Rel := fun _ _ => True

theorem indiffRel_weakOrder : IsWeakOrder indiffRel :=
  ⟨fun _ _ => Or.inl trivial, fun _ _ _ _ _ => trivial⟩

theorem indiffRel_hvqc : HVQC indiffRel :=
  ⟨fun _ _ _ _ _ _ _ _ _ => trivial, fun _ _ _ _ _ _ _ _ _ => trivial⟩

theorem hqc_satisfiable : ∃ R, IsWeakOrder R ∧ HQC R :=
  ⟨indiffRel, indiffRel_weakOrder, indiffRel_hvqc.1⟩

theorem vqc_satisfiable : ∃ R, IsWeakOrder R ∧ VQC R :=
  ⟨indiffRel, indiffRel_weakOrder, indiffRel_hvqc.2⟩

/-- "`a` is the unique best point; everything else is indifferent." -/
def topRel (a : Pt) : Rel := fun x y => x = a ∨ y ≠ a

theorem topRel_weakOrder (a : Pt) : IsWeakOrder (topRel a) := by
  refine ⟨fun x y => ?_, fun x y z hxy hyz => ?_⟩
  · by_cases hx : x = a
    · exact Or.inl (Or.inl hx)
    · by_cases hy : y = a
      · exact Or.inr (Or.inl hy)
      · exact Or.inl (Or.inr hy)
  · rcases hxy with h | h
    · exact Or.inl h
    · rcases hyz with h' | h'
      · exact absurd h' h
      · exact Or.inr h'

theorem topRel_hvqc (a : Pt) : HVQC (topRel a) := by
  constructor
  · intro x y z w hyz hwy hw hy hz
    by_cases hx : x = a
    · subst hx
      have hy' : y = x := hy.resolve_right (by simp)
      have hz' : z = x := hz.resolve_right (by simp)
      subst hy'; subst hz'
      left
      simp only [Set.uIcc_self, Set.mem_singleton_iff] at hw
      exact Prod.ext hw hwy
    · exact Or.inr hx
  · intro x y z w hyz hwy hw hy hz
    by_cases hx : x = a
    · subst hx
      have hy' : y = x := hy.resolve_right (by simp)
      have hz' : z = x := hz.resolve_right (by simp)
      subst hy'; subst hz'
      left
      simp only [Set.uIcc_self, Set.mem_singleton_iff] at hw
      exact Prod.ext hwy hw
    · exact Or.inr hx

theorem inR_mono {P Q : Rel → Prop} (h : ∀ R, P R → Q R) {L : List Pt} :
    InR P L → InR Q L := fun ⟨R, hR, hP, hL⟩ => ⟨R, hR, h R hP, hL⟩

/-- Every ranking with at most two entries is in R(HVQC). -/
theorem inR_hvqc_of_length_le_two (L : List Pt) (hnd : L.Nodup) (hl : L.length ≤ 2) :
    InR HVQC L := by
  match L, hnd, hl with
  | [], _, _ => exact ⟨indiffRel, indiffRel_weakOrder, indiffRel_hvqc, by simp⟩
  | [_], _, _ => exact ⟨indiffRel, indiffRel_weakOrder, indiffRel_hvqc, by simp⟩
  | [a, b], hnd, _ =>
    refine ⟨topRel a, topRel_weakOrder a, topRel_hvqc a, ?_⟩
    have hab : a ≠ b := by simpa using hnd
    simp only [List.pairwise_cons, List.mem_singleton, forall_eq, List.not_mem_nil,
      IsEmpty.forall_iff, implies_true, List.Pairwise.nil, and_true]
    refine ⟨Or.inl rfl, ?_⟩
    rintro (h | h)
    · exact hab h.symm
    · exact h rfl
  | _ :: _ :: _ :: _, _, hl => simp at hl

/-- Not 2-local for H-QC: `(0,0) ≻ (2,0) ≻ (1,0)`. -/
theorem not_isLocal_hqc_two : ¬ IsLocal HQC 2 := by
  intro hloc
  have hnd : ([((0:ℝ),(0:ℝ)), (2,0), (1,0)] : List Pt).Nodup := by
    norm_num [Prod.ext_iff]
  obtain ⟨R, hR, hP, hL⟩ := hloc _ hnd (fun L' hsub hl =>
    inR_mono (fun _ h => h.1) (inR_hvqc_of_length_le_two L' (hnd.sublist hsub) hl))
  simp only [List.pairwise_cons, List.mem_cons, forall_eq_or_imp,
    List.not_mem_nil, IsEmpty.forall_iff, implies_true, List.Pairwise.nil,
    and_true] at hL
  obtain ⟨⟨h01, _⟩, h12⟩ := hL
  have hself : R ((2:ℝ),(0:ℝ)) (2,0) := (hR.complete _ _).elim id id
  have := hP (2,0) (0,0) (2,0) (1,0) rfl rfl (by norm_num [Set.uIcc]) h01.1 hself
  exact h12.2 this

/-- Not 2-local for V-QC: `(0,0) ≻ (0,2) ≻ (0,1)`. -/
theorem not_isLocal_vqc_two : ¬ IsLocal VQC 2 := by
  intro hloc
  have hnd : ([((0:ℝ),(0:ℝ)), (0,2), (0,1)] : List Pt).Nodup := by
    norm_num [Prod.ext_iff]
  obtain ⟨R, hR, hP, hL⟩ := hloc _ hnd (fun L' hsub hl =>
    inR_mono (fun _ h => h.2) (inR_hvqc_of_length_le_two L' (hnd.sublist hsub) hl))
  simp only [List.pairwise_cons, List.mem_cons, forall_eq_or_imp,
    List.not_mem_nil, IsEmpty.forall_iff, implies_true, List.Pairwise.nil,
    and_true] at hL
  obtain ⟨⟨h01, _⟩, h12⟩ := hL
  have hself : R ((0:ℝ),(2:ℝ)) (0,2) := (hR.complete _ _).elim id id
  have := hP (0,2) (0,0) (0,2) (0,1) rfl rfl (by norm_num [Set.uIcc]) h01.1 hself
  exact h12.2 this

-- Expected: [(0, 0), (2, 0), (1, 4), (7, 2), (4, 10)] and (4, 6)
#eval ((List.range 5).map endPt, midPt 4)
-- Expected (n = 5): ... (4, 10), (14, 6) and (9, 6)
#eval ((List.range 6).map endPt, midPt 5)

end Q1
