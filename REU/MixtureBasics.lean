/-
# Generic facts about finite mixtures

`mass w P = Σ_i w_i [P i]` is the weight of the event `P` under weights `w`. Facts:
* monotonicity / congruence / bounds of `mass`;
* `minOr1` (min with `min ∅ = 1`) basics;
* **nested events**: if the events `P b` (`b ∈ S`) are totally ordered by inclusion (e.g. all
  down-closed in a common scalar `τ`), then `mass (⋂_b P b) = minOr1 S (mass ∘ P)`;
* **threshold intersection** (`sum_threshold_inter`): if `E` is down-closed and `F` up-closed in
  a common scalar `τ`, then `mass (E ∩ F) = max 0 (mass E + mass F - 1)`.
-/
import REU.LevelSets

namespace REU

variable {ι : Type*} [Fintype ι]

open Classical in
/-- Weight of the event `P` under the weights `w`: `Σ_i w_i [P i]`. -/
noncomputable def mass (w : ι → ℝ) (P : ι → Prop) : ℝ := ∑ i, if P i then w i else 0

/-! ## Basic facts about `mass` -/

lemma mass_congr (w : ι → ℝ) {P Q : ι → Prop} (h : ∀ i, P i ↔ Q i) : mass w P = mass w Q := by
  have : P = Q := funext fun i => propext (h i)
  subst this; rfl

lemma mass_mono {w : ι → ℝ} (hw : ∀ i, 0 ≤ w i) {P Q : ι → Prop} (h : ∀ i, P i → Q i) :
    mass w P ≤ mass w Q := by
  unfold mass
  refine Finset.sum_le_sum fun i _ => ?_
  by_cases hp : P i
  · simp [hp, h i hp]
  · by_cases hq : Q i <;> simp [hp, hq, hw i]

lemma mass_nonneg {w : ι → ℝ} (hw : ∀ i, 0 ≤ w i) (P : ι → Prop) : 0 ≤ mass w P := by
  unfold mass
  exact Finset.sum_nonneg fun i _ => by by_cases hp : P i <;> simp [hp, hw i]

lemma mass_true (w : ι → ℝ) : mass w (fun _ => True) = ∑ i, w i := by
  simp [mass]

lemma mass_le_one {w : ι → ℝ} (hw : ∀ i, 0 ≤ w i) (hsum : ∑ i, w i = 1) (P : ι → Prop) :
    mass w P ≤ 1 :=
  (mass_mono hw (fun _ _ => trivial)).trans (by rw [mass_true, hsum])

/-! ## `minOr1` basics -/

lemma minOr1_empty (g : Pt → ℝ) : minOr1 ∅ g = 1 := by
  unfold minOr1; simp

lemma mass_false (w : ι → ℝ) : mass w (fun _ => False) = 0 := by
  simp [mass]

lemma minOr1_le {S : Finset Pt} {g : Pt → ℝ} {y : Pt} (hy : y ∈ S) : minOr1 S g ≤ g y := by
  unfold minOr1
  rw [dite_eq_left ⟨y, hy⟩]
  exact Finset.inf'_le g hy

lemma le_minOr1 {S : Finset Pt} {g : Pt → ℝ} {c : ℝ} (hc : c ≤ 1) (h : ∀ y ∈ S, c ≤ g y) :
    c ≤ minOr1 S g := by
  unfold minOr1
  split_ifs with hS
  · exact Finset.le_inf' hS g h
  · exact hc

lemma minOr1_cases (S : Finset Pt) (g : Pt → ℝ) :
    minOr1 S g = 1 ∨ ∃ y ∈ S, minOr1 S g = g y := by
  unfold minOr1
  split_ifs with hS
  · obtain ⟨y, hy, he⟩ := Finset.exists_mem_eq_inf' hS g
    exact Or.inr ⟨y, hy, he⟩
  · exact Or.inl rfl

lemma minOr1_le_one {S : Finset Pt} {g : Pt → ℝ} (h : ∀ y ∈ S, g y ≤ 1) : minOr1 S g ≤ 1 := by
  rcases minOr1_cases S g with h' | ⟨y, hy, he⟩
  · exact h'.le
  · rw [he]; exact h y hy

lemma minOr1_nonneg {S : Finset Pt} {g : Pt → ℝ} (h : ∀ y ∈ S, 0 ≤ g y) : 0 ≤ minOr1 S g :=
  le_minOr1 zero_le_one h

lemma minOr1_congr {S : Finset Pt} {g g' : Pt → ℝ} (h : ∀ y ∈ S, g y = g' y) :
    minOr1 S g = minOr1 S g' := by
  unfold minOr1
  split_ifs with hS
  · exact Finset.inf'_congr hS rfl h
  · rfl

lemma minOr1_eq_zero {S : Finset Pt} {g : Pt → ℝ} {y : Pt} (hy : y ∈ S) (h0 : g y = 0)
    (hnn : ∀ y ∈ S, 0 ≤ g y) : minOr1 S g = 0 :=
  le_antisymm ((minOr1_le hy).trans h0.le) (minOr1_nonneg hnn)

/-- Adding or removing elements whose value is `1` does not change `minOr1` (values `≤ 1`). -/
lemma minOr1_congr_one {S T : Finset Pt} {g : Pt → ℝ} (hS1 : ∀ y ∈ S, g y ≤ 1)
    (hT1 : ∀ y ∈ T, g y ≤ 1) (hST : ∀ y ∈ S, y ∉ T → g y = 1)
    (hTS : ∀ y ∈ T, y ∉ S → g y = 1) : minOr1 S g = minOr1 T g := by
  have key : ∀ {S T : Finset Pt}, (∀ y ∈ S, g y ≤ 1) → (∀ y ∈ T, y ∉ S → g y = 1) →
      minOr1 S g ≤ minOr1 T g := by
    intro S T hS1 hTS
    rcases minOr1_cases T g with h | ⟨y, hy, he⟩
    · rw [h]; exact minOr1_le_one hS1
    · rw [he]
      by_cases hyS : y ∈ S
      · exact minOr1_le hyS
      · rw [hTS y hy hyS]; exact minOr1_le_one hS1
  exact le_antisymm (key hS1 hTS) (key hT1 hST)

/-! ## Nested events -/

omit [Fintype ι] in
/-- A finite nonempty family of events totally ordered by inclusion has a least member. -/
lemma exists_least_event {α : Type*} [DecidableEq α] (S : Finset α) (hS : S.Nonempty)
    (P : α → ι → Prop)
    (hnest : ∀ b ∈ S, ∀ c ∈ S, (∀ i, P b i → P c i) ∨ (∀ i, P c i → P b i)) :
    ∃ b ∈ S, ∀ c ∈ S, ∀ i, P b i → P c i := by
  induction S using Finset.induction_on with
  | empty => exact absurd hS Finset.not_nonempty_empty
  | insert a S ha ih =>
    rcases S.eq_empty_or_nonempty with rfl | hne
    · refine ⟨a, Finset.mem_insert_self a ∅, fun c hc i h => ?_⟩
      have hca : c = a := by simpa using hc
      subst hca; exact h
    · obtain ⟨b, hb, hbmin⟩ := ih hne fun b hb c hc =>
        hnest b (Finset.mem_insert_of_mem hb) c (Finset.mem_insert_of_mem hc)
      rcases hnest a (Finset.mem_insert_self a S) b (Finset.mem_insert_of_mem hb) with hab | hba
      · refine ⟨a, Finset.mem_insert_self a S, fun c hc i h => ?_⟩
        rcases Finset.mem_insert.1 hc with rfl | hc
        · exact h
        · exact hbmin c hc i (hab i h)
      · refine ⟨b, Finset.mem_insert_of_mem hb, fun c hc i h => ?_⟩
        rcases Finset.mem_insert.1 hc with rfl | hc
        · exact hba i h
        · exact hbmin c hc i h

omit [Fintype ι] in
/-- Two events, both down-closed in the same scalar `τ`, are nested. -/
lemma nested_of_down (τ : ι → ℝ) {P Q : ι → Prop} (hP : ∀ i j, τ j ≤ τ i → P i → P j)
    (hQ : ∀ i j, τ j ≤ τ i → Q i → Q j) : (∀ i, P i → Q i) ∨ (∀ i, Q i → P i) := by
  by_contra hcon
  push Not at hcon
  obtain ⟨⟨i, hPi, hQi⟩, ⟨j, hQj, hPj⟩⟩ := hcon
  rcases le_total (τ i) (τ j) with h | h
  · exact hQi (hQ j i h hQj)
  · exact hPj (hP i j h hPi)

/-- **Nested events**: the mass of the intersection of a nested family is the minimum mass
(with `min ∅ = 1`). -/
lemma mass_forall_nested {w : ι → ℝ} (hw : ∀ i, 0 ≤ w i) (hsum : ∑ i, w i = 1) (S : Finset Pt)
    (P : Pt → ι → Prop)
    (hnest : ∀ b ∈ S, ∀ c ∈ S, (∀ i, P b i → P c i) ∨ (∀ i, P c i → P b i)) :
    mass w (fun i => ∀ b ∈ S, P b i) = minOr1 S (fun b => mass w (P b)) := by
  rcases S.eq_empty_or_nonempty with rfl | hne
  · rw [minOr1_empty, mass_congr w (fun i => show (∀ b ∈ (∅ : Finset Pt), P b i) ↔ True by simp),
      mass_true, hsum]
  · obtain ⟨b, hb, hmin⟩ := exists_least_event S hne P hnest
    have h1 : mass w (fun i => ∀ c ∈ S, P c i) = mass w (P b) :=
      mass_congr w fun i => ⟨fun h => h b hb, fun h c hc => hmin c hc i h⟩
    rw [h1]
    apply le_antisymm
    · exact le_minOr1 (mass_le_one hw hsum _) fun c hc => mass_mono hw (hmin c hc)
    · exact minOr1_le (g := fun b => mass w (P b)) hb

/-- Nested events, down-closed version. -/
lemma mass_forall_down {w : ι → ℝ} (hw : ∀ i, 0 ≤ w i) (hsum : ∑ i, w i = 1) (τ : ι → ℝ)
    (S : Finset Pt) (P : Pt → ι → Prop) (hdown : ∀ b ∈ S, ∀ i j, τ j ≤ τ i → P b i → P b j) :
    mass w (fun i => ∀ b ∈ S, P b i) = minOr1 S (fun b => mass w (P b)) :=
  mass_forall_nested hw hsum S P fun b hb c hc => nested_of_down τ (hdown b hb) (hdown c hc)

/-- Nested events, up-closed version. -/
lemma mass_forall_up {w : ι → ℝ} (hw : ∀ i, 0 ≤ w i) (hsum : ∑ i, w i = 1) (τ : ι → ℝ)
    (S : Finset Pt) (P : Pt → ι → Prop) (hup : ∀ b ∈ S, ∀ i j, τ i ≤ τ j → P b i → P b j) :
    mass w (fun i => ∀ b ∈ S, P b i) = minOr1 S (fun b => mass w (P b)) :=
  mass_forall_nested hw hsum S P fun b hb c hc => nested_of_down (fun i => -τ i)
    (fun i j h => hup b hb i j (by linarith)) (fun i j h => hup c hc i j (by linarith))

/-! ## Intersections -/

/-- If `E ∪ F` is everything or `E ∩ F` is empty, `mass (E ∩ F) = (mass E + mass F - 1)₊`. -/
lemma mass_inter_of_cover_or_disjoint {w : ι → ℝ} (hw : ∀ i, 0 ≤ w i) (hsum : ∑ i, w i = 1)
    {E F : ι → Prop} (h : (∀ i, E i ∨ F i) ∨ (∀ i, ¬ (E i ∧ F i))) :
    mass w (fun i => E i ∧ F i) = max 0 (mass w E + mass w F - 1) := by
  classical
  rcases h with hc | hd
  · have h1 : mass w (fun i => E i ∧ F i) = mass w E + mass w F - 1 := by
      unfold mass
      rw [← hsum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rcases hc i with he | hf
      · by_cases hf : F i <;> simp [he, hf]
      · by_cases he : E i <;> simp [he, hf]
    have h0 := mass_nonneg hw (fun i => E i ∧ F i)
    rw [h1] at h0 ⊢
    exact (max_eq_right h0).symm
  · have h1 : mass w (fun i => E i ∧ F i) = 0 := by
      rw [mass_congr w (fun i => show E i ∧ F i ↔ False from ⟨fun h => hd i h, False.elim⟩)]
      exact mass_false w
    have h2 : mass w E + mass w F ≤ 1 := by
      unfold mass
      rw [← hsum, ← Finset.sum_add_distrib]
      refine Finset.sum_le_sum fun i _ => ?_
      by_cases he : E i <;> by_cases hf : F i
      · exact absurd ⟨he, hf⟩ (hd i)
      all_goals simp [he, hf, hw i]
    rw [h1, max_eq_left (by linarith)]

/-- **Threshold intersection.** If `E` is down-closed and `F` is up-closed in the same scalar
`τ`, then `mass (E ∩ F) = max 0 (mass E + mass F - 1)`. -/
lemma sum_threshold_inter {w : ι → ℝ} (hw : ∀ i, 0 ≤ w i) (hsum : ∑ i, w i = 1) (τ : ι → ℝ)
    {E F : ι → Prop} (hE : ∀ i j, τ j ≤ τ i → E i → E j)
    (hF : ∀ i j, τ i ≤ τ j → F i → F j) :
    mass w (fun i => E i ∧ F i) = max 0 (mass w E + mass w F - 1) := by
  apply mass_inter_of_cover_or_disjoint hw hsum
  by_cases hc : ∀ i, E i ∨ F i
  · exact Or.inl hc
  · right
    push Not at hc
    obtain ⟨i, hEi, hFi⟩ := hc
    rintro j ⟨hEj, hFj⟩
    rcases le_total (τ i) (τ j) with h | h
    · exact hEi (hE j i h hEj)
    · exact hFi (hF j i h hFj)

end REU
