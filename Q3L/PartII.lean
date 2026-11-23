/-
`part_ii`: Theorem 36(2), for general `K ≥ 3`.
-/
import Q3L.Statement
import Q3L.PartIIa
import Q3L.PerpIffConst
import Q3L.ThreePoints
import Q3L.LinIndepSwap
import Q3L.GenericDir
import Q3L.HalfReversalRule
import Q3L.NotBinRed

namespace Q3L

open K4 (Lot)

private lemma dot_sub' {K : ℕ} (v p q : Lot K) : dot v (p - q) = dot v p - dot v q := by
  simp only [dot_eq_dotProduct, dotProduct_sub]

/-- Theorem 36(2).
Sketch. Intro `K hK X hXs hdim`; `0 < K`. (a) is `meets_iff_hyperplane`.
(b) Assume `hM : MeetsConeTrivially X`. (a) gives `w` with `hw : StrictMono w` and a constant
`γ` on `affHull X`; `perp_iff_const` (backwards) gives `hperp : ∀ v ∈ dirSpace X,
dot w v = 0`. `exists_three_points hdim` gives `a, b, c ∈ X` with `![a - b, b - c]`
independent; `linIndep_swap` gives `![a - c, c - b]` independent and `a, b, c` distinct.
`exists_generic_dir` with `(a - b, b - c)` gives `v₁` with `v₁·a > v₁·b > v₁·c`
(`dot_eq_dotProduct`, `dotProduct_sub`) injective on `X`; with `(a - c, c - b)` it gives `v₂`
with `v₂·a > v₂·c > v₂·b`, injective on `X`. `exists_halfReversal_rule hw hperp` with `v₁`
gives `ρ`, with `v₂` gives `ρ'`. Take `A := {a, b, c} ⊆ X`, `A.card = 3`
(`Finset.card_insert_of_not_mem`, distinctness), and `x := b`:
`ρ.p b A = 0` (neither extreme for `v₁`: `a` above, `c` below) and `ρ'.p b A = 1/2`
(`b` is the strict `v₂`-minimum, `a` above), so they differ. The `w` of the witness is the
`w` from (a), with its `InIndiffHyperplane`. Finally `not_binaryReduction ρ ρ'` (with the
binary-`½` facts and the menu `A`) gives `¬ BinaryReduction X`. -/
theorem part_ii : part_ii_stmt := by
  classical
  intro K hK X _hXs hdim
  have hK0 : 0 < K := by omega
  refine ⟨meets_iff_hyperplane hK0 X, ?_⟩
  intro hM
  obtain ⟨w, hwH⟩ := (meets_iff_hyperplane hK0 X).1 hM
  have hw : StrictMono w := hwH.1
  have hperp : ∀ v ∈ dirSpace X, dot w v = 0 := (perp_iff_const X w).2 hwH.2
  obtain ⟨a, ha, b, hb, c, hc, hli⟩ := exists_three_points hdim
  obtain ⟨hli2, hab, hbc, hac⟩ := linIndep_swap hli
  obtain ⟨v₁, h1ab, h1bc, hinj1⟩ := exists_generic_dir hli X
  obtain ⟨v₂, h2ac, h2cb, hinj2⟩ := exists_generic_dir hli2 X
  rw [dot_sub'] at h1ab h1bc h2ac h2cb
  obtain ⟨ρ, hρH, hρE, hρB, hρbin, hρmid, _⟩ := exists_halfReversal_rule hw hperp hinj1
  obtain ⟨ρ', hρ'H, hρ'E, hρ'B, hρ'bin, _, hρ'min⟩ := exists_halfReversal_rule hw hperp hinj2
  have hbin : ∀ x ∈ X, ∀ y ∈ X, x ≠ y → ρ.p x {x, y} = 1 / 2 ∧ ρ'.p x {x, y} = 1 / 2 :=
    fun x hx y hy hxy => ⟨hρbin x hx y hy hxy, hρ'bin x hx y hy hxy⟩
  set A : Finset (Lot K) := {a, b, c} with hA
  have hAX : A ⊆ X := by
    intro z hz
    simp only [hA, Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl | rfl <;> assumption
  have hbA : b ∈ A := by simp [hA]
  have hAc : A.card = 3 := by
    rw [hA, Finset.card_insert_of_notMem, Finset.card_pair hbc]
    simp [hab, hac]
  have h0 : ρ.p b A = 0 :=
    hρmid A hAX b hbA ⟨a, by simp [hA], by linarith⟩ ⟨c, by simp [hA], by linarith⟩
  have h12 : ρ'.p b A = 1 / 2 := by
    refine hρ'min A hAX b hbA ⟨a, by simp [hA], by linarith⟩ ?_
    intro y hy hyb
    simp only [hA, Finset.mem_insert, Finset.mem_singleton] at hy
    rcases hy with rfl | rfl | rfl
    · linarith
    · exact absurd rfl hyb
    · linarith
  have hne : ρ.p b A ≠ ρ'.p b A := by rw [h0, h12]; norm_num
  exact ⟨⟨w, hwH, ρ, ρ', hρH, hρ'H, hρE, hρ'E, hρB, hρ'B, hbin, A, hAX, hAc, b, hbA, hne⟩,
    not_binaryReduction ρ ρ' hρB hρ'B hbin ⟨A, hAX, b, hbA, hne⟩⟩

end Q3L
