/-
`planar_formula`: formula (1) for every mixture of betweenness preferences
(Theorem 36(1), first claim).
-/
import Q3L.Statement
import Q3L.Label
import Q3L.Coords
import Q3L.IsNorthIff
import Q3L.PairProb
import Q3L.NestedMin
import Q3L.NestedMinUp
import Q3L.NestedMeet
import Q3L.MinOr1Congr

namespace Q3L

open K4 (Lot Simplex IsBetweennessPref SPref)

/-- Theorem 36(1), formula (1).
Sketch. Unpack `hρ` into `n, R, w` with `R i` betweenness and strict on `X`, `w ≥ 0`,
`∑ w = 1`, and the mixture formula `hform`. Fix `A ⊆ X`, `x ∈ A` (`x ∈ Simplex`).
Labels: for each `i`, `label_exists hK (R i) hx hd0D hd0 g` gives `η i` (`choose`).
Coordinates: for `y ∈ X`, `exists_coords hdim hd0V hgV hind x hx y hy` gives `α y, β y`
with `x - y = α y • d0 + β y • g` (`choose`, extended by `0` off `X`). So for `y ∈ A`,
`SPref (R i) x y ↔ 0 < α y + β y * η i` (∗), and `IsNorth d0 g x y ↔ 0 < β y`
(`isNorth_iff`). Hence `AS d0 g A x = A.filter (y ≠ x ∧ β y ≤ 0)` and
`AN = A.filter (y ≠ x ∧ 0 < β y)` membership-wise.
Let `P y i := SPref (R i) x y`. By (∗), `P y` is down-closed in `η` for `y ∈ AS` (`β y ≤ 0`:
`η j ≤ η i → β y * η i ≤ β y * η j`) and up-closed for `y ∈ AN` (`β y > 0`).
`IsMaxIn (R i) x A ↔ (∀ y ∈ AS, P y i) ∧ (∀ y ∈ AN, P y i)`, because `A \ {x} = AS ∪ AN`.
So by `hform`, `ρ.p x A = ∑ i, if E i ∧ F i then w i else 0` with `E i := ∀ y ∈ AS, P y i`
(down-closed) and `F i := ∀ y ∈ AN, P y i` (up-closed). `nested_meet` rewrites this as
`max 0 (w(E) + w(F) - 1)`. `nested_min_down` gives `w(E) = minOr1 AS (fun y => ∑ i, if P y i
then w i else 0)`, `nested_min_up` the same for `F` and `AN`. Finally `mixture_pair` (with
`y ∈ X`, `y ≠ x`) and `minOr1_congr` turn `∑ i, if P y i then w i else 0` into
`ρ.p x {x, y}`. -/
theorem planar_formula {K : ℕ} (hK : 0 < K) {X : Finset (Lot K)}
    (hXs : (↑X : Set (Lot K)) ⊆ Simplex K) (hdim : Module.finrank ℝ (dirSpace X) = 2)
    {d0 : Lot K} (hd0V : d0 ∈ dirSpace X) (hd0D : d0 ∈ FOSDCone K) (hd0 : d0 ≠ 0)
    {g : Lot K} (hgV : g ∈ dirSpace X) (hind : LinearIndependent ℝ ![d0, g])
    (ρ : RandomChoiceRule X) (hρ : IsMixture IsBetweennessPref X ρ) :
    PlanarFormula X ρ d0 g := by
  classical
  obtain ⟨n, R, w, hR, hw0, hw1, hform⟩ := hρ
  intro A hA x hxA
  have hxX : x ∈ X := hA hxA
  have hx : x ∈ Simplex K := hXs hxX
  choose η hη using fun i => label_exists hK (hR i).1 hx hd0D hd0 g
  have hc : ∀ y : Lot K, ∃ α β : ℝ, y ∈ X → x - y = α • d0 + β • g := by
    intro y
    by_cases hy : y ∈ X
    · obtain ⟨α, β, h⟩ := exists_coords hdim hd0V hgV hind x hxX y hy
      exact ⟨α, β, fun _ => h⟩
    · exact ⟨0, 0, fun h => absurd h hy⟩
  choose α β hαβ using hc
  -- (∗)
  have hP : ∀ y ∈ A, ∀ i, SPref (R i) x y ↔ 0 < α y + β y * η i := fun y hy i =>
    hη i y (hXs (hA hy)) (α y) (β y) (hαβ y (hA hy))
  have hN : ∀ y ∈ A, IsNorth d0 g x y ↔ 0 < β y := fun y hy =>
    isNorth_iff hind (hαβ y (hA hy))
  have hmemS : ∀ y, y ∈ AS d0 g A x ↔ y ∈ A ∧ y ≠ x ∧ ¬ IsNorth d0 g x y := by
    intro y; unfold AS; simp only [Finset.mem_filter]
  have hmemN : ∀ y, y ∈ AN d0 g A x ↔ y ∈ A ∧ y ≠ x ∧ IsNorth d0 g x y := by
    intro y; unfold AN; simp only [Finset.mem_filter]
  set P : Lot K → Fin n → Prop := fun y i => SPref (R i) x y with hPdef
  have hdown : ∀ c ∈ AS d0 g A x, ∀ i j, η j ≤ η i → P c i → P c j := by
    intro c hc i j hij hci
    obtain ⟨hcA, -, hcN⟩ := (hmemS c).1 hc
    have hb : β c ≤ 0 := not_lt.mp (fun h => hcN ((hN c hcA).2 h))
    have h1 := (hP c hcA i).1 hci
    refine (hP c hcA j).2 ?_
    nlinarith [mul_le_mul_of_nonpos_left hij hb]
  have hup : ∀ c ∈ AN d0 g A x, ∀ i j, η i ≤ η j → P c i → P c j := by
    intro c hc i j hij hci
    obtain ⟨hcA, -, hcN⟩ := (hmemN c).1 hc
    have hb : 0 < β c := (hN c hcA).1 hcN
    have h1 := (hP c hcA i).1 hci
    refine (hP c hcA j).2 ?_
    nlinarith [mul_le_mul_of_nonneg_left hij hb.le]
  have hmax : ∀ i, IsMaxIn (R i) x A ↔
      ((∀ y ∈ AS d0 g A x, P y i) ∧ (∀ y ∈ AN d0 g A x, P y i)) := by
    intro i
    constructor
    · rintro ⟨-, h⟩
      exact ⟨fun y hy => let h' := (hmemS y).1 hy; h y h'.1 h'.2.1,
        fun y hy => let h' := (hmemN y).1 hy; h y h'.1 h'.2.1⟩
    · rintro ⟨hS, hNn⟩
      refine ⟨hxA, fun y hy hyx => ?_⟩
      by_cases hyN : IsNorth d0 g x y
      · exact hNn y ((hmemN y).2 ⟨hy, hyx, hyN⟩)
      · exact hS y ((hmemS y).2 ⟨hy, hyx, hyN⟩)
  rw [hform A hA ⟨x, hxA⟩ x hxA]
  have h1 : (∑ i, if IsMaxIn (R i) x A then w i else 0) =
      ∑ i, if ((∀ y ∈ AS d0 g A x, P y i) ∧ (∀ y ∈ AN d0 g A x, P y i)) then w i else 0 :=
    Finset.sum_congr rfl fun i _ => if_congr (hmax i) rfl rfl
  have hm := nested_meet w hw0 hw1 η (fun i => ∀ y ∈ AS d0 g A x, P y i)
      (fun i => ∀ y ∈ AN d0 g A x, P y i)
      (fun i j hij hE c hc => hdown c hc i j hij (hE c hc))
      (fun i j hij hF c hc => hup c hc i j hij (hF c hc))
  have hd := nested_min_down w hw0 hw1 η (AS d0 g A x) P hdown
  have hu := nested_min_up w hw0 hw1 η (AN d0 g A x) P hup
  rw [h1]
  convert hm using 3
  have hpair : ∀ y ∈ A, y ≠ x →
      ρ.p x {x, y} = ∑ i, if P y i then w i else 0 := fun y hy hyx => by
    rw [mixture_pair hform hxX (hA hy) (Ne.symm hyx)]
  rw [minOr1_congr (S := AS d0 g A x) (f' := fun y => ∑ i, if P y i then w i else 0)
      (fun y hy => hpair y ((hmemS y).1 hy).1 ((hmemS y).1 hy).2.1),
    minOr1_congr (S := AN d0 g A x) (f' := fun y => ∑ i, if P y i then w i else 0)
      (fun y hy => hpair y ((hmemN y).1 hy).1 ((hmemN y).1 hy).2.1)]
  convert (congrArg₂ (· + ·) hd hu).symm using 2 <;>
    exact Finset.sum_congr rfl fun i _ => by congr 1

end Q3L
