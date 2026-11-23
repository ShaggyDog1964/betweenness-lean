import Q1.Defs

namespace Q1

private def swapRel (R : Rel) : Rel := fun x y => R x.swap y.swap

private lemma swapRel_weak {R : Rel} (h : IsWeakOrder R) : IsWeakOrder (swapRel R) :=
  ⟨fun x y => h.complete x.swap y.swap,
   fun x y z hxy hyz => h.trans x.swap y.swap z.swap hxy hyz⟩

private lemma hqc_swapRel {R : Rel} (h : VQC R) : HQC (swapRel R) := by
  intro x y z w h1 h2 h3 hy hz
  exact h x.swap y.swap z.swap w.swap h1 h2 h3 hy hz

private lemma vqc_swapRel {R : Rel} (h : HQC R) : VQC (swapRel R) := by
  intro x y z w h1 h2 h3 hy hz
  exact h x.swap y.swap z.swap w.swap h1 h2 h3 hy hz

/-- Swapping coordinates exchanges V-QC and H-QC rankings.
Sketch: (→) from a V-QC `R`, use `R' x y := R x.swap y.swap`. It is a weak order; `HQC R'`
is `VQC R` at the swapped points (`Prod.fst_swap`, `Prod.snd_swap`); and
`List.pairwise_map` turns `L.Pairwise (SPref R)` into `(L.map Prod.swap).Pairwise (SPref R')`
using `Prod.swap_swap`. (←) symmetric: from an H-QC `R` on `L.map swap` use
`R' x y := R x.swap y.swap`, which is V-QC, and `List.pairwise_map`. -/
theorem inR_vqc_iff_swap (L : List Pt) : InR VQC L ↔ InR HQC (L.map Prod.swap) := by
  constructor
  · rintro ⟨R, hw, hv, hp⟩
    refine ⟨swapRel R, swapRel_weak hw, hqc_swapRel hv, ?_⟩
    rw [List.pairwise_map]
    refine hp.imp ?_
    intro a b hab
    simpa [SPref, swapRel] using hab
  · rintro ⟨R, hw, hh, hp⟩
    refine ⟨swapRel R, swapRel_weak hw, vqc_swapRel hh, ?_⟩
    rw [List.pairwise_map] at hp
    refine hp.imp ?_
    intro a b hab
    simpa [SPref, swapRel] using hab

end Q1
