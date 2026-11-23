import Conv.Statement

/-!
# Ranking basics

R(P) is closed under sub-rankings and under weakening the property; locality is monotone
in the test size.
-/

namespace Conv

universe u

variable {α : Type u} {P Q : Rel α → Prop}

/-- R(P) is closed under sub-rankings: the same preference works. -/
theorem inR_sublist {L L' : List α} (h : InR P L) (hs : L'.Sublist L) : InR P L' := by
  obtain ⟨R, hR, hP, hL⟩ := h
  exact ⟨R, hR, hP, hL.sublist hs⟩

/-- Locality is monotone in the test size: passing larger tests implies passing smaller ones. -/
theorem isLocal_mono {n m : ℕ} (h : IsLocal P n) (hnm : n ≤ m) : IsLocal P m :=
  fun L hL hloc => h L hL fun L' hs hlen => hloc L' hs (hlen.trans hnm)

/-- R(P) grows when the property is weakened. -/
theorem inR_mono {L : List α} (h : ∀ R, P R → Q R) : InR P L → InR Q L := by
  rintro ⟨R, hR, hP, hL⟩
  exact ⟨R, hR, h R hP, hL⟩

end Conv
