import Odds.Defs

namespace Odds

open K4

private lemma blockB_eq_map (b : ℝ) (K J m : ℕ) (hm : m < J) :
    blockB b K J m = (List.range 4).map (fun r => racePtB b K J (4 * m + r + 1)) := by
  simp only [blockB, List.range_succ, List.range_zero, List.nil_append,
    List.map_cons, List.map_nil, List.cons_append]
  have h0 : 4 * m + 0 + 1 ≠ 4 * J + 1 := by omega
  have h1 : 4 * m + 1 + 1 ≠ 4 * J + 1 := by omega
  have h2 : 4 * m + 2 + 1 ≠ 4 * J + 1 := by omega
  have h3 : 4 * m + 3 + 1 ≠ 4 * J + 1 := by omega
  have e0 : (4 * m + 0 + 1 - 1) % 4 = 0 := by omega
  have e1 : (4 * m + 1 + 1 - 1) % 4 = 1 := by omega
  have e2 : (4 * m + 2 + 1 - 1) % 4 = 2 := by omega
  have e3 : (4 * m + 3 + 1 - 1) % 4 = 3 := by omega
  have d0 : (4 * m + 0 + 1 - 1) / 4 = m := by omega
  have d1 : (4 * m + 1 + 1 - 1) / 4 = m := by omega
  have d2 : (4 * m + 2 + 1 - 1) / 4 = m := by omega
  have d3 : (4 * m + 3 + 1 - 1) / 4 = m := by omega
  simp only [racePtB, rtKind, rtExp, h0, h1, h2, h3, e0, e1, e2, e3, d0, d1, d2, d3,
    Nat.add_one_ne_zero, ite_false, ite_true, ekLotB]
  simp

private lemma blocksUpToB_eq_map (b : ℝ) (K J : ℕ) :
    ∀ m ≤ J, blocksUpToB b K J m =
      (List.range (4 * m)).map (fun i => racePtB b K J (i + 1)) := by
  intro m
  induction m with
  | zero => intro _; simp [blocksUpToB]
  | succ m ih =>
    intro hm
    rw [blocksUpToB, ih (by omega), blockB_eq_map b K J m (by omega),
      show 4 * (m + 1) = 4 * m + 4 by ring, List.range_add, List.map_append, List.map_map]
    congr 1

/-- The base-`b` racetrack as a mapped range (base-`b` copy of `K4.racetrack_eq_map`). -/
theorem racetrackB_eq_map (b : ℝ) (K J : ℕ) :
    racetrackListB b K J = (List.range (4 * J + 2)).map (racePtB b K J) := by
  rw [racetrackListB, blocksUpToB_eq_map b K J J le_rfl,
    show 4 * J + 2 = (4 * J + 1) + 1 by ring, List.range_succ, List.range_succ_eq_map,
    List.map_append, List.map_cons, List.map_map]
  have hl : racePtB b K J (4 * J + 1) = lotRB b K (parV0 J + J * parBeta J) := by
    simp [racePtB, rtKind, rtExp, ekLotB]
  simp only [List.map_cons, List.map_nil, hl]
  rfl

end Odds
