import K4.Defs

namespace K4

private lemma block_eq_map (K J m : ℕ) (hm : m < J) :
    block K J m = (List.range 4).map (fun r => racePt K J (4 * m + r + 1)) := by
  simp only [block, List.range_succ, List.range_zero, List.nil_append,
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
  simp only [racePt, rtKind, rtExp, h0, h1, h2, h3, e0, e1, e2, e3, d0, d1, d2, d3,
    Nat.add_one_ne_zero, ite_false, ite_true, ekLot]
  simp

private lemma blocks_eq_map (K J : ℕ) :
    ∀ m ≤ J, blocksUpTo K J m = (List.range (4 * m)).map (fun i => racePt K J (i + 1)) := by
  intro m
  induction m with
  | zero => intro _; simp [blocksUpTo]
  | succ m ih =>
    intro hm
    rw [blocksUpTo, ih (by omega), block_eq_map K J m (by omega),
      show 4 * (m + 1) = 4 * m + 4 by ring, List.range_add, List.map_append, List.map_map]
    congr 1

theorem racetrack_eq_map (K J : ℕ) :
    racetrackList K J = (List.range (4 * J + 2)).map (racePt K J) := by
  rw [racetrackList, blocks_eq_map K J J le_rfl,
    show 4 * J + 2 = (4 * J + 1) + 1 by ring, List.range_succ, List.range_succ_eq_map,
    List.map_append, List.map_cons, List.map_map]
  have hz : racePt K J 0 = lotR K (parV0 J) := by simp [racePt, rtKind, rtExp, ekLot]
  have hl : racePt K J (4 * J + 1) = lotR K (parV0 J + J * parBeta J) := by
    simp [racePt, rtKind, rtExp, ekLot]
  simp only [List.map_cons, List.map_nil, hl]
  rfl

end K4
