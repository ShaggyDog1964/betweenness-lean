import Odds.Defs
import Odds.LogWBStrictMono
import Odds.LogWBMono
import Odds.DotLogWB
import Odds.EkLotBMem
import K4.LiftUSVW
import K4.RepresentableOfChain

namespace Odds

open K4

/-- A (base-free, integer) log chain certifies representability of the corresponding list of
base-`b` family lotteries, for every `b > 1`.
Sketch: copy `K4.representable_of_logChain` (file `K4/RepresentableOfLogChain.lean`):
destructure `h`; `K4.lift_usvw` gives `L1 … L4`; set
`W i = logWB b K (L1 i) (L2 i) (L3 i) (L4 i)`. `StrictMono (W i)` by `logWB_strictMono hb`
(`L1 - L2 = s - u > 0`, `L4 - L3 = v - s > 0`, `omega`). `W i ≤ W (i+1)` by
`logWB_mono hb` (antitone `L1, L2`, monotone `L3, L4`). Separation: `dot_logWB_ekLotB hK hb`
rewritten with `L3 - L1 = u`, `L3 - L2 = s`, `L4 - L2 = v`. Memberships:
`ekLotB_mem_simplex hK (by linarith)`. Conclude with `K4.representable_of_chain`. -/
theorem representable_of_logChainB {K : ℕ} (hK : 4 ≤ K) {b : ℝ} (hb : 1 < b) (m : ℕ)
    (kind : ℕ → EK) (ex : ℕ → ℕ) (u s v w : ℕ → ℤ) (h : LogChain m kind ex u s v w) :
    Representable ((List.range m).map (fun i => ekLotB b K (kind i) (ex i))) := by
  obtain ⟨hu, hs, hv, hw, hbal, hord, hsep⟩ := h
  obtain ⟨L1, L2, L3, L4, hA1, hA2, hM3, hM4, hid⟩ := lift_usvw u s v w hu hs hv hw hbal
  refine representable_of_chain (fun i => logWB b K (L1 i) (L2 i) (L3 i) (L4 i))
    (fun i => ekLotB b K (kind i) (ex i)) m
    (fun i _ => ekLotB_mem_simplex hK (by linarith) (kind i) (ex i)) ?_ ?_ ?_
  · intro i
    obtain ⟨a, b', c⟩ := hid i
    obtain ⟨o1, o2⟩ := hord i
    exact logWB_strictMono hb (by omega) (by omega)
  · intro i
    exact logWB_mono hb (hA1 (Nat.le_succ i)) (hA2 (Nat.le_succ i)) (hM3 (Nat.le_succ i))
      (hM4 (Nat.le_succ i))
  · intro i hi
    obtain ⟨a, b', c⟩ := hid i
    obtain ⟨s1, s2⟩ := hsep i hi
    have d1 := (dot_logWB_ekLotB hK hb (L1 i) (L2 i) (L3 i) (L4 i) (kind i) (ex i)).1
    have d2 := (dot_logWB_ekLotB hK hb (L1 i) (L2 i) (L3 i) (L4 i) (kind (i + 1))
      (ex (i + 1))).2
    rw [a, b', c] at d1 d2
    exact ⟨d1.mpr s1, d2.mpr s2⟩

end Odds
