import K4.Defs
import K4.LiftUSVW
import K4.LogWStrictMono
import K4.LogWMono
import K4.DotLogW
import K4.EkLotMem
import K4.RepresentableOfChain

namespace K4

/-- A log chain certifies representability of a list of family lotteries.
Sketch: destructure `h`; `lift_usvw` gives `L1 … L4`; set
`W i = logW K (L1 i) (L2 i) (L3 i) (L4 i)`. `StrictMono (W i)` by `logW_strictMono`
(`L1 - L2 = s - u > 0`, `L4 - L3 = v - s > 0`). `W i ≤ W (i+1)` by `logW_mono` with
antitone `L1, L2` and monotone `L3, L4`. Separation: `dot_logW_ekLot`, rewriting
`L3 - L1 = u`, `L3 - L2 = s`, `L4 - L2 = v`. Memberships: `ekLot_mem_simplex`. Conclude with
`representable_of_chain`. -/
theorem representable_of_logChain {K : ℕ} (hK : 4 ≤ K) (m : ℕ) (kind : ℕ → EK)
    (ex : ℕ → ℕ) (u s v w : ℕ → ℤ) (h : LogChain m kind ex u s v w) :
    Representable ((List.range m).map (fun i => ekLot K (kind i) (ex i))) := by
  obtain ⟨hu, hs, hv, hw, hbal, hord, hsep⟩ := h
  obtain ⟨L1, L2, L3, L4, hA1, hA2, hM3, hM4, hid⟩ := lift_usvw u s v w hu hs hv hw hbal
  refine representable_of_chain (fun i => logW K (L1 i) (L2 i) (L3 i) (L4 i))
    (fun i => ekLot K (kind i) (ex i)) m
    (fun i _ => ekLot_mem_simplex hK (kind i) (ex i)) ?_ ?_ ?_
  · intro i
    obtain ⟨a, b, c⟩ := hid i
    obtain ⟨o1, o2⟩ := hord i
    exact logW_strictMono (by omega) (by omega)
  · intro i
    exact logW_mono (hA1 (Nat.le_succ i)) (hA2 (Nat.le_succ i)) (hM3 (Nat.le_succ i))
      (hM4 (Nat.le_succ i))
  · intro i hi
    obtain ⟨a, b, c⟩ := hid i
    obtain ⟨s1, s2⟩ := hsep i hi
    have d1 := (dot_logW_ekLot hK (L1 i) (L2 i) (L3 i) (L4 i) (kind i) (ex i)).1
    have d2 := (dot_logW_ekLot hK (L1 i) (L2 i) (L3 i) (L4 i) (kind (i + 1)) (ex (i + 1))).2
    rw [a, b, c] at d1 d2
    exact ⟨d1.mpr s1, d2.mpr s2⟩

end K4
