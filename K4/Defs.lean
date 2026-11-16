/-
# Shared definitions for the racetrack construction (no theorems, no proof holes)

Everything here is a plain definition used by the lemma files `K4/*.lean`.
Conventions follow `K4/Statement.lean`: prizes `0 < 1 < … < K-1`, worst first.
-/
import K4.Statement

namespace K4

/-- Edge lottery with real odds ratio `x = p i / p j`: mass `x/(x+1)` on prize `i`,
`1/(x+1)` on prize `j`. `edgeLot K i j c` is `rLot K i j (2^c)` definitionally. -/
noncomputable def rLot (K i j : ℕ) (x : ℝ) : Lot K := fun k =>
  if k.val = i then x / (x + 1)
  else if k.val = j then 1 / (x + 1)
  else 0

/-- The degenerate lottery (vertex) on prize `i`. -/
noncomputable def vtx (K i : ℕ) : Lot K := fun k => if k.val = i then 1 else 0

/-- Euclidean pairing `∑ w k * p k`. -/
noncomputable def dot {K : ℕ} (w p : Lot K) : ℝ := ∑ k, w k * p k

/-- The three edge-lottery kinds of the family. -/
inductive EK where
  | P
  | Q
  | R

/-- `ekLot K e c` is `lotP K c`, `lotQ K c` or `lotR K c`. -/
noncomputable def ekLot (K : ℕ) : EK → ℕ → Lot K
  | EK.P, c => lotP K c
  | EK.Q, c => lotQ K c
  | EK.R, c => lotR K c

/-- Selects the log-tilt coordinate that decides the side of a lottery of the given kind:
`P ↦ u`, `Q ↦ s`, `R ↦ v`. -/
def ekSel : EK → ℤ → ℤ → ℤ → ℤ
  | EK.P, u, _, _ => u
  | EK.Q, _, s, _ => s
  | EK.R, _, _, v => v

/-- Kind of the `i`-th entry (0-based) of `racetrackList K J`. -/
def rtKind (J i : ℕ) : EK :=
  if i = 0 then EK.R
  else if i = 4 * J + 1 then EK.R
  else if (i - 1) % 4 = 0 then EK.P
  else if (i - 1) % 4 = 3 then EK.P
  else EK.Q

/-- Exponent of the `i`-th entry (0-based) of `racetrackList K J`. -/
def rtExp (J i : ℕ) : ℕ :=
  if i = 0 then parV0 J
  else if i = 4 * J + 1 then parV0 J + J * parBeta J
  else if (i - 1) % 4 = 0 then expA J ((i - 1) / 4)
  else if (i - 1) % 4 = 1 then expD J ((i - 1) / 4)
  else if (i - 1) % 4 = 2 then expD J ((i - 1) / 4) + parG J
  else expA J ((i - 1) / 4) + parG_small J

/-- The `i`-th entry of `racetrackList K J` as an explicit function of `i`. -/
noncomputable def racePt (K J i : ℕ) : Lot K := ekLot K (rtKind J i) (rtExp J i)

/-- Index map of a one-point deletion: position `i` of `L.eraseIdx k` is position
`skipIdx k i` of `L`. -/
def skipIdx (k i : ℕ) : ℕ := if i < k then i else i + 1

/-- Log-coordinate tilt vector `(-2^L1, -2^L2, 2^L3, 2^L4, 2^L4 + 1, 2^L4 + 2, …)`. -/
noncomputable def logW (K : ℕ) (L1 L2 L3 L4 : ℤ) : Lot K := fun k =>
  if k.val = 0 then -((2 : ℝ) ^ L1)
  else if k.val = 1 then -((2 : ℝ) ^ L2)
  else if k.val = 2 then (2 : ℝ) ^ L3
  else (2 : ℝ) ^ L4 + ((k.val : ℝ) - 3)

/-- A log-coordinate separating chain for the list `i ↦ ekLot K (kind i) (ex i)`,
`i < m`: integer sequences `u, s, v, w` (the log tilts `u = L3-L1`, `s = L3-L2`,
`v = L4-L2`, `w = L4-L1`), all nondecreasing, balanced, with `u < s < v`, and the
`i`-th tilt puts entry `i` strictly above and entry `i+1` strictly below. -/
def LogChain (m : ℕ) (kind : ℕ → EK) (ex : ℕ → ℕ) (u s v w : ℕ → ℤ) : Prop :=
  Monotone u ∧ Monotone s ∧ Monotone v ∧ Monotone w ∧
  (∀ i, u i + v i = s i + w i) ∧ (∀ i, u i < s i ∧ s i < v i) ∧
  ∀ i, i + 1 < m →
    ((ex i : ℤ) < ekSel (kind i) (u i) (s i) (v i)) ∧
    (ekSel (kind (i + 1)) (u i) (s i) (v i) < (ex (i + 1) : ℤ))

/-- A log chain for `(racetrackList K J).eraseIdx k`. -/
def LogCert (J k : ℕ) (u s v w : ℕ → ℤ) : Prop :=
  LogChain (4 * J + 1) (fun i => rtKind J (skipIdx k i)) (fun i => rtExp J (skipIdx k i))
    u s v w

end K4
