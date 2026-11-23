/-
# Q2CL: shared definitions (no theorems, no proof holes)

The chain-first slice family `T(m, ns, ds)` of Appendix A.20 of the working paper, written out
explicitly. Theorem, lemma and table numbers in the comments of `Q2CL` refer to the working
paper. Notation: `ns`, `ds`, `δ` (as an argument of the face functions), `V` and `ρ_j` here
are `n_s`, `ξ`, `τ`, `Z` and `π_j` there.
Conventions follow `K4.Statement`: prizes `0 < 1 < 2 < 3`, a lottery is `Fin 4 → ℝ`.
-/
import Mathlib
import K4.Statement
import K4.Defs
import Q2CL.Statement

namespace Q2CL

open K4

noncomputable section

/-! ## 1. Normalized face geometry (Appendix A.20, before Lemma 73), as functions of `(u, δ)` -/

/-- `a = t(xb)`. -/
def fa (u : ℝ) : ℝ := 1 / 50 + 7 / 25 * u
/-- `a' = t(xa)`. -/
def fa' (u δ : ℝ) : ℝ := fa u + 7 / 25 * δ
/-- `b = t(ya)`. -/
def fb (u : ℝ) : ℝ := 31 / 50 + 9 / 25 * u
/-- `b' = t(yb)`. -/
def fb' (u δ : ℝ) : ℝ := fb u + 9 / 25 * δ
/-- `ε = 3a'/(4b)`. -/
def feps (u δ : ℝ) : ℝ := 3 / 4 * fa' u δ / fb u
/-- normalized slope of `A`. -/
def fsA (u δ : ℝ) : ℝ := -feps u δ / (fb u - fa' u δ)
/-- normalized slope of `B`. -/
def fsB (u δ : ℝ) : ℝ := (feps u δ - 1) / (fb' u δ - fa u)
/-- normalized height drop `d`. -/
def fd (u δ : ℝ) : ℝ := 13 / 10 + (1 - fb' u δ) / (fb' u δ - fa u) + feps u δ
/-- `α(t)`: `A_j(t) = H_j + g α(t)`. -/
def falpha (u δ t : ℝ) : ℝ := fsA u δ * (t - fb u)
/-- `β(t)`: `B_j(t) = H_j + g β(t)`. -/
def fbeta (u δ t : ℝ) : ℝ := -1 + fsB u δ * (t - fb' u δ)
/-- `α_n(t)`: `A_{j+1}(t) = H_j + g α_n(t)` when gadget `j+1` has slot parameter `un`. -/
def falphaN (u un δ t : ℝ) : ℝ := -fd u δ + fsA un δ * (t - fb un)

/-- The constant `K = 39/88`. -/
def KC : ℝ := 39 / 88

/-! ## 2. Face functions (Table 4) -/

/-- `P = α(0) - β(0)`. -/
def fP (u δ : ℝ) : ℝ := falpha u δ 0 - fbeta u δ 0
/-- `c_1 = (β(0) - β(1)) - (α(0) - α(1))`. -/
def fc1 (u δ : ℝ) : ℝ :=
  (fbeta u δ 0 - fbeta u δ 1) - (falpha u δ 0 - falpha u δ 1)
/-- `c_2 = β(0) α(1) - α(0) β(1)`. -/
def fc2 (u δ : ℝ) : ℝ := fbeta u δ 0 * falpha u δ 1 - falpha u δ 0 * fbeta u δ 1

def fL2a (u δ : ℝ) : ℝ := falpha u δ (fb' u δ) + 1 - 2 * KC * fP u δ
def fL2b (u δ : ℝ) : ℝ := falpha u δ (fa u) + feps u δ - 2 * KC * fP u δ
def fL2c (u δ x : ℝ) : ℝ :=
  feps u δ - fbeta u δ (fa' u δ) - KC * (2 + x * feps u δ) * fP u δ
def fL2d (u δ : ℝ) : ℝ := -fbeta u δ (fb u) - 2 * KC * fP u δ
def fBET (u δ x : ℝ) : ℝ :=
  17 / 20 * fd u δ * (1 + x * falpha u δ 0) * (1 + x * fbeta u δ 1) - (fc1 u δ + x * fc2 u δ)
def fKAP (u δ x : ℝ) : ℝ :=
  (fc1 u δ + x * fc2 u δ) - 1 / 2 * (1 + x * falpha u δ 0) * (1 + x * fbeta u δ 1)
def fDyb (u δ : ℝ) : ℝ := 8 - (falpha u δ (fb' u δ) + 1)
def fDxb (u δ : ℝ) : ℝ := 8 - (falpha u δ (fa u) + feps u δ)

/-- Transition: `P_tr = β(1) - α_n(1)`. -/
def tP (u un δ : ℝ) : ℝ := fbeta u δ 1 - falphaN u un δ 1
def tc1 (u un δ : ℝ) : ℝ :=
  (fbeta u δ 0 - fbeta u δ 1) - (falphaN u un δ 0 - falphaN u un δ 1)
def tc2 (u un δ : ℝ) : ℝ :=
  fbeta u δ 0 * falphaN u un δ 1 - falphaN u un δ 0 * fbeta u δ 1
def tL4 (u un δ x : ℝ) : ℝ :=
  fbeta u δ (fa' un δ) - (feps un δ - fd u δ) - KC * (2 + x * feps un δ) * tP u un δ
def tLR1 (u un δ : ℝ) : ℝ := fbeta u δ (fb un) + fd u δ - 2 * KC * tP u un δ
def tL5a (u un δ x : ℝ) : ℝ :=
  -1 - falphaN u un δ (fb' u δ) - KC * (2 + x * (fd u δ - 1)) * tP u un δ
def tL5b (u un δ x : ℝ) : ℝ :=
  -feps u δ - falphaN u un δ (fa u) - KC * (2 + x * (fd u δ - feps u δ)) * tP u un δ
def tRHO (u un δ x : ℝ) : ℝ := tc1 u un δ + x * tc2 u un δ

/-- Gadget domain: `δ ∈ [0, 1/5]`, `u ∈ [0, 1 - δ]`. -/
def GadDom (u δ : ℝ) : Prop := 0 ≤ δ ∧ δ ≤ 1 / 5 ∧ 0 ≤ u ∧ u ≤ 1 - δ

/-- Transition domain: stay, step or wrap (Lemma 73). -/
def TransDom (u un δ : ℝ) : Prop :=
  0 ≤ δ ∧ δ ≤ 1 / 5 ∧
    ((0 ≤ u ∧ u ≤ 1 - δ ∧ un = u) ∨ (0 ≤ u ∧ u ≤ 1 - 3 * δ ∧ un = u + 2 * δ) ∨
      (u = 1 - δ ∧ un = 0))

/-! ## 3. The construction `T(m, ns, ds)` (Appendix A.20) -/

/-- `g = 2/(5 m² ns)`. -/
def gP (m ns : ℕ) : ℝ := 2 / (5 * (m : ℝ) ^ 2 * ns)
/-- slot step `δ_m = 1/(2m+1)`. -/
def dlt (m : ℕ) : ℝ := 1 / (2 * (m : ℝ) + 1)
/-- class of gadget `j`. -/
def cls (m ns j : ℕ) : ℕ := (j / ns) % (m + 1)
/-- slot parameter `u_j = 2 i δ_m`. -/
def uOf (m ns j : ℕ) : ℝ := 2 * (cls m ns j : ℝ) * dlt m
def epsJ (m ns j : ℕ) : ℝ := feps (uOf m ns j) (dlt m)
def dJ (m ns j : ℕ) : ℝ := fd (uOf m ns j) (dlt m)
def alJ (m ns j : ℕ) (t : ℝ) : ℝ := falpha (uOf m ns j) (dlt m) t
def beJ (m ns j : ℕ) (t : ℝ) : ℝ := fbeta (uOf m ns j) (dlt m) t

/-- Base heights `H_j = 4 - g Σ_{k<j} d_k` (closed form of the recursion). -/
def Hh (m ns j : ℕ) : ℝ := 4 - gP m ns * ∑ k ∈ Finset.range j, dJ m ns k

/-- Number of gadgets: the first `j` with `H_j - g ε_j < 1` (junk `0` if none). -/
def Jn (m ns : ℕ) : ℕ := sInf {j : ℕ | Hh m ns j - gP m ns * epsJ m ns j < 1}

/-- Lines `A_j = (UA, SA)`, `B_j = (UB, SB)`: `L(t) = U(1-t) + S t`. -/
def UA (m ns j : ℕ) : ℝ := Hh m ns j + gP m ns * alJ m ns j 0
def SA (m ns j : ℕ) : ℝ := Hh m ns j + gP m ns * alJ m ns j 1
def UB (m ns j : ℕ) : ℝ := Hh m ns j + gP m ns * beJ m ns j 0
def SB (m ns j : ℕ) : ℝ := Hh m ns j + gP m ns * beJ m ns j 1

/-- `ρ_j = r(B_j)/r(A_j)`. -/
def rho (m ns j : ℕ) : ℝ := (UB m ns j / SB m ns j) / (UA m ns j / SA m ns j)
/-- `o_0 = 3/2`. -/
def o0 : ℝ := 3 / 2
/-- Tight states `w_A(j) = o_0 ∏_{k<j} ρ_k`, `w_B(j) = w_A(j) ρ_j`. -/
def wA (m ns j : ℕ) : ℝ := o0 * ∏ k ∈ Finset.range j, rho m ns k
def wB (m ns j : ℕ) : ℝ := wA m ns j * rho m ns j
def VA (m ns j : ℕ) : ℝ := wA m ns j * SA m ns j
def VB (m ns j : ℕ) : ℝ := wB m ns j * SB m ns j
/-- `o_1 = w_B(J-1) = w_A(J)`. -/
def o1 (m ns : ℕ) : ℝ := wA m ns (Jn m ns)

/-- Slice of gadget `j`: `σ_j = (j mod ns) ds`. -/
def sig (ns : ℕ) (ds : ℝ) (j : ℕ) : ℝ := ((j % ns : ℕ) : ℝ) * ds
/-- `c = σ/(1-σ)`. -/
def cOf (s : ℝ) : ℝ := s / (1 - s)

/-- Lifted height `H' = (L - κ)/(1 + κ)`, `κ = c V`. -/
def hLift (s L V : ℝ) : ℝ := (L - cOf s * V) / (1 + cOf s * V)

/-- Lifted lottery `(1-s) f(t, H') + s e_3`, `f(t,H) = ((1-h)(1-t), (1-h)t, h, 0)`,
`h = H/(1+H)`. -/
def liftPt (s t L V : ℝ) : Lot 4 :=
  ![(1 - s) * (1 - hLift s L V / (1 + hLift s L V)) * (1 - t),
    (1 - s) * (1 - hLift s L V / (1 + hLift s L V)) * t,
    (1 - s) * (hLift s L V / (1 + hLift s L V)), s]

/-- `t` of point `τ ∈ {0,1,2,3} = {xa, ya, yb, xb}` of gadget `j`. -/
def ptT (m ns j τ : ℕ) : ℝ :=
  if τ = 0 then fa' (uOf m ns j) (dlt m) else if τ = 1 then fb (uOf m ns j)
  else if τ = 2 then fb' (uOf m ns j) (dlt m) else fa (uOf m ns j)
/-- virtual height of point `τ` of gadget `j`. -/
def ptL (m ns j τ : ℕ) : ℝ :=
  if τ = 0 then Hh m ns j + gP m ns * epsJ m ns j else if τ = 1 then Hh m ns j
  else if τ = 2 then Hh m ns j - gP m ns else Hh m ns j - gP m ns * epsJ m ns j
/-- `V` of the line point `τ` is lifted from (`A_j` for `τ < 2`, `B_j` otherwise). -/
def ptV (m ns j τ : ℕ) : ℝ := if τ < 2 then VA m ns j else VB m ns j

/-- Lifted point `τ` of gadget `j`. -/
def gpt (m ns : ℕ) (ds : ℝ) (j τ : ℕ) : Lot 4 :=
  liftPt (sig ns ds j) (ptT m ns j τ) (ptL m ns j τ) (ptV m ns j τ)

/-- `R(o) = (0, o/(1+o), 0, 1/(1+o))`. -/
def Rlot (o : ℝ) : Lot 4 := ![0, o / (1 + o), 0, 1 / (1 + o)]

/-- Entry `i` of `T(m, ns, ds)`. -/
def Tpt (m ns : ℕ) (ds : ℝ) (i : ℕ) : Lot 4 :=
  if i = 0 then Rlot o0
  else if i = 4 * Jn m ns + 1 then Rlot (o1 m ns)
  else gpt m ns ds ((i - 1) / 4) ((i - 1) % 4)

/-- The ranking `T(m, ns, ds)`, best first: `R(o_0), xa_0, ya_0, yb_0, xb_0, …, R(o_1)`. -/
def Tlist (m ns : ℕ) (ds : ℝ) : List (Lot 4) :=
  (List.range (4 * Jn m ns + 2)).map (Tpt m ns ds)

/-- Hypotheses of Proposition 71. -/
def Adm (m ns : ℕ) (ds : ℝ) : Prop :=
  2 ≤ m ∧ 30 ≤ m ^ 2 * ns ∧ 0 < ds ∧ ((ns : ℝ) - 1) * ds ≤ 1 / 12

/-- Ratio of an effective line: `r' = (r - φ)/(1 - φ)`. -/
def rEff (r φ : ℝ) : ℝ := (r - φ) / (1 - φ)

/-- Transfer map of gadget `j` (Lemma 78):
`F_j(ω) = ω r'_B / (r'_A + c ω (r'_B - r'_A))`. -/
def transF (m ns : ℕ) (ds : ℝ) (j : ℕ) (ω : ℝ) : ℝ :=
  ω * rEff (UB m ns j / SB m ns j) (cOf (sig ns ds j) * wB m ns j) /
    (rEff (UA m ns j / SA m ns j) (cOf (sig ns ds j) * wA m ns j) +
      cOf (sig ns ds j) * ω *
        (rEff (UB m ns j / SB m ns j) (cOf (sig ns ds j) * wB m ns j) -
          rEff (UA m ns j / SA m ns j) (cOf (sig ns ds j) * wA m ns j)))

/-! ## 4. Chains in state form -/

/-- Normalized vector `(-U, -S, 1, V)`. -/
def tvec (U S V : ℝ) : Lot 4 := ![-U, -S, 1, V]

/-- `tvec U S V · p`. -/
def fval (U S V : ℝ) (p : Lot 4) : ℝ := -U * p 0 - S * p 1 + p 2 + V * p 3

/-- A chain (Definition 32) for the entries `p 0, …, p (n-1)`. -/
def IsChainFn (n : ℕ) (p : ℕ → Lot 4) (W : ℕ → Lot 4) : Prop :=
  (∀ i, i + 1 < n → StrictMono (W i) ∧ 0 < dot (W i) (p i) ∧ dot (W i) (p (i + 1)) < 0) ∧
  (∀ i, i + 2 < n → W i ≤ W (i + 1))

/-! ## 5. Witness parameters for the lower bound -/

/-- `m(δ)`: `2` above `3/400`, `3` on `(9/2000, 3/400]`, `⌊(9/500)/δ⌋` below. -/
def mOf (δ : ℝ) : ℕ :=
  if 3 / 400 < δ then 2 else if 9 / 2000 < δ then 3 else ⌊(9 / 500) / δ⌋₊
/-- `ns(δ) = 1 + ⌊1/(12δ)⌋`. -/
def nsOf (δ : ℝ) : ℕ := 1 + ⌊1 / (12 * δ)⌋₊

end

end Q2CL
