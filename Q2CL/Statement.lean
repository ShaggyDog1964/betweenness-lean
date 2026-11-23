/-
# Separated rankings: statement of the cubic bounds on `L_4(δ)`

L_4(δ) = Θ(δ^{-3}): in the 3-simplex (K = 4 prizes), the number of lotteries a test must look
at to certify representability of a δ-separated ranking grows like δ^{-3}.

This file contains ONLY definitions and headline `Prop`s. There are no theorems, no proof
holes, and no assumed axioms. It imports `K4.Statement` (audited) and reuses, verbatim
and without restating them, its definitions of:
  * `K4.Lot`, `K4.Simplex` (lotteries and the simplex Δ^{K-1}; here always `K = 4`, so the
    simplex is the 3-simplex Δ³ ⊂ ℝ⁴),
  * `K4.IsBetweennessPref` (the betweenness axioms, BT, used through `K4.Representable`),
  * `K4.Representable` (some BT preference ranks every earlier entry strictly above every
    later entry),
  * `K4.LocallyRepresentable` (every sub-ranking with at most `n` entries is representable).
A ranking of a finite set `X` is, as in `K4.Statement`, a list with no repeated entries,
listed best first; `X` is the set of its entries.

The only new ingredients are the l_∞ separation condition and the separated locality
predicate `SepLocalComplete δ n`.

Relation to the paper's `L_4(δ)` (least `n` such that every `n`-locally representable ranking
of every finite δ-separated `X ⊂ Δ³` is representable):
  * `SepLocalComplete δ n` is exactly the property whose least witness is `L_4(δ)`.
  * It is monotone in `n` (a larger `n` makes the locality hypothesis stronger), although
    that is not needed to read the claims below.
  * "`L_4(δ) ≥ c δ^{-3}`" is the same as "`SepLocalComplete δ n` fails for every natural
    `n < c δ^{-3}`" (that is `lower_stmt`).
  * "`L_4(δ) ≤ N`" is the same as "`SepLocalComplete δ N` holds" (that is `upper_stmt`, with
    `N = ⌈(3/δ + 1)^3⌉`).
Stating both directly in terms of the predicate avoids defining `L_4` as an infimum (whose
value on an empty set would be a junk `0` in Lean).

Source: Theorem 31 of the working paper, part (2) (lower bound, constant `2.03·10^{-4}`, range
`δ ∈ (0, 11/1000]`) and part (1) (packing upper bound). The paper writes `loc_BT(4, δ)` for
`L_4(δ)`.
-/
import Mathlib
import K4.Statement

namespace Q2CL

open K4

/-! ## 1. l_∞ separation -/

/-- `SepGe δ L`: the entries of `L` are pairwise at l_∞ distance at least `δ`. Precisely, for
any two DIFFERENT entries `x ≠ y` of `L` there is a coordinate (prize) `i ∈ {0,1,2,3}` with
`|x i - y i| ≥ δ`; equivalently `max_i |x i - y i| ≥ δ`, i.e. `‖x - y‖_∞ ≥ δ`.
This is the paper's `δ(X) ≥ δ`, where `δ(X)` is the minimum over distinct `x, y ∈ X` of
`‖x - y‖_∞` and `X` is the set of entries. All four coordinates count, including prize `0`
(the paper's `x_0`). A list with fewer than two distinct entries satisfies `SepGe δ L` for
every `δ` (the minimum over an empty set of pairs is `+∞`). -/
def SepGe (δ : ℝ) (L : List (Lot 4)) : Prop :=
  ∀ x ∈ L, ∀ y ∈ L, x ≠ y → ∃ i : Fin 4, δ ≤ |x i - y i|

/-! ## 2. Separated locality -/

/-- `SepLocalComplete δ n`: every `n`-locally representable ranking of every finite
δ-separated subset of Δ³ is representable. Spelled out: for every list `L` of lotteries over
4 prizes (a ranking, best first) such that
  * `L` has no repeated entries (it is a strict ranking of the finite set of its entries),
  * every entry is in the 3-simplex `Simplex 4`,
  * the entries are pairwise at l_∞ distance `≥ δ` (`SepGe δ L`),
  * every sub-ranking of `L` with at most `n` entries is representable in BT,
the whole ranking `L` is representable in BT.
`L_4(δ)` of the paper is the least `n` for which this holds. This is `K4.LocalComplete 4 n`
with the extra hypothesis `SepGe δ L`. -/
def SepLocalComplete (δ : ℝ) (n : ℕ) : Prop :=
  ∀ L : List (Lot 4), L.Nodup → (∀ x ∈ L, x ∈ Simplex 4) → SepGe δ L →
    LocallyRepresentable n L → Representable L

/-! ## 3. Headline statements -/

/-- The explicit lower-bound constant `c = 2.03·10^{-4} = 203/1000000` (Theorem 31(2)). -/
noncomputable def cLower : ℝ := 203 / 1000000

/-- Lower bound, `L_4(δ) ≥ 2.03·10^{-4} · δ^{-3}` for `δ ∈ (0, 11/1000]`: for every real `δ`
with `0 < δ ≤ 11/1000` and every natural number `n` with `n < c / δ^3`, the predicate
`SepLocalComplete δ n` FAILS, i.e. some ranking of distinct δ-separated lotteries in Δ³ is
`n`-locally representable but not representable. (In the paper the witness is the critical
chain-first slice ranking `T_m = T(m, ns_m, ds_m)`, `ds_m = 11/(500m)`,
`ns_m = 1 + ⌊125m/33⌋`, for the `m ≥ 2` with `ds_{m+1} < δ ≤ ds_m`; the witness is not part of
this statement.) -/
def lower_stmt : Prop :=
  ∀ δ : ℝ, 0 < δ → δ ≤ 11 / 1000 →
    ∀ n : ℕ, (n : ℝ) < cLower / δ ^ 3 → ¬ SepLocalComplete δ n

/-- Upper bound (packing), `L_4(δ) ≤ (3/δ + 1)^3` for `δ ∈ (0, 1]`: with
`N = ⌈(3/δ + 1)^3⌉` (the natural-number ceiling `Nat.ceil`), `SepLocalComplete δ N` holds.
(Reason, not checked here: a δ-separated subset of Δ³ has at most `(3/δ + 1)^3` points, and a
ranking that is `N`-locally representable with `N ≥` its length is representable, by taking
the whole list as its own sub-ranking.) -/
def upper_stmt : Prop :=
  ∀ δ : ℝ, 0 < δ → δ ≤ 1 → SepLocalComplete δ ⌈(3 / δ + 1) ^ 3⌉₊

/-- The whole claim: the lower and the upper bound, so
`L_4(δ) = Θ(δ^{-3})` as `δ → 0`. -/
def target_stmt : Prop := lower_stmt ∧ upper_stmt

/-! ## 4. Audit controls (statements only, not part of the target)

These are expected to hold by short arguments; they are here so that an auditor can check that
the definitions mean what the comments say. -/

/-- `SepGe δ L` agrees with the Mathlib l_∞ norm: on `Fin 4 → ℝ` Mathlib's `‖·‖` is the sup
norm, and for distinct entries `δ ≤ ‖x - y‖` iff some coordinate differs by at least `δ`. -/
def sepGe_iff_norm_stmt : Prop :=
  ∀ (δ : ℝ) (L : List (Lot 4)),
    SepGe δ L ↔ ∀ x ∈ L, ∀ y ∈ L, x ≠ y → δ ≤ ‖x - y‖

/-- Monotonicity in `n`: if `SepLocalComplete δ n` holds then so does `SepLocalComplete δ m`
for every `m ≥ n`. So "fails for all `n < c δ^{-3}`" really is "`L_4(δ) ≥ c δ^{-3}`". -/
def mono_stmt : Prop :=
  ∀ (δ : ℝ) (n m : ℕ), n ≤ m → SepLocalComplete δ n → SepLocalComplete δ m

end Q2CL
