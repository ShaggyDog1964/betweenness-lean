# betweenness-lean

Lean 4 formalization accompanying Noah Koike Smith, "Axioms That Do Not Combine: Finite Tests
for Betweenness and Its Two Halves" (2026). It contains machine-checked proofs of the results
that rest on the longest arguments of the paper, together with the script that performs the
exact computation used in the proof of the separation bound. The developments on lotteries
define the class of betweenness preferences directly from the axioms of the paper; they do
not assume a utility representation or the linearity of indifference sets.

## Verified results

Numbering refers to the working paper. Each formal statement is a `def ... : Prop` in a
`Statement.lean` file (`REU/Statement.lean`, `K4/Statement.lean`, `Conv/Statement.lean`,
`Q1/Statement.lean`, `Odds/Statement.lean`, `Q2CL/Statement.lean`, `Q3L/Statement.lean`), kept
apart from its proof.

| Result | Formal statement | Proof | File |
|---|---|---|---|
| Theorem 4, parts (1) and (2) | `Conv.char_stmt`, `Conv.locality_stmt` | `Conv.char`, `Conv.locality` | `Conv/Char.lean`, `Conv/Locality.lean` |
| Theorem 4, last sentence of part (3) | `Conv.local_iff_finite_stmt` | `Conv.local_iff_finite` | `Conv/Locality.lean` |
| Proposition 13, except minimality | `Conv.join_stmt`, `Conv.conj_local_stmt` | `Conv.join`, `Conv.conj_local` | `Conv/Join.lean` |
| Proposition 15 | `Q1.target_stmt` | `Q1.target`, `Q1.target_via_conv` | `Q1/Main.lean`, `Q1/ConvMain.lean` |
| Theorem 17 | `REU.thm1_stmt` | `REU.thm1` | `REU/Main.lean` |
| Expected-utility companion of Theorem 17 | `REU.thm1_reu_stmt` | `REU.thm1_reu` | `REU/EU.lean` |
| Finite mixtures suffice | `REU.bridge_stmt` | `REU.bridge` | `REU/Bridge.lean` |
| Theorems 21 and 22 | `K4.target_stmt` | `K4.target` | `K4/Main.lean` |
| Proposition 24 | `Odds.target_stmt` | `Odds.target` | `Odds/Main.lean` |
| Lemma 29 | (in the proof term) | `K4.logCert_exists` | `K4/LogCertExists.lean` |
| Theorem 31, parts (1) and (2) | `Q2CL.target_stmt` | `Q2CL.target` | `Q2CL/Main.lean` |
| Theorem 33, "if" direction | (in the proof term) | `K4.representable_of_chain` | `K4/RepresentableOfChain.lean` |
| Lemma 34 | (in the proof term) | `Q3L.lemma_H` | `Q3L/LemmaH.lean` |
| Theorem 36 | `Q3L.target_stmt` | `Q3L.target` | `Q3L/Main.lean` |

The class of betweenness preferences is `IsBetweennessPref`; the notion of locality in the
paper is `LocalComplete K n`; the racetrack ranking is `racetrackList K J`. In the namespace
`K4`, `target_stmt` is the conjunction of `racetrack_stmt` and `sharp_impossibility_stmt`.

In the namespace `Conv`, a convexity is any family of sets closed under arbitrary
intersections, preferences are complete and transitive relations on the whole type, with no
continuity, and the class of preferences whose upper contour sets are convex is `UCC C`.
`Conv.target_stmt` is the conjunction of the five statements in the first three rows. Part (3)
of Theorem 4 is covered only in its last sentence, and Proposition 13 without its statement
that the hull operator of the intersection is the least of the operators described there. The
development in `Q1` defines the two classes of Proposition 15 directly on the plane and proves
the proposition twice, once directly (`Q1.target`) and once through `Conv.locality` and
`Conv.conj_local` (`Q1.target_via_conv`), by way of `Q1.conv_target_stmt`, which gives the
Carathéodory numbers used in the proof of the proposition.

`Odds.target_stmt` has three parts. Part (A) says that the racetrack built in a real base
`b > 1` in place of `2` is critical, part (B) computes its largest odds, and part (C),
`Odds.boundedOdds_impossibility_stmt`, is Proposition 24.

`Q2CL.target_stmt` is the conjunction of `Q2CL.lower_stmt`, the lower bound
`L_4(δ) ≥ 2.03·10⁻⁴ δ⁻³` for `δ ∈ (0, 11/1000]` of part (2), and `Q2CL.upper_stmt`, the
packing bound `L_4(δ) ≤ (3/δ + 1)³` for `δ ∈ (0, 1]` of part (1). The paper writes
`loc_BT(4, δ)` for `L_4(δ)`. The proof of Theorem 31 in the paper delegates a finite set of
exact inequalities, Lemma 83, to the script in `certificates/` (see below). The Lean proof of
`Q2CL.target` does not use the script. It proves both bounds independently, with the
inequalities of Lemma 83 replaced by proofs in Lean, in some places with cruder constants that
suffice for the stated bounds.

`Q3L.target_stmt` is the conjunction of `part_i_stmt`, `part_ii_stmt` and `part_iii_stmt`,
which are parts (1), (2) and (3) of Theorem 36, for every number of prizes `K ≥ 3`. Part (3)
is stated without the identification of the two representable rankings as the two orders of
the line. `Q3L.lemma_H` proves Lemma 34 for every `K`.

Two further statements are formalized but are not used by the paper. In `REU`, the class
`IsEUPref` consists of betweenness preferences on the triangle that satisfy mixture
independence; its equivalence with the expected-utility class of the paper is not proved in
this repository. In `K4`, the statement `K4.control_K3_stmt`, that betweenness is 4-local with
three prizes (Theorem 18 of the paper), is stated without proof.

## Not formalized

Lemmas 1, 5, 9, 11 and 19, Propositions 6 and 10, Theorems 8, 12 and 18, the first two
sentences of part (3) of Theorem 4, the minimality statement of Proposition 13, Corollary 23,
part (3) of Theorem 31, the "only if" direction of Theorem 33, and Proposition 35. For four
prizes, the proof of `Q2CL.target` does prove the "only if" direction of Theorem 33
(`Q2CL/ChainOfRepresentable.lean`) and the convexity of contour sets from Lemma 1
(`Q2CL/ContourConvex.lean`) as intermediate steps. Lemma 83 is checked by the script in
`certificates/`, not in Lean.

## Building

Install [elan](https://github.com/leanprover/elan), which provides the Lean toolchain named in
`lean-toolchain`. From the repository root:

```
lake exe cache get
lake build
lake env lean REU/Audit.lean
lake env lean K4/Audit.lean
lake build Conv Q1 Odds Q2CL Q3L
lake env lean ConvAudit.lean
lake env lean Odds/Audit.lean
lake env lean Q2CL/Audit.lean
lake env lean Q3L/Audit.lean
```

`lake exe cache get` downloads a prebuilt Mathlib. `lake build` builds the default libraries,
`REU` and `K4`. The libraries `Conv`, `Q1`, `Odds`, `Q2CL` and `Q3L` are not default targets,
so the second build command names them. The audit files check that each headline proof has
exactly the statement type from `Statement.lean`, and print the axioms it depends on. Every
printed line has the form

```
'REU.thm1' depends on axioms: [propext, Classical.choice, Quot.sound]
```

These three axioms are the standard axioms of classical mathematics in Lean. `REU/Audit.lean`
prints this line for `REU.thm1`, `REU.thm1_reu`, `REU.bridge`, `REU.witness_CD_B_not_CDAll`,
`REU.witness_btw_not_EU` and `REU.btw_strictly_larger_than_EU`; `K4/Audit.lean` prints it for
`K4.target`, `K4.logCert_exists` and `K4.representable_of_chain`; `ConvAudit.lean` prints it
for `Conv.target`, `Q1.target_via_conv` and `Q1.target`; `Odds/Audit.lean` prints it for
`Odds.target`; `Q2CL/Audit.lean` prints it for `Q2CL.target`, `Q2CL.lower` and `Q2CL.upper`;
and `Q3L/Audit.lean` prints it for `Q3L.target` and `Q3L.lemma_H`.

The directories `REU` and `K4` are unchanged since commit `1b4e573`, to which the paper refers
for them.

## Certificate

`certificates/certificate.py` verifies Lemma 83 of the paper, which the proof of Theorem 31
uses. It needs only the Python standard library. From the repository root:

```
python3 certificates/certificate.py
```

It uses exact rational arithmetic throughout, and intervals with exact rational endpoints. It
runs in about 30 seconds, and its last line reports the verdict `CERTIFIED` when every check
passes. Its parts A, C and D check parts (1), (2) and (3) of Lemma 83. Part S rechecks the
scalar inequalities that the paper verifies by hand, part E the constants of Theorem 31, and
parts B and F are cross-checks on the ranking `T(2, 8, 11/1000)` that the proof does not use.
The docstring at the top of the script describes each part.

## Layout

`REU/` formalizes the characterization of mixtures of betweenness preferences by Chord
Dominance and Bracketing, on the triangle of lotteries over three prizes.

- `Statement.lean`: definitions and the three headline statements.
- `Sanity.lean`: checks of the definitions on small examples.
- `Geometry.lean`: first-order stochastic dominance and the geometry of the triangle.
- `Utility.lean`: a utility function representing the preference, derived from the axioms.
- `LevelSets.lean`: level sets as straight, non-crossing segments; orientation of chords.
- `MixtureBasics.lean`: the mass of a mixture; threshold and telescoping sums.
- `Necessity.lean`: the necessity direction of Theorem 17.
- `MixtureRule.lean`: the choice rule generated by a mixture.
- `Thresholds.lean`: threshold mixtures shared by both sufficiency proofs.
- `EU.lean`: the expected-utility companion, `REU.thm1_reu`.
- `Chains.lean`: line chains and their nesting.
- `Construct.lean`: the chain preference and its properties.
- `Sufficiency.lean`: the sufficiency direction of Theorem 17.
- `Main.lean`: `REU.thm1`.
- `Bridge.lean`: `REU.bridge`.
- `Witness.lean`: a concrete witness that random betweenness is strictly larger than random
  expected utility.
- `Audit.lean`: the audit described above; not imported by `REU.lean`.

`K4/` formalizes the racetrack rankings for four or more prizes. The files are grouped as
follows.

- Statement and definitions: `Statement.lean`, which does not import `REU`, and `Defs.lean`.
- Log certificates: `LogCertExists.lean` assembles the files `LogCertDelFirst.lean`,
  `LogCertDelLast.lean`, `LogCertDelA.lean`, `LogCertDelAp.lean`, `LogCertDelD.lean` and
  `LogCertDelDp.lean`, one for each kind of deleted position; `LogWMono.lean`,
  `LogWStrictMono.lean`, `DotLogW.lean` and `LiftUSVW.lean` support them.
- Representability: `RepresentableOfLogCert.lean`, `RepresentableOfLogChain.lean`,
  `RepresentableOfChain.lean` and `RepresentableSublist.lean`, with the construction of a
  preference from a chain in `StrictChain.lean`, `PathOfChain.lean` and `PrefOfPath.lean`.
- The racetrack: `RacetrackLength.lean`, `RacetrackEqMap.lean`, `RacetrackMemSimplex.lean`,
  `RacePtVals.lean`, `SprefFacts.lean`, `Menelaus.lean`, `BlockRise.lean`, `Budget.lean` and
  `NotRepresentable.lean`, together with `NodupOfErase.lean` and `SharpOfRacetrack.lean`.
- Assembly: `Main.lean` proves `K4.target`. `Audit.lean` is not imported by `K4.lean`.

The remaining files of `K4/` are lemmas used by the groups above.

`Conv/` formalizes the Carathéodory criterion for convexities on an arbitrary type.
`Statement.lean` holds the definitions and the five statements. `Basic.lean`, `Hull.lean` and
`ChainOrder.lean` develop convexities, hulls and the weak orders built from chains of convex
sets; `Char.lean` proves the characterization by obstructions, `Upper.lean`, `Lower.lean` and
`Locality.lean` the locality criterion, and `Join.lean` the statements on the intersection of
two convexities. `Main.lean` assembles `Conv.target`, and `Sanity.lean` checks the
definitions on small examples. The root file `Conv.lean` imports `Main.lean` and
`Sanity.lean`. The file `ConvAudit.lean`, at the top level, audits both `Conv` and `Q1`.

`Q1/` formalizes the two-attribute example on the plane. `Statement.lean` defines the
horizontally and vertically quasi-concave classes, the statement, and an explicit zigzag
family used in the proof; `Defs.lean` holds shared definitions and `Sanity.lean` checks them.
The files `Chain*.lean`, `HHull*.lean`, `TripleHQC.lean` and `HqcLocal3.lean` prove that the
horizontal class is 3-local, `InRSwap.lean` and `IsLocalSwap.lean` transfer this to the
vertical class, and the files `Zz*.lean`, `Crit*.lean`, `End*.lean`, `Mid*.lean` and
`Orth*.lean` prove that the zigzag rankings are critical for the intersection. `Main.lean`
proves `Q1.target`. `ConvStatement.lean` states the Carathéodory numbers of the two
convexities and of their intersection, `ConvBridge.lean` and `ConvCara*.lean` prove them, and
`ConvMain.lean` derives `Q1.target_via_conv` from `Conv`.

`Odds/` formalizes the racetrack in a real base `b > 1`. `Statement.lean` imports
`K4/Statement.lean` and adds the base-`b` racetrack and the odds of a lottery. The other
files repeat the steps of the proof in `K4/` with `2` replaced by `b`, reusing the lemmas of
`K4/` that do not depend on the base, and `MaxOddsB.lean`, `OddsLeRLot.lean`,
`ExistsBasePow.lean` and `BoundedOddsOfAB.lean` add the computation of the odds and the
choice of the base. `Main.lean` proves `Odds.target`, and `Audit.lean` audits it.

`Q2CL/` formalizes the bounds on the separated locality number. `Statement.lean` imports
`K4/Statement.lean` and adds separation and the two bounds; `Defs.lean` constructs the
rankings `T(m, n_s, ξ)` of the paper, and its header lists the notation that differs from the
paper. The face inequalities are in `Face*.lean`, `Trans*.lean`, `Normalization.lean`,
`ClassTrans.lean`, `GadgetLines.lean`, `RhoBounds.lean`, `WEnvelope.lean`, `WCons.lean`,
`CwBound.lean` and `JSpec.lean`; slice evaluation and the lifted relations in
`SliceEval.lean`, `LiftOn.lean`, `LiftedRel*.lean` and `HomX.lean`; non-representability in
`ChordLemma.lean`, `TransferMap.lean`, `GadgetOmegaStep.lean`, `ChainNormal.lean`,
`LevelHyperplane.lean`, `ContourConvex.lean`, `ChainOfRepresentable.lean` and
`NotRepresentable.lean`; the representable deletions in `Del*.lean`, `Deletions.lean`,
`TightNest.lean`, `ChainOfStates.lean`, `Strictify.lean`, `FarkasStep.lean`,
`ReliftDval.lean` and `RepresentableOfChainFn.lean`; size and separation in `TLength.lean`,
`TMemSimplex.lean`, `TSep.lean`, `Sep*.lean` and `WitnessArith.lean`; and the packing bound in
`Packing.lean`. `Main.lean` proves `Q2CL.lower`, `Q2CL.upper` and `Q2CL.target`, and
`Audit.lean` audits them.

`Q3L/` formalizes the planar dichotomy for every number of prizes `K ≥ 3`. `Statement.lean`
restates for `K` prizes the random choice rules and mixtures of `REU/Statement.lean`, and
defines the cone of dominance directions and binary reduction. `LemmaH.lean` proves Lemma 34
from `HConvex.lean`, `HRelOpen.lean`, `HSeparate.lean`, `HClosure.lean`, `HTrichotomy.lean` and
`HStrictMono.lean`. `PartI.lean`, `PartII.lean` and `PartIII.lean` prove the three parts of
Theorem 36 from the remaining files, among them `DotPosCone.lean` and `PerpStrictMono.lean`
for Lemmas 84 and 85, `Compare.lean` for Lemma 87, and `NestedMin.lean`, `NestedMinUp.lean` and
`NestedMeet.lean` for Lemma 44. `Main.lean` proves `Q3L.target`, and `Audit.lean` audits it.

## Versions

Lean 4.35.0, Mathlib v4.35.0.

## Use of AI

The proofs were first written by hand and are given in full in the paper. Claude (Anthropic)
was used to translate them into Lean. The Lean kernel checks every step, so the correctness of
the formal proofs does not depend on the translation; that the formal statements match those
of the paper is the author's responsibility.

## Citation

```bibtex
@unpublished{smith2026axioms,
  author = {Smith, Noah Koike},
  title  = {Axioms That Do Not Combine: Finite Tests for Betweenness and Its Two Halves},
  year   = {2026},
  note   = {Lean 4 formalization: https://github.com/ShaggyDog1964/betweenness-lean}
}
```

## License

Apache 2.0. See `LICENSE`.
