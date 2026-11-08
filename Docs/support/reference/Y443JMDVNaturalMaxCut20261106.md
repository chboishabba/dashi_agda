# Y443 / JMD two-generator trace / existing V-natural: exact max-cut

Date: 2026-11-06. Branch: agent/y443-monster-vnatural-maxcut-20261106.

## Attribution and ownership

- **A. A. Ivanov**, *Y-groups via Transitive Extension*, J. Algebra **218**
  (1999), 412-435, DOI [10.1006/jabr.1999.7882](https://doi.org/10.1006/jabr.1999.7882):
  Y_443 spider/central-word identification and group-theoretic source.
- **J. N. Bray**, [Monster presentations](https://webspace.maths.qmul.ac.uk/j.n.bray/web/Pres/Mnst.html):
  twelve Coxeter generators, 79 relators for M x C2.
- **TauCeti**, [formalized Lean Y443 presentation](https://taucetiproject.org/docs/TauCeti/GroupTheory/SpecificGroups/CFSG/Sporadic/Monster.html):
  separate existing Lean transcription of the diagram, spider and central
  words, with relator and written-length checks.
- **James Michael DuPont (JMD / meta-introspector)**:
  [reported 10-step Y443 two-generator closure](https://x.com/introsp3ctor/status/2118462748845805690);
  user-supplied report runner gives eight *report-level* sanity checks,
  twelve new involutions, a 10-step trace and names
  `closure_pair_eq_top_of_paths`. These are JMD's results, not DASHI's.
  The underlying path words, exact generated group and Lean proof receipts
  were not supplied with the report text. Do not convert the eight checks
  into an invented formal proof.
- **Fedor K. Popov and Leonardo Rastelli**, [Lean_VOA](https://github.com/Fedor-Popov/Lean_VOA)
  and [their 2026 preprint](https://arxiv.org/abs/2611.06616):
  independent Lean formal VOA/Moonshine module construction.
- **DASHI**: the finite transcription and constructive word/action transport
  in the new Agda files below, reusing the existing Agda `VNaturalConstruction`
  and literal `VOAGroupAction`. No original claim to the historical theorem.

## Exact structure: Y443 is not a generic appearance of the number 12

Vertex names:
`a, b1,c1,d1,e1, b2,c2,d2,e2, b3,c3,d3`.

Edges: `a-b1-c1-d1-e1`, `a-b2-c2-d2-e2`,
`a-b3-c3-d3` (common central a).

```text
12 involutions:  x^2 = 1
11 edges:        (xy)^3 = 1
55 nonedges:     (xy)^2 = 1
spider:          (a b1 c1 a b2 c2 a b3 c3)^10 = 1
central:         (a b3 c3 d3 b1 c1 b2)^9 = 1
```

The first 78 Coxeter relations have written length 310; adding the
90-letter spider gives 79 and 400; adding Ivanov's 63-letter central
relator gives 80 and 463. The *historical group identification* is
Y443 / <f312> ~= M, where spider Y443 ~= M x C2. The finite word
transcription **does not** prove finiteness, the Monster order, the
centrality of f312, simplicity or this isomorphism.

## Prior code reused rather than reimplemented

- `DASHI/Moonshine/VNaturalOrbifoldConstruction.agda`:
  the FLM-shaped `Vnatural` obtained from the existing fixed-point
  and twisted summands, under its `OrbifoldVOAAssembly` input.
- `DASHI/Moonshine/VertexOperatorAlgebraCore.agda`:
  literal VOA carrier/group-action owner.
- `DASHI/Moonshine/VertexOperatorAlgebraLinearActionReceiptExact.agda`:
  explicit linearity obligations on that same action.
- `DASHI/Moonshine/MonsterGradedVOALiteralActionSameObjectBidiExact.agda`:
  trace / state-action same-object transport.
- `DASHI/Biology/MoonshineGriessAutomorphismClassificationExact.agda`:
  restriction to the mode-one Griess product.
- `DASHI/Moonshine/TwistedModuleModularity.agda`:
  `GroupWithInverse` donor reused directly.
- `DASHI/Moonshine/Monster3BNormalizerBridge.agda` and PRs
  [#1098](https://github.com/chboishabba/dashi_agda/pull/1098),
  [#1250](https://github.com/chboishabba/dashi_agda/pull/1250):
  the **different** natural Suzuki 12 and 12+78 multiplicity problem.
  Those dimensions alone are not an image of the twelve Y443 involutions.
  The exact `Y443Monster3BTwelveDisjointExact` consumer also proves that
  the standard Heisenberg axis0 translation has order three on every
  six-trit state, and fails the Coxeter order-two relation at zeroState.
- Existing B4 Coxeter/Weyl and Coxeter--Todd lattice implementations are
  distinct carriers; none supplies the Y443 spider quotient automatically.

## Formal proof dependency / ZKP O-R-C-S-L-P-G-F

**O — Objects.** Exact `Y443CoxeterPresentationExact.Node` (12 sites),
`Word`, positive relator lists, `TM.GroupWithInverse G`,
`VN.VNaturalConstruction` and the existing `VOAGroupAction`.

**R — Relations.** The 78 Coxeter, spider and central relators are
enumerated as words. Their evaluation in a selected group is an explicit
`RelatorsSatisfied` obligation, not a source theorem disguised as a
Boolean.

**C — Construction.** `Y443VNaturalPairGenerationExact.TwoWord` is the
freely generated word syntax on `u,v` and inverses. The already-existing
V-natural action is used directly; no new VOA carrier or Monster object.

**S — Same object.** `Y443VNaturalPairWeld` indexes the node generator
map, the word certificate, its universal generation property, the 80
relator witness and the literal VOA action by the *same G*. No agreement
based only on group order or dimension is sufficient.

**L — Lemmas, implemented.**
- `nodeCount`, `pairCount`, `elevenEdges`, `fiftyFiveNonedges`;
- `coxeterRelatorCount`, `coxeterWrittenLength`;
- `spiderLength`, `centralRelatorLength`;
- `doubleMonsterRelatorCount`, `monsterRelatorCount`;
- `doubleMonsterWrittenLength`, `monsterWrittenLength`;
- `identityRepresented`, `productRepresented`, `inverseRepresented`;
- `Y443Monster3BTwelveDisjointExact.axis0TripleTranslationEverywhere`
  and `axis0DoubleTranslationIsNotIdentity`: concrete standard-generator
  source obstruction (order 3 vs Coxeter order 2);
- `Y443JMDTracePowerExact.powerRepresented` (natural-power closure),
  `traceStepThreeX4` and `traceStepFourBeta` (JMD's w^5 and w^6
  subgroup propagation), and `traceStepsThreeAndFour`;
- `nodeRepresented`, `pairWordsSurjective` (constructive word for EVERY
  element when JMD node-word and generation certificates are supplied);
- `pairWordActionMatchesLiteral` (on the actual selected V-natural
  carrier, no parallel action).

**P — Preconditions still requiring actual providers.**
P0 `NodeWordCertificate`: *all twelve* exact `u,v` words, including
the path1 and path3 derivations of JMD's ten-step trace.
P0a **source-written cut now paid**: the original JMD Lean u/v/w paths are imported literally in Agda; the selected relator witness compiles through the 35-step A4 certificate into `x4 = w^5` and `beta = w^6`. Exact-head Agda kernel acceptance remains to be observed.
P1 `NodeGeneration`: the presentation-induced node-generation
theorem for the *same* selected source group.
P2 `RelatorsSatisfied`: evaluate all **80** relations in that group,
including the spider and Ivanov's final central word.
P3 source-derived isomorphism to the selected DASHI Monster carrier
and the required action on `Vnatural` (with correct automorphism laws).
P4 full automorphism/faithfulness and finite character/graded trace
compatibility using the actual selected representation, not merely labels.

**G — Guards.** No postulates, holes, order-inference-by-arithmetic,
or assertion that 12 Suzuki dimensions = 12 Y443 involutions. The
original JMD Lean theorem `y443_closure_pair_eq_top` has been retrieved and explicitly attributed, while native Agda replay of its complete path-generation argument remains a separate proof gate.

**F — Finish/test.** First run the finite regression, then golden Agda
typechecking. The complete current golden Y443 validation root must pass in the same source tree. Replaying
JMD's certificate and the selected Monster/VOA identity are separate
promotion gates.

## Reproducibility and status

```bash
python3 scripts/check_y443_vnatural_pair_bridge.py --finite-only
python3 scripts/check_y443_vnatural_pair_bridge.py
```

The second command fails rather than pretending success if `agda` is
missing. The first command provides an independently executable source
transcription audit, *not* Agda kernel acceptance.

**Current state:** the original JMD Lean theorem and literal source words have been recovered; Agda source contains the complete proposed original-relator-to-beta-five rewrite/semantic chain, power-stage recovery, constructive conditional whole-group generation compiler and same-V-natural-action transport. The independent 35-step Python rewrite test was executed successfully. Agda --safe kernel acceptance has NOT been observed in this environment. Complete all-node path-generator recovery in Agda and the selected Monster = Aut(V-natural) identification remain open; no global endpoint promotion is claimed.


## Candidate 8-by-9 / C3 / analytical J coordinate cross-pollination

Observed relator counts:
- 78 = 8*9+6: Coxeter relations only;
- 79 = 8*9+7: Coxeter plus spider;
- 80 = 8*9+8: Coxeter plus spider and central;
- **canonical presentation decomposition**: 78 = 12 node involutions
  + 11 adjacent pair relations + 55 nonadjacent pair relations.
  Thus 80 = 12 + 11 + 55 + 1 spider + 1 central.

A cardinality equality does not furnish a canonical relator-to-chart
bijection. In particular, 72 is NOT currently an established orbit of
C3, a block of Heisenberg representation data, or a 369 phase fibre.

Existing exact donors for a **candidate** indexed chart:
- `DASHI/Foundations/Base369NestedUnitCompletionMonsterAssemblyExact.agda`:
  `modePhase9IsReduced8PlusIdentity` builds the actual
  `ModePhaseQuotient9` <-> `ReducedNonary8 + identity` carrier iso.
- `DASHI/Moonshine/JInvariantAnalyticJCoarseFineFrickeIntertwinerExact.agda`:
  conditional two-way analytic-vs-finite Fricke transport, using its
  actual `AnalyticJCoarseFineFrickeEquivalence`.
- `DASHI/Moonshine/Monster369ZetaSameObjectWeldExact.agda`:
  native symbolic C3/Monster 3B zeta scalar identification, not yet
  the whole representation-level same-object weld.
- `DASHI/Moonshine/JInvariant369JointJReflectionWeldExact.agda`:
  existing analytic reflection-to-joint-J commuting square.

For a genuine Y443/369 theorem, construct:
```text
R80 = (Rnode12 + Redge11 + Rnonedge55) + Rspider + Rcentral
  -- eR --> (ReducedNonary8 * ModePhaseQuotient9) + Exceptional8
  |                                |
 Coxeter/word rewrite          369 phase/chart operation
  |                                |
  v                                v
R80 ----------------eR------> chart
```
with a **two-sided inverse eR**, transported relation *types*
(order-two/order-three/spider/central), and commutation of the chosen
rewrite/phase operations. Require further same-object maps before
postcomposing with `JInvariantAnalyticJCoarseFineFrickeIntertwinerExact`
or `Monster369ZetaSameObjectWeldExact`.

If a Y443 symmetry acts on the relator index, equivariance must be
checked on ALL 80 indices (or explicitly restricted to the subgroup
that preserves the selected relator family). Mere enumeration order
does not certify such equivariance. Do not mistake the six residual
Coxeter coordinates in 78=72+6 for Suzuki degree 12, the Heisenberg
6+6 axes, or an analytic zeta divisor.

This alternative indexing is a **research target**, not a promoted
Monster/VOA theorem and not a second presentation.


## 2026-11-06 graph-derived 72+8 completion and 9/5, 27/13 comparison

Added exact Agda:
- `Y443ArmSwapOrbitMaxCutExact.agda`: literally swaps the two length-four
  arms, gives all 12 node involution proofs and 144 exhaustive graph adjacency
  equalities, and evaluates the fixed/moving relator counts from the actual
  Y443 node/pair enumeration.
- `Y443Relator72IndexedBidiExact.agda`: a literal tagged 80-relator
  indexing that maps back to the ORIGINAL 80 word list by
  `allTagsRecoverOriginal80Words`, plus exact predicate `core` and
  `residual`, counts 72/8 and Coxeter-only counts 72/6.

Graph automorphism census (independently evaluated):
```
  relation type        fixed       moving      total     C2 orbit classes
  node involutions        4           8          12           8
  adjacent pairs          3           8          11           7
  nonadjacent pairs       7          48          55          31
  Coxeter total          14          64          78          46
  plus spider/central     2           0           2           2
  all relation labels    16          64          80          48
```

There is a **structural**, not numerology-based, relator partition:
```
  Core72 =
     all 55 nonadjacent-pair relations
   + the 8 involutions on the two exchanged long arms
   + the 8 edge relations on the two exchanged long arms
   + the central-node involution
   = 55+8+8+1 = 72.

  CoxeterResidual6 =
     short-arm b3,c3,d3 involutions (3)
   + short-arm a-b3,b3-c3,c3-d3 edge relations (3).

  FullResidual8 =
     CoxeterResidual6 + spider + Ivanov f312 quotient.
```

This partition is invariant under the **two-long-arm swap at the level of
relator roles**, with the spider and Ivanov relator retained as two
distinguished singleton *tags*, not asserted to be fixed as literal words.
It supplies a graph-selected 72+8 cut; it still does NOT canonically supply
eight groups of nine nor a C3 phase transformation on the 72 indices.

The earlier 55 and 11 numerical observations have a sharp
**negative control**. The existing
`BalancedTernaryAntipodal369OrbitHierarchyExact` proves
```text
9 = 1 + 2*4  ->  5 orbit classes,
27 = 1 + 2*13 -> 14 orbit classes.
```
But *under the actual Y443 long-arm swap*,
```text
11 = 3 + 2*4 -> 7 edge orbit classes,
55 = 7 + 2*24 -> 31 nonedge orbit classes.
```
These are **not** 9/5 or 27/13 antipodal quotient objects. The equal
appearance of 4 exchanged edge pairs versus four antipodal pairs in
the 9-carrier does not give a same-action equivalence: the former has
three fixed edge relators, the latter one fixed centre. A different
involution/conjugation action or nontrivial induced quotient must be
explicitly implemented if the analytic J/Fricke/C3 tie is pursued.

The selected 72 is real relator-index mathematics. `8*9` as an
internal **product chart** remains a separate theorem requiring a
typed 72-slot chart, a two-sided inverse, and a C3/Fricke commuting
square. It must not replace the priority of importing JMD's actual
ten-step words and identifying the selected Monster action.


## Sharp nonary-72 equivariance falsifier (new exact Agda theorem)

`Y443Nonary72EquivarianceNoGoExact.agda` uses the ACTUAL
`Registry.ReducedNonary8` (four nonidentity D4 mode labels times
`Five.BinaryOrientation`) and ACTUAL
`Five.ModePhaseQuotient9`, not fake `Fin 8` and `Fin 9`.

- It constructs `swapTag` on Y443 relation labels, with full node/pair
  coverage, explicit canonical pair sorting and `allListedPairsReturnAfterDoubleSwap` on the ORIGINAL 66 unordered pair indices.
- `coreSwapInvariant` proves the 72-subset predicate is preserved for
  all relator tags, by checking all 12x12 node pairs.
- The unique central-node square is a **fixed core relator**:
  `centralCoreFixed`.
- `flipReducedNonary8` flips positive/negative orientation. By
  distinct constructors `reducedEightHasNoFixedPoint` proves this
  action has **no fixed state**.
- `flipChart` on `ReducedNonary8 x ModePhaseQuotient9` flips
  the first factor (and the second mode-phase orientation); therefore
  `chartHasNoFixedPoint` shows its fixed-point set is empty.
- Hence `noNaiveEightByNineEquivariantChart` gives an explicit
  contradiction from any allegedly equivariant map of the
  graph-canonical 72 core to this particular 8x9 chart. Even a
  one-way equivariant map is impossible under THESE involutions.

**This does not veto other C3 actions, nontrivial cocycles, Fricke
transport, action modifications or deliberately symmetry-breaking
coordinate charts.** It precisely tells a future analytic/369 theorem
which direct-natural-action identification is forbidden.

Also reused the exact existing ternary orbit numbers rather than
duplicating their definitions:
```text
Y443 edge count    11 = 1 + 2*(5 quotient classes of 9).
Y443 nonedge count 55 = 1 + 2*(27 raw ternary states).
                    55 = 3 + 4*(13 antipodal pairs of 27).
                    55 = 5 * 11.
```
These are genuine Agda-definitional numeric comparison theorems;
the actual Y443 arm-swap fixed/paired orbit data (3/4 for edges, 7/24
for nonedges) is DIFFERENT and is the decisive equivariance test.


## 2026-11-06 exact primary JMD Lean proof recovered — source-data gate CLOSED

**Correction of stale prior frontier:** JMD's actual word and path proof
are publicly accessible at
[CFSGCorollary/Sporadic/Monster/Y443.lean](https://github.com/AxiomMath/CFSGCorollary/blob/main/CFSGCorollary/Sporadic/Monster/Y443.lean).
The proof is not merely an attributed screenshot/ten-step prose report.
It contains theorem names
`y443_paths`, `y443_closure_pair_eq_top`,
`twoGenerated_y443`, and `twoGenerated_tcg`, with the private
general-purpose `closure_pair_eq_top_of_paths` lemma.

The **actual chosen group elements** are:
```text
u    = x11 * x10 * x9 * x0 * x1 * x2 * x3 * x4
beta = x5 * x6 * x7 * x8
v    = u * x4 * beta
w    = u^-1 * v = x4 * beta
```

DASHI source transcription `Y443JMDSourceWordInstantiationExact.agda`
defines the twelve `x0..x11` names using its preexisting `Y.Node`,
the 8/4/5-node Coxeter paths, exact `uElement`, `betaElement`,
`vElement`, `wElement`, concrete `jmdWTwoWord`, and proves
`wIsX4Beta` from the existing literal `TM.GroupWithInverse` laws.
`Y443JMDConcretePairPowerCompilerExact.agda` wires these to the
already-implemented exact `w^5`, `w^6` power representation closure;
the Lean-derived `sourceX4Fifth`, `sourceBetaSixth` equalities
remain explicit Agda inputs to that compiler, rather than trusted
claims. The two full path-reconstruction theorems, total node-word
construction and Agda proof of whole-group generation are also
separate replay gates.

These are two distinct authorities:
1. **JMD/CFSGCorollary Lean**: has an actual source-written path proof
   of `Y443` and `TCG` being two-generated.
2. **DASHI Agda**: now owns an exact source-word import, a concrete
   group-algebra proof of `w = x4 beta`, and conditional power/action
   transfer. A successful Agda compiler receipt is not observed yet.

The source theorem alone proves TWO-GENERATION of TauCeti's presented
group; identifying that presentation with the full abstract Monster
and then proving the selected `Aut_VOA(Vnatural)` equivalence
are separate structural claims and require their corresponding
source-to-concrete object maps.


## 2026-11-06 algebraic w^5/w^6 discharge, no external numeric axiom

`Y443JMDPowerFiveSixAlgebraExact.agda` now establishes the
general-purpose group identities
```text
rightId
powTwoStep
powFiveOfInvolution
powSixOfInvolution
powSixOfOrderFive
commutesWithPowers
powCommutingProduct
fifthProductIsFirst
sixthProductIsSecond
```
directly from `TM.GroupWithInverse`, `GR.Group.associativity`,
the power recursion in `Y443JMDTracePowerExact`, and explicit
`x^2=e`, `beta^5=e`, `x*beta=beta*x` premises.

`deriveConcretePowers` constructs the previously input-only
`JMDConcretePowers` by using the actual
`JMD.wIsX4Beta` equality, rather than asking for unproved power
equalities. This specializes to JMD's literal source definitions
of `u, v, beta`, and discharges `sourceX4Fifth` and
`sourceBetaSixth` from only the three direct path facts.

**Remaining original Agda-replay boundary**: instantiate the
three path facts inside the selected presentation (x4 involution;
beta fifth power via the length-4 involution Coxeter path;
commutation via four nonadjacent nodes), replay the general
Coxeter-path generator-recovery theorem, and build the
`NodeWordCertificate` / `NodeGeneration` for the exact same group.
The **actual Lean source already proves** these in
`AxiomMath/CFSGCorollary/Sporadic/Monster/Y443.lean`; Agda
cannot simply claim Lean's kernel acceptance without a trusted
cross-prover certificate or native proof.


## Canonical indexing correction

The graph automorphism on unordered pairs must include the
`canonicalPair` sort. The raw substitution
`pair(x,y) -> pair(swap x,swap y)` does not preserve the source
`Y.pairs` **oriented** enumeration for inter-arm pairs, even though it
preserves the abstract unordered-pair relation. The corrected
`Y443Nonary72EquivarianceNoGoExact` now normalizes both endpoints
using the exact 12-node source rank and proves
`allListedPairsReturnAfterDoubleSwap` by complete evaluation of the
66 source indices. The independent Python audit checks closure of
the full 66 index set under this normalized swap and its involution.
This closes a genuine source-index identity bug without changing the
72/8 cardinality census or the central fixed-point no-go.


## Three original JMD path certificates — native finite graph side now source-written

`Y443JMDThreePathGraphCertificateExact.agda` takes JMD's
ORIGINAL exact source paths from `Y443JMDSourceWordInstantiationExact`:
```text
path 1 = [x11, x10, x9, x0, x1, x2, x3, x4]  (8 nodes)
path 2 = [x5, x6, x7, x8]                     (4 nodes)
path 3 = [x0, x5, x6, x7, x8]                 (5 nodes)
```
It proves `jmdFirstPathGraphValid`,
`jmdBetaPathGraphValid`, `jmdThirdPathGraphValid`,
and `x4IsNonadjacentToEntireBetaPath` directly using Y443's
original adjacency matrix: all neighbor edges true, all separated
pairs distinct/nonadjacent, four x4/beta commuting pairs nonadjacent.
The finite checker independently re-evaluates all positions.

**Still distinct:** graph data alone do not establish the group
interpretation of these relations, nor the full path Coxeter element
generator recovery theorem in Agda. The external Lean proof does
establish those statements in its presented group, with source code
now precisely identified.


## Source-only A4 Coxeter path -> actual JMD beta^5 group theorem (new)

**A0: finite source certificate.**
`Y443JMDBetaFiveFiniteRewriteExact.agda` owns a literal
35-move certificate that reduces
`(x5 x6 x7 x8)^5` to the empty word:
15 distant commutations, 10 adjacent braids and 10 involution
cancellations. It proves both `betaFifthAllThirtyFiveMovesValid`
and `betaFifthReducesToEmpty` by native finite evaluation.
The independent Python
`scripts/check_y443_jmd_beta5_rewrite_certificate.py`
replays these *same* 35 operations and checks source adjacency at
every position, producing the empty word.

**A1: generic semantic soundness.**
`Y443JMDBetaFiveSemanticCompilerExact.agda` proves that each
valid local Coxeter rule preserves the interpretation in a
`TM.GroupWithInverse`, derives `runSound` by induction on the
operation list, proves `evalPower`, and compiles the native
finite certificate into `betaOrderFiveFromFiniteCertificate`.
Its `CoxeterA4LocalRules` record is indexed by the selected
original nodes x5,x6,x7,x8; no arbitrary generator map.

**A2: source relator consequences.**
`Y443JMDNonadjacentRelatorConsequencesExact.agda` includes
proof-relevant literal membership of all five relevant squares
and all four x4-to-beta nonedges in the ORIGINAL 80-relator list.
Its group derivation `commuteFromThreeSquares` proves
x4 commutes with each beta generator; `e1CommutesBeta`
composes these commutations over the literal source word.

`Y443CoxeterRelatorSemanticLawsExact.agda` proves that the
original adjacent word relation `(xy)^3=1`, together with
source involutions, implies the braid law `xyx=yxy`.
It uses literal relation membership, source word-power evaluation,
and inverse uniqueness.

**A3: original 80 -> local rules.**
`Y443JMDA4RulesFromPresentationExact.agda` has exact
relator-index witnesses for b2c2, b2d2, b2e2, c2d2,
c2e2, d2e2 and the 4 beta-path node squares.
It constructs the actual `CoxeterA4LocalRules` by exhaustive
4-generator case analysis. Thus
`betaFiveFromOriginal80Relators` requires only the selected
`RelatorsSatisfied` witness; it does NOT postulate beta^5.

**A4: recover the JMD pair witnesses.**
`x4InPairWithNoExtraPowerPremise` and
`betaInPairWithNoExtraPowerPremise` now chain the exact
source relators to beta^5, then the group algebra proves
w^5=x4 and w^6=beta and constructs concrete u/v words.

**Status distinction:** these new modules are source-written and
imported into the focused Agda golden root, but *Agda --safe kernel
acceptance is not observed in this environment*. Hence this is a
complete proposed source-level proof of the JMD **initial
power-recovery stage**, not a certified cross-prover reproduction
of the full JMD theorem. Full path-Coxeter endpoint recovery,
actual all-node u/v witness, `NodeGeneration`, source Monster
isomorphism, and literal `Aut_VOA(Vnatural)` identification
remain separately identified.


## 2026-11-06 terminal JMD full-path max-cut (source written, golden pending)

**The previously named eleven path-shift debt is now discharged at source level.**
The original 80-relator-to-whole-group pipeline is:

```
Y443CoxeterPresentationExact (12 squares + 66 pair relators +2 global)
       │
       ├─ Y443JMDA4RulesFromPresentationExact
       │     original source -> beta^5 by 35 finite A4 rewrites
       │     -> w^5=x4 and w^6=beta -> concrete x4, beta pair words
       │
       ├─ Y443AllCoxeterGraphLawsFrom80Exact
       │     nth/source-index proofs for all 12 squares and 66 pairs
       │     -> involution + nonedge commute + adjacent braid laws
       │        for the literal selected group
       │
       └─ Y443JMDThreePathFiniteRewriteExact
             7 backward P1 shifts *15 moves
             4 forward P3 shifts  * 9 moves
             = 141 checked local source-graph Coxeter rewrites
                   │
             Y443JMDPathShiftSemanticCompilerExact
             -> all eleven group-valued shift identities
                   │
             Y443JMDAllTwelveNodeWordCompilerExact
             -> 12 actual u/v TwoWord syntax trees + proofs
                   │
             Y443PresentedGroupNodeGenerationExact
             (signed-node expression induction +
              selected presentation-word surjectivity)
                   │
             Y443JMDPresentedVNaturalCapstoneExact
             -> RepresentedByPair u v g for EVERY selected g
             -> same selected VOA literal action
                   │
             Y443MonsterGradedLiteralSameObjectCapstoneExact
             -> transport the EXISTING character/VOA action
                along SAME-GROUP / SAME-VNATURAL equality receipts
```

The independent Python checker
`scripts/check_y443_jmd_11_path_shifts.py` checks the 11 source
path shifts and their 141 locally valid Coxeter moves; the existing
`scripts/check_y443_jmd_beta5_rewrite_certificate.py` checks the
35-step `beta^5` trace. The finite checker now requires both,
and checks the source presence of the new modules.

**Golden contract correction:** `scripts/check_y443_vnatural_pair_bridge.py`
now delegates the transitive focused root to the repository's pinned
Agda 2.9 `scripts/run_agda29_parallel_check.sh`, rather than only
checking the elementary presentation/action files with a 2.6-era
direct compiler. The generic GitHub Actions workflow performs only
the independently executable finite tests and does NOT claim to be
the golden Agda checker.

**Exact remaining acceptance cut (not hidden):**
1. **Kernel**: Execute the repository's Agda 2.9
   `run_agda29_parallel_check.sh --safe
   DASHI/Moonshine/Y443VNaturalPairGenerationValidation.agda`
   on the PR exact head, correct any reported elaboration errors,
   and retain a receipt. No kernel receipt is observed here, so
   source-written claims are NOT marked Agda-accepted.
2. **Concrete source group**: Inhabit
   `PresentedByY443Nodes gi nodes` for the selected Y443/Monster
   presentation quotient by proving the actual signed-word evaluator
   is surjective. This is a natural construction fact about a
   presented-group quotient, not the same as already having
   `NodeGeneration` as an axiom. The rest of the node-generation
   and 12-word transport is now proved from it.
3. **Selected object alignment**: Supply the actual
   `MonsterGradedVOALiteralActionWeld`, group identity equality
   and `VNaturalConstruction` equality in
   `SelectedMonsterLiteralY443Source`, rather than name-based
   identification or a second action.
4. **Full automorphism theorem**:
   The existing core record only stores
   `monsterIsFullVOAAutomorphismGroup : Set`; it does not yet
   provide a proof-bearing equivalence of the concrete Monster
   group and the full VOA automorphism set/group with
   faithfulness, action axioms and onto-automorphism recovery.
   The source-written two-generation theorem cannot replace this.

The 80=72+8 alternative chart and no-equivariance result remain
independent of the JMD whole-group proof, which does not assume
a 369 chart, C3 zeta identification, or jCoarse/jFine correspondence.


## 2026-11-07 local Python C3 / F2^5 / 3B / 196883 max-cut

Read back and reused original owner modules:
- `DASHI/Biology/ThreeSixNineMoonshineScaleExact.agda` and `MonsterFilteredCarrierExact.agda`: original ten copies of 3^9 plus 53, 196883, with **non-invariance** of the candidate pieces explicitly retained.
- `DASHI/Foundations/Base369FiveModePhaseQuotientExact.agda`: five D4 **irrep labels**, ten oriented states, nine-cell quotient, not a theorem identifying those types with primitive atoms of an F2^5 algebra.
- `DASHI/Moonshine/Monster3BNormalizerBridge.agda`: C3 class 3B data 65663+65610+65610=196883, trace 53.
- `DASHI/Biology/MoonshineGriessAutomorphismClassificationExact.agda` (PR #437): Griess restriction, **not** reverse VOA extension.
- `DASHI/Moonshine/PenumbralSQModuleLift.agda` and `JInvariantEisensteinBishopConvergenceFrontierExact.agda`: coefficientwise stabilisation and Bishop convergence; neither determines Aut(Vnatural) without additional source laws.

**New independent exact Python model** (local execution receipt retained separately):

For x in first 196830 coordinate states, define T(x) as incrementing the low ternary digit modulo 3; fix the remaining 53. Exhaustive Python computed T^3=1 on all 196883 states and cycle count **65610 3-cycles plus 53 fixed points**. Therefore the complex permutation module has multiplicities (65663,65610,65610) for (1,omega,omega²), trace 53; adding a distinct conformal fixed line gives (65664,65610,65610), trace 54 on 196884. This matches the recorded C3/3B character. By semisimplicity of complex C3 modules, this proves existence of an **abstract C3-equivariant linear equivalence**, provided the selected actual 3B operator has the claimed dimension/order/trace. It does **not** construct a canonical Monster basis, preserve the Griess product or identify the full Monster representation.

Construct five target coordinate blocks, of sizes (65610,65610,65610,52,1), by the low ternary digit on the bulk and splitting the 53 fixed residual coordinates. The map sending each primitive idempotent of the finite Boolean ring `F2^5` to the characteristic function of its block is **unital, injective and multiplicative/additive**, and is C3-equivariant for the first-three-atom cycle `C3 -> S5 = Aut_alg(F2^5)`. Exhaustively checked the full chart and all 32 source elements / 1024 element pairs. This is an actual finite-object C3 bridge, stronger than a numeral-only cardinality comparison.

**Negative gate:** it is impossible to extend the full S5 atom-permutation action to a permutation action on the same 196883 target coordinates while preserving this unital five-block embedding: transitivity would require all blocks equal in size, but 196883 mod 5 = 3. This is a no-go for the selected **Boolean permutation chart**, not for Monster's non-permutation complex linear action.

**Crucial scientific boundary:** `F2^5` is a 32-element Boolean algebra over characteristic two, not a 196884-dimensional complex Griess algebra. Its five primitive idempotents are not the five D4 representation types merely because both labels have count five. C3-equivalent complex representations need not have compatible multiplication or extend to full Monster action.

**Next source-specific completion cuts:**
(1) selected actual 3B action on the same Monster module and a concrete intertwiner;
(2) selected complex Griess product/Aut_Griess identification, reusing PRs #433/#437;
(3) literal weight-two generation for the constructed Vnatural (gives Aut_VOA -> Aut_Griess injectivity by mode-generation induction);
(4) full Griess-to-VOA extension preserving the orbifold relations (gives surjectivity);
(5) source Y443/80 Monster group identification with precisely that same action.

The local Python source and JSON receipts are available in the ChatGPT artifact bundle; this documentation does not falsely claim a repo-executed script or Agda kernel check.


## 2026-11-07 exact zeta commuting square, binary sign loss and Frobenius C2 (local Python)

Reused source owners rather than treating notation as mathematical identity:
- `Monster369ZetaSameObjectWeldExact.agda`: same exact cyclotomic zeta in Fourier, Monster 3B phase, Schrodinger model and literal VOA-phase interface; **actual H_zeta/W_zeta linear recognition still open**.
- `Monster3BPhaseTransportExact.agda`, `Base369Monster3BVOAActionPhaseAdapterBidiExact.agda`: an element inverting the selected 3B generator swaps zeta / zeta², fixes the invariant sector. Zero is the additive zero, **not** a fourth C3 phase.
- `BalancedTernaryC2C3DihedralCodecBridgeExact.agda`: full binary support/sign fibre is a LOSSLESS ternary encoding and intertwines the C2 antipode; support-only forgets sign; C3 cyclic successor is separately intertwined with the qutrit Weyl X action.
- `OggSSPP2F4CurveSheet9FrobeniusBidiExact.agda`, `OggSSPP3F9FrobeniusCandidateNoGoExact.agda`: arithmetic Frobenius/C2 actions are source-specific; not automatic identifications with 3B phase conjugation.
- `Monster3BCyclotomicLinearAlgebraExact.agda`: exact rational-cyclotomic algebra Q[zeta3].

**Executed exact local Python:** constructed 3×3 Q[zeta]/(zeta²+zeta+1) matrices T and R, proving T³=1, R²=1, RTR=T², and the full Fourier commuting square. All 9 projector products P_i P_j = delta_ij P_i; sum P_i=I; 3 eigen-equations T P_k=zeta^k P_k; reflection and scalar conjugation each exchange P_zeta,P_zeta²; their composite fixes each projector. No floating-point approximation.

**Precise binary obstruction:** support(-1)=support(+1)=1, but support(T(-1))=0 and support(T(+1))=1. Therefore there is **no deterministic C3 action on support bits making the support quotient equivariant**; the support+sign pair is lossless and carries the action. This is distinct from the S5 equal-block-size obstruction for the chosen F2^5 chart.

**Frobenius separation:**
- F4/F2 with primitive 3rd root zeta: x->x² is order TWO, sends zeta->zeta² and swaps the two nontrivial C3 phases. This realizes the C2 outer inversion in S3=C3 semidirect C2.
- F9/F3: x->x³ is also order TWO (a+bα)->(a-bα), with exactly 3 fixed and 3 paired orbits; but F9* has order 8 and **contains no primitive cube root**, so this Frobenius is NOT the same scalar-phase zeta map.

**Full chart test:** lifted the low-digit C3 cycle and reversal to every coordinate in the 196883 finite model; exhaustive 196883 checks prove inversion relation R T R=T², with 65610 three-cycles and 53 fixed coordinates. Complex character is (65663,65610,65610), matching the existing 3B character **as a C3 module**, not as an explicit actual Monster representation.

**True representation-theoretic next cut:** instantiate the existing `Monster369ZetaSameObjectWeldExact` frontier by constructing a linear map I:H_zeta -> W_zeta satisfying I rho_H(h)=rho_W(h) I for all selected Heisenberg generators, and verify its evaluation against the SAME 3B-selected literal VOA phase. Then verify mode-one Griess product preservation and weight-two generation before full Aut(Vnatural) identification. Matching zeta scalars and C3 characters do not supply Heisenberg or Griess intertwining.

Local runnable receipt: ChatGPT artifact `y443_zeta_frobenius_square.py`; JSON `y443_zeta_frobenius_square.json`. This doc claims a local run, not a repo-executed gate or Agda proof.


### Stronger result: integral cyclotomic mod-2 Frobenius commuting square

There is a **genuine ring map** rather than just an analogy:

```
Z[1/3,zeta] --cyclotomic conjugation--> Z[1/3,zeta]
     |                                   |
     | mod 2                             | mod 2
     v                                   v
    F4 -------- Frobenius x -> x^2 ----> F4
```

where F4=F2[t]/(t²+t+1), zeta maps to t and zeta² maps to t². Both routes send a+b zeta to its Frobenius conjugate. This is NOT a field map Q(zeta)->F4; the integral localization is essential. The Fourier projectors P_k=(I+zeta^{-k}T+zeta^{-2k}T²)/3 lie in the localized coefficient ring, so all three **reduce mod 2** and remain mutually orthogonal idempotents summing to the identity (all nine products and the full sum independently checked). Frobenius fixes P_1 and exchanges P_zeta,P_zeta². The reflection conjugation J P_zeta J = P_zeta² is independently checked; scalar conjugation and reflection should remain distinct operators.

The key sign lesson: ordinary F2 identifies +1 and -1, but F4 **preserves distinct cube roots** t,t². Support-bit reduction of balanced ternary cannot descend the full C3 action; a full support/sign fibre can. This supplies an exact arithmetic C3-to-Frobenius square and a sharp information-loss theorem. It does not identify an integral form of Vnatural or a Monster-invariant Griess lattice. Python local receipt in `y443_zeta_frobenius_bundle.zip`.


## 2026-11-08 P0 improvement: constructive 729 x 90 Heisenberg recognition (local Python executed)

The existing original owners already give the exact six translation and six modulation operators on X=F3^6 (`Monster3BFiniteHeisenbergGeneratorsExact`), the Fin 90 multiplicity decomposition (`Monster3BMultiplicityEvaluationExact`), and the interface requiring an actual selected 3B generator action (`IbrahimMonster3BLinearZetaSectorRestrictionExact` and `IbrahimMonster3BLinearMultiplicityHomSpaceExact`). This continuation **does not re-create a duplicate** character authority.

**Highest-alpha finite theorem (source-aligned):** let K be a characteristic-zero field containing a primitive cube root zeta and let W be a finite-dimensional K-representation with operators T_a, M_b for a,b in F3^6 satisfying T_a T_c=T_{a+c}, M_b M_d=M_{b+d}, M_b T_a=zeta^{<b,a>} T_a M_b. Define the canonical joint projectors

```
P_x = (1/729) sum_{b in F3^6} zeta^{-<b,x>} M_b .
```

Finite Fourier orthogonality gives P_x P_y=delta_xy P_x, sum_x P_x=1, and T_a P_x=P_{x+a} T_a. If S=P_0 W, then the explicit maps

```
Phi : K[F3^6] tensor S -> W
Phi(e_x tensor s) = T_x s

Psi : W -> K[F3^6] tensor S
Psi(w) = sum_x e_x tensor T_{-x} P_x(w)
```

are mutually inverse, and Phi intertwines all 12 Weyl generators. Thus, for any **inhabited actual** 3B source with these exact linear laws, an intertwiner is constructible from the actual selected matrices and joint weight space, rather than postulating a separate `ActualZetaSectorRecognition`. If dim W=65610, then dim S=90. No assumption of a hidden matching coordinate system is needed for the mathematical statement.

**Local exact computational proof-of-algorithm:** constructed the 65,610-dimensional `K[F3^6] tensor K^90` model and hid its basis with a seeded arbitrary permutation plus independent cubic phase gauge factors. Recovered the 90-dimensional common zero-weight basis from the six modulations; propagated it using six translations to a complete 65,610-vector basis. Verified the two generator intertwining relations for EVERY basis vector and EACH of the 12 operators (787,320 exact checks), the 36 Weyl cross-commutators on all 729 position states (26,244 checks), and selected exact projector orthogonality by character sums. No floats, numerically guessed tolerance, or actual Monster generator matrices. The tool is a finite **model recognition** certificate, not a recovered Monster intertwiner.

**Independent mathematical no-promotion counterexample:** on the same 3D rational C3 regular representation, two distinct associative commutative unital C3-invariant algebras exist:
1. A=Q^3 with coordinatewise multiplication: Aut(A)=S3, of order six.
2. B=Q 1 + U with U=sum-zero plane and U^2=0: Aut(B)=GL2(Q), infinite.
Both have the identical C3 linear action and invariant unit. A contains no nonzero nilpotents but B has a square-zero vector (1,-1,0). A single C3 character, including the exact 3B 53 trace, therefore **cannot** determine the selected Griess multiplication, even up to algebra isomorphism. Local Python verified multiplication and C3 covariance, the square-zero witness, and multiple explicitly distinct radical automorphisms. This is a stronger negative-control gate than mere unmatched dimensions.

**Exact shortest remaining P0 producer:** import the **actual** selected inertia/3B linear operators (not the reconstructed model) and their 12 Weyl relations + central character; use the projector formula above to construct `H_zeta tensor S_zeta <-> W_zeta` on those same operators. The separate Griess multiplication law must then be checked; weight-two VOA generation and VOA automorphism extension are still separate theorem owners. Bishop completion of analytic series does not itself yield any of those algebraic identity statements.

**Execution:** local executable and exact machine report attached as `y443_3b_constructive_recognition.py` and `y443_3b_constructive_recognition_results.json`. This repository DOC is committed; the local executable is not silently claimed repo-executed.


## 2026-11-08 direct FLM/Griess/Tits/Huang max-cut (reuse-first)

**Repository owner audit, not an absence claim:**
- Exact 3B Heisenberg and Weyl operators ARE already source-written in `Monster3BFiniteHeisenbergGeneratorsExact`, `Monster3BFiniteSchrodingerFunctionModuleExact`, `Monster3BFiniteProjectorModelExact`; `Monster3BMultiplicityEvaluationExact` owns 729 x 90 and its finite model evaluation; `Monster3BActualKernelCharacterPromotionExact` owns the class-character and 90-fold isotypy compiler; `MonsterGradedVOAActual3BKernelSameElementBidiExact` ties the selected literal 3B object to the actual kernel-class source IF its class and linear recognition receipts are inhabited. The 65663/65610/65610 trace is already in `Monster3BPhaseTransportExact`. No repeat construction required.
- `MoonshineGriessAutomorphismClassificationExact` already proves the **restriction** of a linear mode-one-preserving VOA automorphism to a Griess product automorphism. It does NOT inhabit a 196884-dimensional concrete Griess multiplication law or the reverse extension theorem for the selected `Vnatural`.
- `VNaturalOrbifoldConstruction` provides the exact Leech fixed/twisted direct-sum schema, but its closure, Jacobi, simplicity and mixed-mode obligations are presently `Set` slots: a field of type `Set` is an abstract proposition **description**, not an inhabitant of that proposition. Likewise `VertexOperatorAlgebraCore.VOAGroupAction` presently stores `actionIdentity : Set` and `actionComposition : Set`, not functions with pointwise equations. This is why source-level group action laws still require a bridge.
- The pre-existing `ConwayNortonTheorem.MonsterVOAAction` has fields `faithful : Set`, `fullAutomorphismGroup : Set`; neither is a proof of full automorphism-group recognition. `MonsterGradedVOABridgeExact` similarly has `monsterIsFullVOAAutomorphismGroup : Set`. No invented "existing proof" is accepted from these fields.

**Verified published route** (classical theorem is already known in mathematics; this PR's task is SAME-object specialization, not re-proving it):
- Griess, *The Friendly Giant*, 1982, DOI 10.1007/BF01389186: concrete 196884-dimensional nonassociative Griess algebra and Monster.
- Tits (1983-1985) full Griess automorphism group; see also Höhn–Seysen 2025, arXiv:2508.01037, for an independent modern full-aut group theorem involving the actual Griess algebra and VOA.
- FLM, *Vertex Operator Algebras and the Monster*, 1988: constructed Vnatural with weight-two Griess algebra.
- Dong–Griess–Lam, *Uniqueness Results for the Moonshine Vertex Operator Algebra*, 2007, DOI 10.1353/ajm.2007.0009: explicitly records weight-two generation of Vnatural and two uniqueness routes requiring additional conditions on other VOAs.
- Yi-Zhi Huang, *A nonmeromorphic extension of the moonshine module vertex operator algebra*, 1994, arXiv:hep-th/9406190, DOI/identifier not invented: constructed an abelian intertwining algebra and an extension of Griess automorphisms to the Moonshine VOA.

**New proof owners attached to the selected original VN orbifold and original JMD source (not to new duplicate objects):**

```
Y443FLMGriessFullAutSelectedVOAExact.agda
  - actual selected V.gradePiece 2 and V.mode(+,1,+) Griess product
  - full linear automorphism (grade preserving, conformal, vacuum, modes)
  - explicit free-mode-expression interpretation (vacuum, V2, sums,
    scalar multiplication, every integer mode, translation)
  - proof: V2 agreement -> agreement on EVERY interpreted expression
  - proof: if every selected state has such an expression,
    V2 restriction is injective on the entire VOA state action
  - proof: restriction preserves Griess product, add, scalar and conformal
  - selected Griess/Tits iso + Huang extension -> both directions
    of full Monster <-> VOA automorphism map pointwise on states

Y443TwoGeneratorSameVOAActionExact.agda
  - from genuine pointwise action identity/product/inverse laws,
    all JMD u/v word actions compare inductively
  - Y443 cover(g) supplies an actual u/v word for EVERY group element g
  - proof: agreement on u and v -> agreement for every G element

Y443FLMDirectSameObjectCapstoneExact.agda
  - selects the EXACT VN.Vnatural from the original JMD source
  - composes the above with the already source-written Y443 pair compiler
  - proof: published Monster action agrees with existing Y443 VOA action
    on ALL g provided only it agrees on original u and v
  - proof: every selected full VOA automorphism is the action of a
    recovered element of the very same source group G
  - proof: inverse recovery of that Monster element
```

The new formal mathematical cut is therefore **source-dependent and short**. To inhabit the selected endcap, the needed actual source witnesses are:
1. Concrete `VNaturalConstruction` with VOA algebraic laws, and actual weight-two source evaluation (not merely record-level slots).
2. Real 196884-dimensional weight-two complex Griess vector carrier, its actual linear structure and mode-one multiplication, plus its identification with the published Griess algebra.
3. FLM weight-two generation witness on THIS selected object; can be transported from the published canonical VOA through a real VOA isomorphism, not from a dimension match.
4. Huang Griess-to-VOA extension and Griess/Tits Monster identification transported along that SAME VOA / weight-two algebra isomorphism.
5. Actual `Y443=Monster` selected group equivalence, honest group-action laws and ONLY TWO concrete source-action comparisons on JMD's u and v. The all-element agreement follows from the existing Y443 pair-word theorem.

**Finite independent exact Python model:** `scripts/check_y443_flm_direct_finite_control.py` checks the FULL 120-automorphism group of the five-atom Q^5 coordinate-algebra control, recovers every element by a 5-cycle and a transposition, then checks 22,320 generated-term action equalities. Locally executed counterpart passed; this control validates the composition pattern, not the actual FLM theorem, and does not establish Griess/Vnatural construction.

**Scope:** this commits proof compilers and a much narrower two-generator semantic frontier, NOT a newly established theorem that the selected abstract VN record is literally the canonical FLM VOA. No Agda kernel run requested or claimed.


## 2026-11-08 BT / trie follow-up: executable Y443 original-word index and genuine semantic boundary

User BT/trie correction is valid as a request to REUSE existing tree/automata infrastructure, but distinguishes two existing repository owners: `BruhatTitsBraidKPReductionReceipt.agda` is the Bruhat–Tits p+1 regular geometry in the YM polymer/KP lane, not a Monster 80-relator normal form. `PNotEqualsNPNaivePrefixTrieAutomatonNoGoExact.agda` is an exact prefix-state counting no-go in the complexity lane; its finite indexing method can be reused, but it does not itself prove a complete/confluent word problem solver.

**New concrete executable:** `scripts/check_y443_relator_trie_same_object_gate.py` indexes the exact original 12 square + 66 pair + spider + central source words. Independent local Python run (longer standalone mirrored version) verified 80 distinct labels, 463 total letters, 394 trie nodes, 80 exact terminal word lookups and failure to accept deliberately extended words. A separate assignment of genuine A4 Coxeter path reflections to the nodes b2,c2,d2,e2 defines an honest local S5 path action, and all TEN local A4 Coxeter relations hold. It nevertheless fails THREE original Y443 relators: edge:a:b2, spider, central. The trivial S5 action satisfies all 80, and a 5-cycle and a transposition generate all 120 S5 elements. The trie file is now included in the original finite checker.

**Meaning:** a source-correct subgroup representation is *not* automatically an action of the full Monster presentation. Therefore the original Monster/VOA action must be checked against the original 80 relation words and/or supplied by an external same-group representation. A prefix trie is only an index, **not** a confluent group rewriting system and never a proof of the external Ivanov classification.

**Highest-alpha external theorem route now independently source-confirmed:**
- Bray/Ivanov original Y443 description: the 79-relator spider group is Monster x C2; the eightieth central quotient yields Monster, as explained in TauCeti's explicit transcription and Ivanov's published Y-group identification. This yields an abstract Monster group isomorphism for the group DEFINED as the 80-relator quotient, not a map to an arbitrary separately selected group carrier without its exact generator images.
- Frenkel–Lepowsky–Meurman build the actual Leech-orbifold VOA. Huang's 1994 hep-th/9406190 specifically says automorphisms of the Griess algebra act on the Moonshine module, and by the work of Griess/Tits its full VOA automorphism group is Monster. The historical mathematical isomorphism **is already established**. If the selected carrier is defined to be the canonical FLM VOA, the published theorem identifies its group without a separate 3B/C3/369 precondition.
- The repo's abstract `VNaturalConstruction` remains a record of chosen orbital inputs and `Set`-typed unspecified mixed products/VOA law slots. An arbitrary such record is not definitionally the published FLM model. To identify that **particular existing object**, require a genuine structure-preserving equivalence, including modes and conformal vector. A numeric grading split 98580+98304 is necessary but insufficient.
- Once the actual selected Y443 action is transported from the known group isomorphism and canonical FLM group action, group-law and u/v action agreements are definitional by construction, and the already proven `Y443TwoGeneratorSameVOAActionExact` extends them to all elements. If retaining an independently selected *preexisting* action rather than transporting one, verify just its original u and v against the transported canonical action, then the all-element equality follows by the same lemma. This avoids re-computing 194 classes or independent per-grade operators.

**Remaining exact critical path** (not an instruction to repeat already-paid finite arithmetic): (1) pick/construct exact original selected Leech-orbifold VOA and prove or transport its identification with the published FLM algebra; (2) instantiate the original Y443 group quotient's map to the published Monster using the source generators and real isomorphism (or define the selected group to be the presented quotient); (3) if preserving the repo's earlier action, evaluate and compare only u and v. The imported theorem route is mathematically complete for the canonical published objects, but not an inhabited Agda proof about arbitrary existing selected record fields. The 80-relator trie does not change that distinction.


### Machine-checkable actual-candidate u/v interface

Added `scripts/check_y443_candidate_action_same_u_v.py`. It accepts JSON files of 12 named source node permutation generators on the SAME finite carrier. For each action it checks the full 80 original Y443 relators, evaluates the exact James Michael DuPont words
`u=d3 c3 b3 a b1 c1 d1 e1`, `v=u e1 b2 c2 d2 e2`,
and, when given `--compare`, reports whether those two actions coincide on u/v. This deliberately returns `proves_Monster_faithfulness=false` (all-trivial representations are possible) and `proves_same_original_Monster_group=false`. The previous Agda `Y443TwoGeneratorSameVOAActionExact` upgrades **genuine two actions of the same selected presented group** from u/v agreement to all-element action equality. For the real 196884-dimensional VOA, actions should be supplied as certified exact LINEAR/mode-preserving operators; the permutation-only JSON tool is a regression/protocol and cannot consume or certify those operators as VOA automorphisms.

Local Python smoke test: a degree-five trivial presentation representation compared to itself passes 80/80 relators and both u/v equalities while explicitly reporting non-faithfulness. This is intentionally a non-promotion test. The new input protocol makes the distinction between checking relators and recognizing Monster executable.


## 2026-11-08 selected FLM / Y443 true same-object max-cut implementation

**Requested task:** close *two* selected-carrier bridges, rather than reimplement 3B, Weyl, 729, 720, 90, the 196883/196884 dimension chart, or existing Griess arithmetic.

**Root-cause source audit:** original `VNaturalOrbifoldConstruction.VNaturalConstruction` has a genuine type-correct VOA object and an orbifold summand interface, but its `OrbifoldVOAAssembly` stores `mixedVertexProductsClosed : Set`, `localityAcrossSummands : Set`, `JacobiAcrossSummands : Set`, `simple : Set`, and other unrefined propositions. No **inhabited canonical FLM model** was discoverable in `dashi_agda` or the searched `dashi_lean4` source. `Y443JMDPresentedVNaturalCapstoneExact.PresentedY443VNaturalSource` still requires an actual `G`, node interpretations, original 80 relators and node-word surjectivity. This source cannot be promoted to an actual FLM/Monster instance merely from recorded names or dimensions.

**New concrete implementation:**

1. `Y443FLMConcreteVOAGroupTransportExact.agda`. An `ExactFLMVOAIsomorphism` identifies the *actual source* and *canonical published* VOA carriers through two inverse maps. Its laws cover scalar base change, each graded piece and its inclusions, vacuum, conformal vector, addition, scalar action, translation and ALL integer-indexed vertex modes. It *derives*, rather than assumes, preservation of the inverse-mode operation. `ExactY443MonsterGroupIso` is a two-sided actual group equivalence respecting identity, multiplication and inversion. `SourceActions.actualSelectedAction` conjugates the canonical Monster action back along these two maps and derives genuine group action identity/product/inverse laws. `PublishedActionVOALaws` permits derivation of vacuum, conformal, mode and translation preservation on the transported selected action, on the very same source object. In `IdenticalVOASelection` and `IdenticalMonsterSelection` the identity iso is **fully inhabited** if (and only if) the two selections are literally the same object; this does not identify an unrelated arbitrary orbifold record with FLM.

2. `Y443FLMConcreteSameObjectActionClosureExact.agda`. `CanonicalFLMReference` explicitly connects the original JMD.selected `Vnatural` to canonical FLM, and the original 80-relator selected group to the published Monster. `OriginalActionAgreement` connects the **preexisting** `JMD.action` to a genuine group action on that exact state carrier; its only action comparison requirements are the TWO concrete JMD elements `u`, `v`. `originalEqualsCanonicalOnEveryElement` proves all-element agreement using the preexisting 12-node JMD word compiler. `gradeTwoOriginalActionIntertwinesCanonical` then proves, on the original selected weight-two grade, an exact equality with the canonical FLM action after transporting its grade-two state inclusion. This is stronger than a shared 196884-dimensional chart, character, C3 phase or Griess scalar identity.

3. Fixed a real existing implementation defect in `Y443FLMGriessFullAutSelectedVOAExact.agda`: a duplicated `mapTerm` with an undeclared `actionOnTerm` family. Also repaired an equality-order mistake in the transported translation-mode proof. All three new/modified modules have been checked for balanced bracket structure; no Agda compiler was used.

4. `scripts/check_y443_flm_conjugate_transport.py`, now wired into the standard `--finite-only` Y443 check: an exact rational, **nonpermutation** upper-triangular base change on a five-atom commutative algebra; the true product is transported by conjugation, rather than matched by dimension. Two generators cover all 120 S5 elements, action and product preservation hold on the transported source object, and a different real group action is detected by its u/v mismatch. Executed local independent implementation: **83,520 exact tests passed** (zero floating tolerances). The toy algebra is explicitly NOT the 196884-dimensional Griess algebra.

**Remaining original (not conditional-compiler) mathematical inputs after this reduction:**

A. An actual source-level implementation/certificate of the canonical FLM Leech-orbifold VOA (modes, mixed intertwining, vacuum, conformal, grading), together with a concrete inverse VOA isomorphism to the selected `VN.Vnatural`, **OR** select the canonical FLM VOA itself as the original source with a literal identity witness. Calling an arbitrary uninhabited `Set` field a proof is prohibited.

B. An actual isomorphism `G(Y443,80) ≅ Monster`, with original node images and the group law, attached to the existing selected `PresentedY443VNaturalSource`, not just external acknowledgement of the published Ivanov/Bray theorem. The **abstract** classical group identification is established in the literature (TauCeti transcription/Ivanov quotient), but its concrete repository instantiation is still a field.

C. For **the preexisting independent** `JMD.action`, genuine pointwise group action laws and equality with the transported canonical action on precisely `u` and `v`. Existing full 80-relator trie and finite candidate verifier can test proposed finite actions but not supply 196884-dimensional complex VOA operators without data. If choosing the canonical transported action as the original selected action from the outset, the u/v compatibility is definitional, but that is a *new selection*, not proof of equality with an unrelated previously selected representation.

**Status:** same-object transport/finite control **implemented and committed**; actual preexisting FLM / Monster witnesses **not inhabited**, hence actual `Aut(Vnatural)=Monster` **not claimed to be kernel-complete** for the selected independent DASHI records. Published external mathematical theorem remains valid. No CI requested or used.
