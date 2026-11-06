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
P0a JMD's actual `w` word and equalities `x4 = w^5`,
`beta = w^6`, now consumable by the proved `JMDStepsTwoToFour` module;
`w` has not been reconstructed from the report alone.
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
fact that JMD reports `H = Y443` is tracked as attributed external data
until the exact proof/witness is ingested.

**F — Finish/test.** First run the finite regression, then golden Agda
typechecking. Both files must pass in the same source tree. Replaying
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

**Current state:** source-written conditional two-generator surjectivity,
plus constructive JMD trace steps 2--4 subgroup-word propagation,
and same-V-natural-action proof, finite arithmetic independently checked.
Agda has not been executed in this environment. The JMD words/Lean
certificate and an actual Monster same-object witness have not been
imported. Do not mark the unified Monster = Aut(V-natural) theorem as
established on this basis.


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
