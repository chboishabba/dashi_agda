# Original Wilson D1 — polymer-animal reuse audit and corrected max-cut
Date: 2026-11-09. Scope: PR #1444 and existing merged YM corpus. No external repository writes.

## Finding: do not reimplement polymer-animal enumeration

The repository already contains the following substantive sources, beyond receipts:

| Original owner | Reusable theorem / construction | Exact application boundary |
|---|---|---|
| `BalabanPolymerDiameterEntropy.agda` | P06 mixed skeleton–decoration animal-count reducer, with rooted skeleton DFS enumeration | The module declares `BalabanPolymerContext`, `BalabanPolymer`, and `currentBalabanGraphAdapter` as postulates; a physical instantiation must not treat these as concrete original Wilson SU(2) data |
| `BalabanP06CanonicalAnimalConstantExact.agda` | `canonicalAnimalCountBound`, canonical skeleton/decoration constants | Requires a supplied `P06ModelLeafDischargePackage`; no second animal-count theorem is necessary once original physical support satisfies its hypotheses |
| `BalabanP06PhysicalModelLeafLightweightExact.agda` | explicit local graph/support, reduced skeleton and decoration/fibre contracts | Contains model-dependent rooted support/connectivity/multiplicity obligations |
| `BalabanClayT2RepositoryConnectedPolymerExtractionExact.agda` | least-root tree, fixed DFS trace, decoder and root-word injectivity | Physical connected-block carrier and canonical decoder input still needed |
| `BalabanCMP116R429ConnectedDomainCountingRound440Exact.agda` | reuse of canonical rooted-trace counting for literal R429 CMP116 domain | `trace`, `literalDomainIsRootedShell`, `literalDomainPolymerFaithful`, `canonicalTraceDepthIsR429TreeDepth` must be supplied for original domain |
| `BalabanClayP2BadComponentGeometryExact.agda` | bad-block finite path/component connectivity and gauge transport | Literal original Wilson bad predicate and physical measure activity are distinct |
| `BalabanClayGate4OscillationAnimalInfluenceExact.agda` | finite shell activity <= animal/oscillation majorant summation | `shellBelowMajorant`, scale-uniform decay and strict weighted ratio need original source estimates |
| `BalabanP06A1A2A3InfluenceExact.agda` | canonical P06 animal constant + per-link oscillation source assembly | `PhysicalA1A2A3InfluenceInputs` has conditional `p06ModelLeaf`, `shellsAt`, and strict ratio |
| `BalabanStepVCanonicalAnimalMarginExact.agda` | logarithmic animal entropy–decay margin transport | Needs original physical kappa/log-exp profile |
| `BalabanLiteralTwoWilsonCMP116ConnectingTailExact.agda` | finite mixed log differentiation, connecting clusters, triangle and rooted-shell transport | `TwoWilsonCMP116PhysicalShellPayment.chargeSumBelowPhysicalRootedShell` is still a supplied field |

`YMLatticeAnimalCountingBoundReceipt.agda` is explicitly a non-promoting receipt: the quoted rooted-Z4 (8e)^n statement is NOT a kernel proof of the concrete Wilson polymer hypothesis.

## Single high-alpha producer path

1. Select the *same* original changing-cutoff Wilson R445 Gibbs/polymer measure, original bad-region event and physical-block supports.
2. Prove these original supports inhabit the existing P06 physical model leaf and R429 canonical trace identification; reuse `canonicalAnimalCountBound`, not a fresh animal lemma.
3. Prove an original Wilson large-field/frustrated-polymer *activity* bound, with a quantitative decay exponent exceeding the canonical animal entropy: `C_anim exp(-kappa) < 1`, uniformly in physical cutoff and volume.
4. Transport that estimate through existing A1/A2/A3 / Step-V / KP/FP and the literal two-Wilson marked expansion to **the exact** finite charge-sum inequality `chargeSumBelowPhysicalRootedShell` for the existing physical-shell package. This must retain source identity, 2 support insertions, actual scale/root/distance, and signed/covariance equality.
5. Consume the already implemented `twoWilsonMixedLogBelowPhysicalRootedShell`, R320 and R333 consumers. No duplicate KP or animal counting.
6. E1 continuum convergence, D2 same-E1 OS spectrum, N1 continuum noncollapse, G1 compact-simple scope remain independent physical terminal gates.

## Physical counterexample to invalid promotion

Rooted-animal count alone controls how many connected supports exist; it gives no upper bound on their Gibbs probability or their polymer activity. A one-link coherent conditional cap also fails to control a sparse connected support of frustrated staples. Combining either with a finite polymer enumeration without actual joint activity domination is logically insufficient.

## Narrow new proof contract (not an already proved lemma)

`originalWilsonSparseFrustratedActivityBelowCanonicalP06Rate`:
For each original physical cutoff, volume, pair of Wilson test supports, and genuinely connecting selected polymer/cluster, bound the absolute marked mixed charge by the original physical activity decaying with canonical trace depth at a uniform rate whose exponential decay wins the P06/Step-V animal constant; establish the root-and-distance indexed *sum* rather than only a pointwise estimate.

This is the missing physical quantitative input. Do NOT replace it with `postulate`, an empty admissibility relation, a generic shell majorant field, or a high-temperature independent-plaquette model.

## Acceptance

This audit reads original GitHub source on PR #1444, not merely PR descriptions. It claims neither Agda kernel acceptance nor an all-Clay result. Existing source already pays counting and finite mixed-derivative transport conditional on model identification. The genuine remaining work is original Wilson physical activity and its source identification, then E1/D2/N1/G1.


## Additional source-owner check: P06 physical constructor and P11

`BalabanP06PhysicalModelLeafExact.agda` already defines `p06ModelLeafFromPhysicalInputs` and `p06PhysicalModelLeafReceipt`. Its record `P06PhysicalModelLeafInputs` supplies the support/reduced-skeleton/decoration/decomposition, concrete neighbour graph and finite-range summation components. Several interfaces carry propositions as `Set` plus evidence fields. This is a *constructor requiring proofs*, not an automatic derivation of original Wilson geometry.

`BalabanP11PhysicalPrefixTailEntropyExact.agda` already consumes the same canonical P06 animal constant in `canonicalAnimalConstantForP11`, and `p11AbsorptionFromPhysicalPrefixTail` transports P11 analytic input to the imported large-field absorption condition. The module explicitly classifies its finite prefix bound, asymptotic tail estimate and entropy payment as conditional. Therefore **P11 entropy absorption also must not be reconstructed from scratch**.

`BalabanStepVGeometricInfluenceSummationExact.agda` already implements `uniformInfluenceBoundFromGeometricSummation` from the A1/A2/A3 input and a majorant partial-sum bound. There is no missing finite-sum comparison theorem in this route.

**Further narrowed maximum cut:** (1) select original Wilson literal physical support into P06/R429 and prove the actual instance of its geometric/model fields; (2) original full Gibbs sparse-frustrated activity/scale bound with a uniform entropy margin and two-mark charge; (3) same-source physical-shell sum calibration. Only then consume the already-existing KP/FP, P11, Step V, CMP116, R320, R333 compilers.

This narrows obligations; it does not prove the missing original-Wilson analytic inputs.


## 2026-11-09 original-link P06 concrete graph implementation

New source module `YMClayD1OriginalLinkStarFiniteNeighbourGraphExact.agda`, imported by `YMClayOriginalWilsonPhysicalRegression.agda`.

It constructs the original 4D positive-link graph on the source carrier `Torus.PositiveBond (suc n)` instead of substituting the eight-neighbour **block** graph. Its `OriginalLinkStarConflict a b` means that the actual incident original plaquette stars are not disjoint. It supplies `originalAllPositiveLinksComplete`, constructive `originalLinkStarConflictDec`, `originalConflictingFilterSound`, `originalConflictingFilterComplete`, `originalNeighbourConflictSound`, `originalNeighbourConflictComplete`, `originalNeighbourHasLiteralSharedPlaquette`, and an instance `originalLinkStarFiniteNeighbourGraph : Nat → P06.FiniteNeighbourGraph`. Thus existing `P06.concreteDegree` can count the **actual enumerated link-star conflicts**, with the original shared-plaquette witness intact.

**Critical counting convention:** the conflict graph has self-conflict, so a closed neighbourhood has size at most 19 (one centre plus up to 18 other links); it is NOT the same as the existing P06 periodic block nearest-neighbour degree eight. Native proof of the 19 closed-neighbourhood bound and its distinct-marked 18-removal corollary is outstanding. Do not silently substitute a block-graph degree-eight estimate.

This is finite source construction and proof terms only. `P06.FiniteNeighbourGraph` does not imply a physical P06ModelLeafDischargePackage; that still needs real original Wilson polymers, source-preserving support/tree/decorations and Gibbs activity suppression. Likewise `chargeSumBelowPhysicalRootedShell` remains unpaid. Current turn produced GitHub source, not an Agda 2.9 kernel acceptance receipt.


## 2026-11-09 original link-graph source partition progress

The native D1/P06 original positive-bond graph module now carries the following exact proof terms:

- `originalLinkStarConflictSymmetric`: original plaquette-overlap conflict is symmetric, using the original symmetric star-separation lemma;
- `originalLinkStarConflictReflexive` and `originalNeighbourListContainsSelf`: the graph is **closed-neighbourhood** counting, including the marked link itself;
- `originalGreedyFilteredLinkHasNoSourceConflict` and `originalGreedyFilteredLinkNotInClosedNeighbourhood`: every native greedy-filter survivor is excluded from the actual source conflict neighbourhood;
- `originalNonConflictIffStarSeparation`: constructive recovery of original star disjointness from failure of conflict using the existing finite decider;
- `originalMarkedBondFreeOrNativeNeighbour`: a constructive, non-vacuous membership cover of each original marked positive bond by the actual source greedy-filter survivors or source enumerated closed conflict neighbours.

**Updated finite maximum cut:** Prove uniqueness/no-duplicates of `originalAllPositiveLinks`, exactly six original plaquettes incident to each link, and source list bound `length (originalLinkStarNeighbourList a) ≤ 19`. Then finite intersection/list-subtraction cardinality converts `originalMarkedBondFreeOrNativeNeighbour` + separation into the existing `OriginalStar18RemovalBound`, after excluding selected head (self-neighbour). The structurally recursive `fuelGreedyOriginal19PackingFullLength` already transports this into the 19-packing conclusion *conditional on that bound*. No new abstract polymer counting is necessary.

The original Wilson sparse-frustrated/mixed activity estimate that inhabits `chargeSumBelowPhysicalRootedShell`, plus E1/D2/N1/G1, remains a genuinely separate physical mathematical frontier. These changes are GitHub source-written, not kernel-accepted; run Agda 2.9/type-check the complete dependency graph before promotion.
