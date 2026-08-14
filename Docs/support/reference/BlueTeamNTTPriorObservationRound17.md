# Blue-Team NTT Prior / Observation / Search Geometry — Round 17

This tranche continues the defensive MLWE/ML-KEM programme at the point where generic candidate-fibre machinery is no longer the main obstacle. The live questions are concrete: conditional list size under actual FIPS coordinates, reconciliation/separator complexity, transition/update geometry of exhaustive verification, and the value of concrete observations after acquisition cost.

No ML-KEM break or security proof is claimed.

## New strongest finite results

Two further source-faithful results now sharpen the frontier.

`MLKEMNTTActualCBD2FullTripleListProfileExact` exhausts all `5^3 = 125` CBD2 triples on source degrees 0, 8 and 12 under two actual FIPS constant-component scalar maps. The first scalar has exactly 16 unordered collision pairs. The joint pair of actual scalars has zero unordered collision pairs on the complete slice.

`MLKEMNTTActualCBD2ConditionalListMassExact` converts those collision counts into exact finite conditional-list mass. With `N=125` candidates and `P` unordered collision pairs, total list mass is `N + 2P`. Hence the first scalar has mass `157`, while the two-scalar observation has mass `125`. Under a uniform finite prior this is mean list-size data `157/125 -> 125/125`.

`MLKEMButterflyStageLocalityInvariantExact` strengthens the coefficient-vs-NTT locality identity across every canonical FIPS Algorithm-9 butterfly stage. Source-support widths `1,2,4,8,16,32,64,128` pair with remaining scalar fanouts `128,64,32,16,8,4,2,1`; after the BaseCase `2*k` public-output factor, every stage has structural locality area exactly `256*k` — 512, 768 and 1024 for the approved parameter sets.

These are local finite/dataflow theorems, not a global key-recovery result, universal uncertainty theorem or runtime lower bound.

## FIPS NTT dataflow and locality tradeoff

`MLKEMNTTDataflowCouplingExact` follows NIST FIPS 203 Algorithm 9, equations (4.10)–(4.13), and BaseCaseMultiply in Algorithm 12. One scalar secret NTT component depends on a 128-coefficient parity class; one quadratic secret residue pair spans all 256 coefficients of its source polynomial. BaseCaseMultiply then recouples the two local components before the public equation is checked.

`MLKEMCandidateMoveFanoutExact` turns that dependency around: a one-coefficient source move is potentially visible across `256*k` public-residual scalar coordinates.

`MLKEMLocalityAreaInvariantExact` exposes the endpoint representation-geometry identity:

- coefficient-local: prior support `1`, public fanout `256*k`;
- scalar-NTT-local: prior support `128`, public fanout `2*k`.

The stronger butterfly-stage theorem shows that this endpoint equality persists through every canonical intermediate Algorithm-9 stage.

Primary source: National Institute of Standards and Technology, *Module-Lattice-Based Key-Encapsulation Mechanism Standard*, FIPS 203 (2024), DOI `10.6028/NIST.FIPS.203`.

## Conditioned BaseCase equations and ambiguity

`MLKEMBaseCaseConditionedResidualExact` proves that conditioning `s0` leaves

`c0 - a0*s0 = a1*s1*gamma + e0`

and

`c1 - a1*s0 = a0*s1 + e1`.

`ConditionedResidualAmbiguityRegressionExact` and `ConditionalMateAmbiguityExact` show that simplification does not imply a unique remaining mate. `ConditionalReconciliationSearchExact` remains the positive seam: if a real conditional-mate theorem exists, one outer candidate can construct a global witness without Cartesian pairing.

## Actual FIPS CBD2 local-list geometry

`MLKEMNTTActualCBD2ScalarCollisionExact` proves that two distinct CBD2-supported source triples collide on the first constant NTT scalar. The multipliers at source degrees 0, 8 and 12 are `1`, `296`, and `2319`, and both `(-1,-1,+1)` and `(+2,0,-2)` map to scalar value `2022`.

`MLKEMNTTActualCBD2SliceCouplingExact` independently shows a two-coefficient FIPS-constant slice whose transported joint support is non-Cartesian.

`MLKEMNTTActualCBD2TwoScalarRefinementExact` uses a second actual scalar at residue `i=2`, where the relevant weights are `1`, `296`, `1010`; the old colliding pair separates.

The exhaustive 125-candidate module strengthens that local example: on the whole selected three-coefficient slice, the first scalar leaves 16 collision pairs while the two-scalar code leaves none.

## List-decoding language

`FiniteMLWEListDecodingGeometryExact` recasts the existing 2x2 Z/5 MLWE lab as a finite list-decoding problem `L(t,tau) = {s' : Score(t-A*s') <= tau}`. The exact score vector is `2,0,0,2`; thresholds 0 and 1 give list size 2, while threshold 2 gives list size 4.

The new exhaustive CBD2 list-mass result is the source-faithful counterpart: an actual FIPS scalar partition has average finite list size `157/125`, while a second real scalar collapses the selected slice to unit average list size.

## Search transition geometry and mixed-radix Gray traversal

`ProtectedLabelSearchGeometryExact` upgrades a candidate fibre into a system with admissible search edges, a machine representation, edge/update cost, reconciliation cost, and observation-induced geometry changes.

`GrayPathTransitionOptimalExact` and `SearchGraphEmbeddingDistortionExact` separate equal-rate encodings by transition geometry. `FiniteMLWETransitionGeometryExact` and `IncrementalResidualTraversalExact` carry that distinction into the finite MLWE lab.

`CBD2MixedRadixGrayTraversalExact` uses the five-value CBD2 coefficient alphabet. For a two-coefficient 25-state carrier, row-major traversal costs 40 while boustrophedon/mixed-radix Gray traversal costs 24. Candidate cardinality is unchanged.

## Observation value and separator geometry

`ObservationSeparatorGeometryExact` shows that observation value need not track candidate-count reduction: one finite observation removes one candidate but collapses separator work from 80 to 12 after acquisition cost.

`ObservationAcquisitionCostExact` compares `recovery-before` against `observation-cost + recovery-after`, so strict candidate shrink is not sufficient for attack progress.

`AttackerObservationLanguageRefinementExact` gives the quotient-theoretic version: enlarging the admitted observation language can only refine attacker observational equivalence, and a newly admitted coordinate matters only with an explicit same-base-observation split witness.

## Representation-security minimax

`RepresentationSecurityGameExact` packages the cross-pollination between computational geometry and physical observation geometry. Its finite minimax regression makes the faster representation worse under one side observation, so transition-optimal and leakage-optimal representations are not identified.

`RepresentationLeakageGeometryExact` keeps the physical side-channel claim boundary explicit: different Hamming movement can define a different observation surface without implying that smaller movement is universally safer.

## Rate / guessing / recovery remain different coordinates

`CryptoRepresentationParetoExact` retains rate, transition cost, reopening cost and observation cost separately. `AdaptiveCandidateResidualWidthExact`, `ConditionalResidualRateExact`, and `FiniteGuessingProbabilityExact` keep fibre-local residual width, finite expected rate, guessing improvement, and computational recovery improvement distinct.

The hierarchy remains strict:

`rate reduction != guessing improvement != candidate shrink != search-cost improvement`.

## Frontier after this tranche

The shortest remaining mathematical targets are narrower again:

1. enlarge the exhaustive source-faithful carrier beyond three CBD2 coefficients and measure how quickly additional actual FIPS coordinates collapse conditional list mass;
2. derive conditional mate/separator complexity for those larger lists rather than stopping at list size;
3. determine whether the all-stage `256*k` locality invariant extends to a broader class of invertible stage-local representations or fails outside the canonical FIPS butterfly network;
4. generalize mixed-radix Gray incremental traversal to larger CBD blocks and compare residual-update work with list-pruning gains;
5. value real implementation/protocol observations by their change to optimal protected-label recovery geometry after acquisition cost.

The working thesis is:

`protected-label quotient + conditional list + search graph + representation geometry + observation refinement + algorithm-relative recovery cost`.

No GitHub Actions or CodeRabbit run is required by this tranche. `scripts/check_crypto_ntt_prior_observation_round17.sh` fail-closes the source surface and invokes the Round-17 aggregate when Agda is locally available. No kernel-clean claim is made without an observed typecheck.
