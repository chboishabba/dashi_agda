# Blue-Team NTT Prior / Observation / Search Geometry — Round 17

This tranche continues the defensive MLWE/ML-KEM programme at the point where generic candidate-fibre machinery is no longer the main obstacle. The live questions are now concrete: conditional list size under actual FIPS coordinates, reconciliation/separator complexity, transition/update geometry of exhaustive verification, and the value of concrete observations after acquisition cost.

No ML-KEM break or security proof is claimed.

## FIPS NTT dataflow and locality tradeoff

`MLKEMNTTDataflowCouplingExact` follows NIST FIPS 203 Algorithm 9, equations (4.10)–(4.13), and BaseCaseMultiply in Algorithm 12. One scalar secret NTT component depends on a 128-coefficient parity class; one quadratic secret residue pair spans all 256 coefficients of its source polynomial. BaseCaseMultiply then recouples the two local components before the public equation is checked.

`MLKEMCandidateMoveFanoutExact` turns that dependency around: a one-coefficient source move is potentially visible across `256*k` public-residual scalar coordinates.

`MLKEMLocalityAreaInvariantExact` exposes the endpoint representation-geometry identity:

- coefficient-local: prior support `1`, public fanout `256*k`;
- scalar-NTT-local: prior support `128`, public fanout `2*k`.

Hence both structural locality areas equal `256*k`, namely 512, 768 and 1024 for the approved parameter sets.

`MLKEMButterflyStageLocalityInvariantExact` strengthens that result across the entire canonical Algorithm-9 butterfly ladder. At the eight stages, source-support widths are

`1,2,4,8,16,32,64,128`

while remaining same-parity scalar fanouts are

`128,64,32,16,8,4,2,1`.

After the BaseCase `2*k` public-output factor, every stage has the same structural locality area `256*k`. Thus the coefficient/NTT endpoint equality was not an isolated coincidence: it is invariant across every canonical butterfly stage. This is still only a FIPS-network/dataflow theorem; it is not promoted to a universal Fourier uncertainty theorem or runtime lower bound.

Primary source: National Institute of Standards and Technology, *Module-Lattice-Based Key-Encapsulation Mechanism Standard*, FIPS 203 (2024), DOI `10.6028/NIST.FIPS.203`.

## Conditioned BaseCase equations and ambiguity

`MLKEMBaseCaseConditionedResidualExact` proves that conditioning `s0` leaves

`c0 - a0*s0 = a1*s1*gamma + e0`

and

`c1 - a1*s0 = a0*s1 + e1`.

The identities need only additive cancellation around the opaque multiplication terms. `ConditionedResidualAmbiguityRegressionExact` and `ConditionalMateAmbiguityExact` then show that simplification of the equation does not imply a unique remaining mate. `ConditionalReconciliationSearchExact` remains the positive seam: if a real conditional-mate theorem exists, one outer candidate can construct a global witness without Cartesian pairing.

## Actual FIPS CBD2 local-list geometry

The programme now contains source-faithful finite slices rather than only abstract transforms.

`MLKEMNTTActualCBD2ScalarCollisionExact` uses actual FIPS constants and proves that two distinct CBD2-supported source triples collide on the first constant NTT scalar. The multipliers at source degrees 0, 8 and 12 are `1`, `296`, and `2319`, and both `(-1,-1,+1)` and `(+2,0,-2)` map to scalar value `2022`.

`MLKEMNTTActualCBD2SliceCouplingExact` independently shows a two-coefficient FIPS-constant slice whose transported joint support is non-Cartesian.

`MLKEMNTTActualCBD2TwoScalarRefinementExact` advances the collision to a conditional-list calculation. For residue `i=2`, `gamma_2 = 17^65 = 2761 (mod 3329)` and the relevant weights are `1`, `296`, `1010`. The two old colliding sources map to 713 and 1311 respectively. Thus on that exact two-point slice the list shrinks `2 -> 1` after adding the second real scalar.

`MLKEMNTTActualCBD2FullTripleListProfileExact` now exhausts the complete `5^3 = 125` CBD2 triple carrier at those same source degrees. It computes all unordered candidate pairs definitionally and proves:

- candidate count: 125;
- collision pairs under the first actual scalar: exactly 16;
- collision pairs under the joint `(scalar0, scalar2)` observation: exactly 0.

So the earlier two-point example is part of a stronger finite fact: on this entire three-coefficient CBD2 slice, the second actual FIPS scalar resolves every collision left by the first.

`MLKEMNTTActualCBD2ConditionalListMassExact` converts the collision counts into uniform finite conditional-list mass. For a finite observation partition, total list mass is `N + 2P`, where `P` is the unordered collision-pair count. Hence the first-scalar slice has total list mass `125 + 2*16 = 157`, while the two-scalar slice has `125`. Under the uniform finite prior this gives mean list-size data `157/125 -> 125/125`. This is exact finite list accounting, not Shannon/min-entropy and not full-scheme recovery complexity.

## List-decoding language

`FiniteMLWEListDecodingGeometryExact` recasts the existing 2x2 Z/5 MLWE lab as a finite list-decoding problem:

`L(t,tau) = {s' : Score(t-A*s') <= tau}`.

The exact score vector is `2,0,0,2`; thresholds 0 and 1 give list size 2, while threshold 2 gives list size 4. Unique-decoding, small-list, and full-list regimes are kept separate from recovery work.

## Search transition geometry and mixed-radix Gray traversal

`ProtectedLabelSearchGeometryExact` upgrades a candidate fibre from a set into a system with admissible search edges, a machine representation, edge/update cost, reconciliation cost, and observation-induced geometry changes.

`GrayPathTransitionOptimalExact` and `SearchGraphEmbeddingDistortionExact` separate equal-rate encodings by transition geometry. `FiniteMLWETransitionGeometryExact` and `IncrementalResidualTraversalExact` carry that distinction into the finite MLWE lab.

`CBD2MixedRadixGrayTraversalExact` uses the real five-value CBD2 coefficient alphabet. For a two-coefficient 5x5 carrier with 25 states:

- row-major traversal cost: 40;
- boustrophedon / mixed-radix Gray traversal cost: 24.

The candidate set is identical; only traversal geometry changes. This is the finite precursor to incrementally maintaining `r(s)=t-A*s` while enumerating an unchanged exponential search space.

## Observation value and separator geometry

`ObservationSeparatorGeometryExact` shows that observation value need not track candidate-count reduction: a finite observation removes one candidate but collapses separator work from 80 to 12 after acquisition cost.

`ObservationAcquisitionCostExact` compares `recovery-before` against `observation-cost + recovery-after`, so strict candidate shrink is not sufficient for attack progress.

`AttackerObservationLanguageRefinementExact` gives the quotient-theoretic version: enlarging the admitted observation language can only refine attacker observational equivalence, and a newly admitted coordinate matters only with an explicit same-base-observation split witness.

## Representation-security minimax

`RepresentationSecurityGameExact` packages the cross-pollination between computational geometry and physical observation geometry. The finite blue-team objective is minimax-shaped: choose an implementation representation whose worst allowed observation gain is smallest.

Its regression deliberately makes the faster representation worse under one side observation:

- fast representation: transition cost 5, worst observation gain 20;
- conservative representation: transition cost 8, worst observation gain 3.

Thus transition-optimal representation is not automatically leakage-optimal representation.

`RepresentationLeakageGeometryExact` keeps the physical side-channel claim boundary explicit: different Hamming movement can define a different observation surface without implying that smaller movement is universally safer.

## Rate / guessing / recovery remain different coordinates

`CryptoRepresentationParetoExact` retains rate, transition cost, reopening cost and observation cost as separate Pareto coordinates. `AdaptiveCandidateResidualWidthExact`, `ConditionalResidualRateExact`, and `FiniteGuessingProbabilityExact` keep fibre-local residual width, finite expected rate, guessing improvement, and computational recovery improvement distinct.

The resulting hierarchy is deliberately strict:

`rate reduction != guessing improvement != candidate shrink != search-cost improvement`.

## Frontier after this tranche

The shortest remaining mathematical targets are now narrower again:

1. grow the exhaustive source-faithful carrier beyond three CBD2 coefficients and measure how rapidly additional actual FIPS coordinates collapse conditional list mass;
2. derive conditional mate/separator complexity for those larger lists rather than stopping at list size;
3. determine whether the all-stage `256*k` locality invariant extends to any broader class of invertible stage-local representations, or fails outside the canonical FIPS butterfly network;
4. generalize mixed-radix Gray incremental traversal to larger CBD blocks and compare exact residual-update work with list-pruning gains;
5. value real implementation/protocol observations by their change to optimal protected-label recovery geometry after acquisition cost.

The working thesis is now:

`protected-label quotient + conditional list + search graph + representation geometry + observation refinement + algorithm-relative recovery cost`.

No GitHub Actions or CodeRabbit run is required by this tranche. `scripts/check_crypto_ntt_prior_observation_round17.sh` fail-closes the source surface and invokes the Round-17 aggregate when Agda is locally available. No kernel-clean claim is made without an observed typecheck.
