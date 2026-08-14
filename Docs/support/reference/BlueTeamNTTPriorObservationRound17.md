# Blue-Team NTT Prior / Observation / Search Geometry — Round 17

This tranche continues the defensive MLWE/ML-KEM programme at the point where generic candidate-fibre machinery is no longer the main obstacle. The live questions are now concrete: conditional list size under actual FIPS coordinates, reconciliation/separator complexity, transition/update geometry of exhaustive verification, and the value of concrete observations after acquisition cost.

No ML-KEM break or security proof is claimed.

## FIPS NTT dataflow and locality tradeoff

`MLKEMNTTDataflowCouplingExact` follows NIST FIPS 203 Algorithm 9, equations (4.10)–(4.13), and BaseCaseMultiply in Algorithm 12. One scalar secret NTT component depends on a 128-coefficient parity class; one quadratic secret residue pair spans all 256 coefficients of its source polynomial. BaseCaseMultiply then recouples the two local components before the public equation is checked.

`MLKEMCandidateMoveFanoutExact` turns that dependency around: a one-coefficient source move is potentially visible across `256*k` public-residual scalar coordinates.

`MLKEMLocalityAreaInvariantExact` exposes a new representation-geometry identity. For the two canonical primitive move notions:

- coefficient-local: prior support `1`, public fanout `256*k`;
- scalar-NTT-local: prior support `128`, public fanout `2*k`.

Hence their structural locality areas are exactly equal:

`1*(256*k) = 128*(2*k) = 256*k`.

For the approved parameter sets this area is exactly 512, 768, and 1024. This is not a universal uncertainty theorem, but it is an exact same-parameter manifestation of the prior-locality / verifier-locality tradeoff.

Primary source: National Institute of Standards and Technology, *Module-Lattice-Based Key-Encapsulation Mechanism Standard*, FIPS 203 (2024), DOI `10.6028/NIST.FIPS.203`.

## Conditioned BaseCase equations and ambiguity

`MLKEMBaseCaseConditionedResidualExact` proves that conditioning `s0` leaves

`c0 - a0*s0 = a1*s1*gamma + e0`

and

`c1 - a1*s0 = a0*s1 + e1`.

The identities need only additive cancellation around the opaque multiplication terms. `ConditionedResidualAmbiguityRegressionExact` and `ConditionalMateAmbiguityExact` then show that simplification of the equation does not imply a unique remaining mate. `ConditionalReconciliationSearchExact` remains the positive seam: if a real conditional-mate theorem exists, one outer candidate can construct a global witness without Cartesian pairing.

## Actual FIPS CBD2 local-list geometry

The programme now contains source-faithful finite slices rather than only abstract transforms.

`MLKEMNTTActualCBD2ScalarCollisionExact` uses actual FIPS constants and proves that two distinct CBD2-supported source triples collide on the first constant NTT scalar. The multipliers at source degrees 0, 8 and 12 are `1`, `296`, and `2319`, and both

`(-1,-1,+1)`

and

`(+2,0,-2)`

map to scalar value `2022`.

`MLKEMNTTActualCBD2SliceCouplingExact` independently shows a two-coefficient FIPS-constant slice whose transported joint support is non-Cartesian.

`MLKEMNTTActualCBD2TwoScalarRefinementExact` advances the collision to a genuine conditional-list calculation. For residue `i=2`, `gamma_2 = 17^65 = 2761 (mod 3329)` and the relevant weights are `1`, `296`, `1010`. The two old colliding sources map to 713 and 1311 respectively. Thus on this exact two-point CBD2 slice:

- first scalar only: candidate list size 2;
- first plus second scalar: candidate list size 1.

This is local conditional-list geometry, not global ML-KEM key recovery.

## List-decoding language

`FiniteMLWEListDecodingGeometryExact` recasts the existing 2x2 Z/5 MLWE lab as a finite list-decoding problem:

`L(t,tau) = {s' : Score(t-A*s') <= tau}`.

The exact score vector is `2,0,0,2`; therefore thresholds 0 and 1 give list size 2, while threshold 2 gives list size 4. Unique-decoding, small-list, and full-list regimes are kept separate from the later question of recovery work.

## Search transition geometry and mixed-radix Gray traversal

`ProtectedLabelSearchGeometryExact` upgrades a candidate fibre from a set into a system with admissible search edges, a machine representation, edge/update cost, reconciliation cost, and observation-induced geometry changes.

`GrayPathTransitionOptimalExact` and `SearchGraphEmbeddingDistortionExact` separate equal-rate encodings by transition geometry. `FiniteMLWETransitionGeometryExact` and `IncrementalResidualTraversalExact` carry that distinction into the finite MLWE lab.

`CBD2MixedRadixGrayTraversalExact` now uses the real five-value CBD2 coefficient alphabet. For a two-coefficient 5x5 carrier with 25 states:

- ordinary row-major traversal has Manhattan transition cost 40;
- boustrophedon / mixed-radix Gray traversal has cost 24.

The candidate set is identical; only the traversal geometry changes. This is the finite precursor to incrementally maintaining `r(s)=t-A*s` while enumerating an unchanged exponential search space.

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

The shortest remaining mathematical targets are now concrete rather than architectural:

1. enlarge the source-faithful CBD2 slices and compute conditional survivor/list-size profiles under increasing sets of actual FIPS NTT/public coordinates;
2. determine whether those conditional lists admit low-cost mate reconstruction or bounded-separator reconciliation despite the connected dataflow graph;
3. lift the finite locality-area identity toward a genuine support-spreading/no-simultaneous-locality theorem, without calling it a universal uncertainty principle until proved;
4. generalize mixed-radix Gray incremental residual traversal from two coefficients to larger CBD blocks and compare exact verifier-update work across coefficient and NTT representations;
5. measure any real protocol/implementation observation by the induced change in optimal protected-label recovery geometry after acquisition cost;
6. move to probabilistic min-entropy / game-advantage semantics only once the finite conditional-list and cost carriers are stable.

The working thesis is now:

`protected-label quotient + conditional list + search graph + representation geometry + observation refinement + algorithm-relative recovery cost`.

No GitHub Actions or CodeRabbit run is required by this tranche. `scripts/check_crypto_ntt_prior_observation_round17.sh` fail-closes the source surface and invokes the Round-17 aggregate when Agda is locally available. No kernel-clean claim is made without an observed typecheck.
