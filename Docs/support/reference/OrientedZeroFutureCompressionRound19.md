# Oriented-zero future compression — Round 19

This tranche continues the merged PNF/future-equivalence/LLM compression spine with a physically motivated zero-crossing refinement and the quantitative compression theorems it exposes.

## Oriented zero

The coarse scalar carrier is `{-1,0,+1}` while the fine wave carrier is `{-1,-0,+0,+1}` with path

`-1 -> -0 -> +0 -> +1`.

The coarse scalar projection merges `-0` and `+0`, but one wave step separates their scalar futures. `OrientedZeroCanonicalFutureExact` proves this in the repository's canonical proof-bearing future-observation relation.

The distinction is local: nonzero scalar fibres are singletons, while the zero fibre contains the two orientations `approachingZero` and `leavingZero`.

## Coding minimality and conditional information geometry

Two coding problems are formalized and deliberately not conflated.

1. A standalone fixed-length code for all four `Wave4` states needs two bits. `OrientedZeroCeilLog2Exact` carries the exact least-capacity certificate `ceil(log2 4) = 2`; all four two-bit words are used by the exact binary code.
2. When the scalar projection is already retained, only the zero fibre needs an additional residual bit. `OrientedZeroConditionalResidualCardinalityExact` proves exact fibre cardinalities `1,2,1` and least local bit widths `0,1,0` over `{-1,0,+1}`. The dependent adaptive residual is exactly equivalent to those local finite code spaces.

Thus a two-bit standalone Wave4 code must not be confused with the conditional PNF residual rate. The latter pays one orientation bit only where the coarse zero fibre is dynamically nontrivial.

`OrientedZeroExpectedResidualRateExact` makes the corresponding average-rate statement. Under any normalized scalar-state probability law, the adaptive residual spends `0,1,0` bits on the three coarse fibres, so its expected additional rate is exactly the probability mass of the scalar-zero fibre. This is a conditional residual rate only; total end-to-end rate must also include the retained scalar carrier.

`OrientedZeroGrayTransitionGeometryExact` proves that ordinary binary and Gray codes have equal exact two-bit rate but different phase-path Hamming geometry. Binary has path cost `4`, Gray has path cost `3`. Under the concrete equal-rate objective `rate + transitionCost`, binary costs `6` and Gray costs `5`. Hence MDL/rate optimality does not by itself determine the dynamically best exact code.

## Generic arbitrary-k residual bound

`GeneralResidualFibreCardinalityExact` proves constructively that a coarse fibre with `k` pairwise future-distinct representatives forces an injection

`Fin k -> Residual`

for every dynamically sufficient residual. For a fixed `b`-bit residual carrier `Fin (2^b)`, finite injectivity yields

`k <= 2^b`.

`CeilLog2Certificate` expresses the least-capacity definition of `ceil(log2 k)`, and `safeBitResidualRespectsCeilLog2` proves every safe fixed-bit residual width lies above that certified minimum.

## Future rate-distortion

`FutureRateDistortionOrientedZeroExact` provides a finite zero-crossing regression. With scalar state retained, the rate-0 scalar-only representation has unit deterministic future distortion, while the one-bit oriented residual has distortion zero. Relaxing the distortion budget from `0` to `1` lowers the optimal residual rate from `1` to `0`.

`FutureRateDistortionGenericExact` abstracts this. For any certified candidate family, if `epsilon <= epsilon'`, the optimum at `epsilon'` cannot have greater rate than the optimum at `epsilon`. A consumer-specific zero-distortion theorem transports exact future safety to the zero-distortion optimum.

This is the finite theorem surface for

`R_C(epsilon) = minimum carrier/residual rate subject to bounded consumer-future distortion`.

No Shannon asymptotic coding theorem is claimed.

## Generic partition refinement, stabilization, and quotient compilation

`GenericFuturePartitionRefinementExact` formalizes

`P_0 = current observation equality`

and

`P_(n+1)(x,y) = current equality AND every same-action successor lies in P_n`.

It proves refinement monotonicity and persistence after a fixed point.

`FiniteRankedRefinementStabilizationExact` proves that any decidable refinement process whose unstable step strictly raises a natural rank bounded by `N` reaches a fixed point within `N` steps. For finite partitions the intended rank is block count.

`StablePartitionCanonicalFutureBridgeExact` closes the semantic seam for every total deterministic system: if `P_n` is a refinement fixed point, then `P_n(left,right)` is equivalent to the repository's canonical proof-bearing `FutureObservationEquivalent(left,right)`. The proof factors through equality of observations along every finite action trace.

`CertifiedFiniteFutureQuotientCompilerExact` combines a certified executable partition refiner, bounded-rank termination, and the stable-partition bridge. Given an initial code implementing `P_0`, an `advance` operation implementing one refinement step, and a bounded rank strictly increased by every unstable step, `compileFutureQuotient` returns a stable depth and proves that the resulting relation is exactly canonical future equivalence.

For the signed-zero machine, `OrientedZeroCanonicalPartitionPresentationExact` proves `P_1` is already injective on the four oriented states and therefore stable. `OrientedZeroCertifiedCompilerExact` instantiates the compiler with a two-stage partition code: `scalarPartition` has three blocks, `orientedPartition` has four, one strict split raises rank `3 -> 4`, and the compiler computes stabilization depth exactly `1`. Thus the scalar zero block is split once and the computation is done.

## Phase orthogonality

`OrientedZeroPhaseOrthogonalityExact` introduces zero-crossing orientation as a fibre-local coordinate separate from C3 process/task phase and evidence-derived semantic phase. Orientation flip preserves both process and semantic phase; process advance preserves orientation; the two operations commute.

This extends the previous modality/process/semantic separation without overloading C3.

## Approximate multimodal and multi-resolution futures

`ApproximateMultimodalFutureEquivalenceExact` proves that if text and visual encodings are within latent distance `eta`, and the declared consumer is `L`-stable, then every query-trace observation is within `L * eta`. Representation rate is carried separately, so a cheaper visual encoding becomes a certified compression only together with the future-distortion bound.

`DynamicApproximateMultiResolutionErrorExact` gives a finite-trace error theorem with separately typed compression, selection, local-residual, and modality defects. One-step error recurrence implies total trace error is bounded by initial error plus the accumulated local defect budget.

## Spectral grokking and learner state

`SpectralGrokkingPhaseDynamicsExact` reuses the existing task-character law. In its exact finite learning trajectory, character-aligned amplitude rises before held-out behaviour changes, while training correctness remains flat. It also gives a separate signed-zero-like learning-direction carrier: equal visible zero gain can lie on two different learning futures. This is an isomorphic future-refinement pattern, not an identification of physical signed zero with learning dynamics.

`FullLearningStateFutureQuotientExact` expands the fine learner carrier to parameters, optimizer state, curriculum/provenance, and replay state. Two learners with identical current parameters can diverge under the same batch. Retaining optimizer/provenance/replay as a residual reopens the learner exactly.

## Cantor boundary advanced to null covers

The merged Round-18 Cantor lane supplies the infinite polar stream carrier, exact projective cylinder masses, and constructive ambient-width decay. `CantorDyadicNullCoverExact` now packages the latter as an explicit null-cover modulus: for every dyadic tolerance `2^-k`, depth `2k` gives a surviving Cantor-stage cover whose total ordinary ambient width is at most that tolerance, while intrinsic/projective root mass remains one.

This is the constructive covering content behind `lambda(C)=0`, but the repository still has no sigma-algebra/countable-additivity/measure-extension infrastructure. This tranche therefore does not fabricate a sigma-additive Cantor probability measure. That extension remains the genuine analytic wall.

## Validation boundary

The round-19 checker cascades the round-18 checker, rejects postulates, holes, unsafe/trust escapes in the tranche, checks the load-bearing theorem names including the generic quotient compiler and signed-zero depth-one computation, and invokes the cumulative Agda aggregate if `agda` is available. GitHub Actions and CodeRabbit are not used for this tranche.
