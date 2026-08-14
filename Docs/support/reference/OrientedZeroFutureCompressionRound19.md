# Oriented-zero future compression — Round 19

This tranche continues the merged PNF/future-equivalence/LLM compression spine with a physically motivated zero-crossing refinement and the quantitative compression theorems it exposes.

## Oriented zero

The coarse scalar carrier is `{-1,0,+1}` while the fine wave carrier is `{-1,-0,+0,+1}` with path

`-1 -> -0 -> +0 -> +1`.

The coarse scalar projection merges `-0` and `+0`, but one wave step separates their scalar futures. `OrientedZeroCanonicalFutureExact` proves this in the repository's canonical proof-bearing future-observation relation.

The distinction is local: nonzero scalar fibres are singletons, while the zero fibre contains the two orientations `approachingZero` and `leavingZero`.

## Coding minimality

Two separate coding problems are formalized and deliberately not conflated.

1. A standalone fixed-length code for all four `Wave4` states needs two bits. One bit cannot exactly decode even the three-state subset `{-1,-0,+0}`, while the four two-bit words are all used by the exact binary code.
2. When the scalar projection is already retained, only the zero fibre needs an additional residual bit. The dependent/adaptive residual carries no orientation payload on the two singleton nonzero fibres.

Thus the PNF residual cost is fibre-local rather than the full standalone state-code cost.

`OrientedZeroGrayTransitionGeometryExact` further proves that ordinary binary and Gray codes have equal rate and exact reopening but different phase-path Hamming geometry: total path distortion is 4 for the ordinary binary ordering and 3 for the Gray ordering.

## Generic arbitrary-k residual bound

`GeneralResidualFibreCardinalityExact` proves constructively that a coarse fibre with `k` pairwise future-distinct representatives forces an injection

`Fin k -> Residual`

for every dynamically sufficient residual.  When the residual is a fixed `b`-bit carrier `Fin (2^b)`, the Agda standard library's finite pigeonhole theorem yields

`k <= 2^b`.

This is the exact general capacity inequality underlying `b >= ceil(log2 k)`.

## Future rate-distortion

`FutureRateDistortionOrientedZeroExact` provides a finite zero-crossing regression: with scalar state retained, no residual has unit deterministic future distortion at rate 0; the oriented residual has distortion 0 at rate 1. Relaxing the allowed distortion from 0 to 1 drops the optimal residual rate from 1 to 0.

`FutureRateDistortionGenericExact` abstracts this. For any certified candidate family, if `epsilon <= epsilon'`, the optimum at `epsilon'` cannot have greater rate than the optimum at `epsilon`. A consumer-specific zero-distortion theorem transports exact future safety to the zero-distortion optimum.

This is the finite theorem surface for the programmatic object

`R_C(epsilon) = minimum carrier/residual rate subject to bounded consumer-future distortion`.

No Shannon asymptotic coding theorem is claimed.

## Generic partition refinement and stabilization

`GenericFuturePartitionRefinementExact` formalizes

`P_0 = current observation equality`

and

`P_(n+1)(x,y) = current equality AND every same-action successor lies in P_n`.

It proves refinement monotonicity and persistence after a fixed point.

`FiniteRankedRefinementStabilizationExact` proves a separate generic termination theorem: any decidable refinement process whose unstable step strictly raises a natural rank bounded by `N` reaches a fixed point within `N` steps. For finite partitions, the intended rank is block count. The remaining adapter is the concrete theorem that a strict split of a finite partition strictly raises its block count; no stabilization assumption is hidden in the generic theorem.

`OrientedZeroPartitionRefinementExact` instantiates the recurrence: `-0` and `+0` agree at depth 0 and separate at depth 1, while the singleton nonzero blocks need no extra local split.

## Phase orthogonality

`OrientedZeroPhaseOrthogonalityExact` introduces zero-crossing orientation as a fibre-local coordinate separate from C3 process/task phase and evidence-derived semantic phase. Orientation flip preserves both process and semantic phase; process advance preserves orientation; the two operations commute.

This extends the previous modality/process/semantic separation without overloading C3.

## Approximate multimodal and multi-resolution futures

`ApproximateMultimodalFutureEquivalenceExact` proves that if text and visual encodings are within latent distance `eta`, and the declared consumer is `L`-stable, then every query-trace observation is within `L * eta`. Representation rate is carried separately, so a cheaper visual encoding becomes a certified compression only together with the future-distortion bound.

`DynamicApproximateMultiResolutionErrorExact` gives a finite-trace error theorem with separately typed compression, selection, local-residual, and modality defects. One-step error recurrence implies total trace error is bounded by initial error plus the accumulated local defect budget.

## Spectral grokking and learner state

`SpectralGrokkingPhaseDynamicsExact` reuses the existing task-character law. In its exact finite learning trajectory, character-aligned amplitude rises before held-out behaviour changes, while training correctness remains flat. It also gives a separate signed-zero-like learning-direction carrier: equal visible zero gain can lie on two different learning futures.

`FullLearningStateFutureQuotientExact` expands the fine learner carrier to parameters, optimizer state, curriculum/provenance, and replay state. Two learners with identical current parameters can diverge under the same batch. Retaining optimizer/provenance/replay as a residual reopens the learner exactly.

## Analytic boundary

The merged Round-18 Cantor lane already supplies the infinite polar stream carrier, exact projective cylinder masses, and constructive ambient-width decay. The repository still has no sigma-algebra/countable-additivity/measure-extension infrastructure, so this tranche does not fabricate a sigma-additive Cantor probability measure. The remaining analytic wall is genuinely foundational rather than another finite accounting lemma.

## Validation boundary

The round-19 checker cascades the round-18 checker, rejects postulates, holes, unsafe/trust escapes in the tranche, checks load-bearing theorem names, and invokes the cumulative Agda aggregate if `agda` is available. GitHub Actions and CodeRabbit are not required for this tranche.
