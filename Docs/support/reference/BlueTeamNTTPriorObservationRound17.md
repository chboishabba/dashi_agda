# Blue-Team NTT Prior / Observation / Search Geometry — Round 17

This tranche continues both remaining defensive crypto programmes simultaneously:

1. determine whether MLWE/ML-KEM search becomes genuinely simpler in transformed coordinates;
2. determine whether a protocol/implementation exposes a hidden-dependent observation that changes protected-label recovery cost.

Round 17 now adds a third coordinate from the future-quotient/Gray representation programme:

3. candidate fibres carry **transition/search geometry**, so equal cardinality or equal storage rate does not imply equal recovery cost.

It does not claim an ML-KEM break or security proof.

## FIPS NTT dataflow

`MLKEMNTTDataflowCouplingExact` follows NIST FIPS 203 Algorithm 9, equations (4.10)–(4.13), and BaseCaseMultiply in Algorithm 12.

Algorithm 9 has seven butterfly stages with lengths

`128, 64, 32, 16, 8, 4, 2`.

The dependency width doubles seven times from one source coefficient to 128 source coefficients for one scalar **secret NTT representation** component. Reduction modulo a quadratic factor sends the 128 even source coefficients into the constant secret component and the 128 odd source coefficients into the linear secret component. Thus one secret quadratic residue pair structurally spans all 256 source coefficients of one secret polynomial.

For module dimension `k`, the secret representation widths are therefore:

- ML-KEM-512: scalar 256 across the two secret polynomials; quadratic pair 512;
- ML-KEM-768: scalar 384; quadratic pair 768;
- ML-KEM-1024: scalar 512; quadratic pair 1024.

There is an important recoupling at the **public equation**. BaseCaseMultiply uses both local secret components to produce either output component. Consequently either scalar component of one public noisy equation can structurally depend on the complete `256*k` source-secret coefficient carrier.

These are structural/dataflow widths, not claims of statistical dependence or hardness.

Primary source: National Institute of Standards and Technology, *Module-Lattice-Based Key-Encapsulation Mechanism Standard*, FIPS 203 (2024), DOI `10.6028/NIST.FIPS.203`.

## Candidate-move fanout: locality depends on the chosen search coordinates

`MLKEMCandidateMoveFanoutExact` turns the same dependency relation around and asks what happens when the search algorithm changes one **source coefficient**.

A coefficient-local move is potentially visible in all 128 same-parity scalar NTT coordinates of its secret polynomial. After BaseCase multiplication across `k` public rows, one source-coordinate move can structurally fan out to `256*k` public-residual scalar coordinates:

- ML-KEM-512: 512;
- ML-KEM-768: 768;
- ML-KEM-1024: 1024.

This is the exact representation-geometry tradeoff: coefficient-local search moves are broad in NTT/public-residual space, while NTT-local moves are not automatically local under the CBD prior because that prior originates in coefficient space. Structural fanout is not equated with numerical change or runtime cost; cancellation/sparsity/caching require separate proofs.

## No disconnected parity cut and combined connectivity

`MLKEMNTTPriorCutNoGoExact` proves neither same-parity family admits a nontrivial source-variable-disjoint cut with both sides inhabited.

`MLKEMNTTCombinedCouplingConnectivityExact` then adds BaseCase cross-component edges and proves every pair of scalar NTT nodes is connected by a path of length at most two. Hence the combined prior/verifier dataflow graph has no nontrivial disconnected cut.

This is stronger than merely saying NTT is invertible. It rules out disconnected independent scalar search components at this dataflow level. It still does **not** establish statistical dependence, treewidth growth, or MLWE hardness.

## Positive two-block prior factorisation, followed by verifier recoupling

`MLKEMNTTParityBlockPriorExact` records the positive side. A coefficient-product source prior admits natural even/odd blocks:

- 256 + 256 for ML-KEM-512;
- 384 + 384 for ML-KEM-768;
- 512 + 512 for ML-KEM-1024.

But FIPS BaseCaseMultiply couples the local components:

`c0 = a0*s0 + a1*s1*gamma`

`c1 = a0*s1 + a1*s0`.

So two-block prior factorisation does not produce two independent public-verifier problems.

## Exact conditioned BaseCase residual equations

`MLKEMBaseCaseConditionedResidualExact` closes the algebraic seam identified after the previous round. In any additive commutative group carrying the opaque BaseCase multiplication terms, conditioning `s0` and subtracting its known contribution gives exactly

`c0 - a0*s0 = a1*s1*gamma + e0`

and

`c1 - a1*s0 = a0*s1 + e1`.

The proof needs only additive cancellation, so the identities instantiate in the modular quotient ring once its operations provide those laws. This is the exact theorem we needed before asking whether conditioning really halves search.

It does not. `ConditionedResidualAmbiguityRegressionExact` gives a finite Z/5 regression in which two distinct remaining secret bits both satisfy the post-conditioning small-residual test. `ConditionalMateAmbiguityExact` lifts that to a general theorem: two distinct plausible remaining candidates at one conditioned state refute a `UniqueConditionalMate` certificate.

Thus:

`conditioning simplifies the equation != conditioning constructs the mate`.

The positive route remains `ConditionalReconciliationSearchExact`: if a real conditional mate theorem is supplied, one outer candidate plus an assembly map yields a genuine global witness. Its finite cost regression is `12` versus `30` for Cartesian pairing.

## Search transition geometry

`ProtectedLabelSearchGeometryExact` upgrades a candidate fibre from a set into a search system carrying:

- hidden/public/protected-label carriers;
- candidate membership;
- admissible search edges;
- a machine representation;
- exact edge/update cost.

An observation update now changes candidate cardinality, graph cost, reconciliation cost and observation acquisition cost separately. The regression demonstrates that identical `8 -> 7` candidate shrinkage can either improve recovery geometry or make it worse.

`SearchGraphEmbeddingDistortionExact` defines an edge-weighted graph embedding cost. On the same four-state path, ordinary two-bit binary coding has transition distortion 4 while Gray coding has distortion 3.

`GrayPathTransitionOptimalExact` proves the general lower-bound schema: if every path edge has positive code cost, total cost is at least the number of edges. A unit-edge realization attains that bound. The P4 Gray path is the concrete two-bit instance and ordinary binary is strictly worse by one transition unit.

## Finite MLWE representation geometry and incremental traversal

`FiniteMLWETransitionGeometryExact` maps the existing four-secret Z/5 MLWE lab onto this path geometry. The candidate carrier and two-bit rate are unchanged, while ordinary binary traversal costs 4 Hamming units and Gray traversal costs 3.

`IncrementalResidualTraversalExact` adds an explicit per-changed-coordinate update model. Under the declared finite architecture, binary traversal costs 15 work units and Gray traversal costs 12. The candidate set is identical; only the order/transition geometry changed.

This is the blue-team analogue of the representation result:

`same information != same computational geometry`.

## Rate / geometry / reopening Pareto carrier

`CryptoRepresentationParetoExact` keeps rate, transition cost, reopen cost and physical-observation cost as independent objective coordinates rather than imposing universal scalar weights. In the finite regression Gray and binary use the same two-bit rate, but Gray weakly dominates binary because its transition cost is lower.

`AdaptiveCandidateResidualWidthExact` makes the residual representation fibre-local: a two-candidate ambiguity needs one bit, while an identified one-candidate fibre needs zero residual bits.

`ConditionalResidualRateExact` then supplies the finite expected-rate precursor. With an ambiguous one-bit fibre weighted once and an identified zero-bit fibre weighted three times, adaptive residual storage has bit-mass `1/4`; fixed one-bit storage has `4/4`. This is finite weighted accounting only, not yet Shannon entropy.

`FiniteGuessingProbabilityExact` separately keeps guessing/statistical improvement distinct from computational improvement. The same 2-to-1 statistical identification can coexist with an explicitly worse recovery cost.

## Observation-induced separator geometry

`ObservationSeparatorGeometryExact` makes an important consequence explicit: the main value of an observation may be geometric rather than cardinality-based. Its finite regression removes only one candidate (`6 -> 5`) but collapses a separator-state search from 80 work units to 12 after observation acquisition, for a net gain of 68.

A real ML-KEM claim would need the same-object separator witness; this is exact accounting, not an asserted attack.

## Observation acquisition, confirmation, implicit rejection and timing

`ObservationAcquisitionCostExact` compares

`recovery-before`

with

`observation-cost + recovery-after`.

On the finite MLWE regression, pre-observation recovery costs 13 and post-observation recovery costs 8. Acquisition cost 2 gives total 10 and net gain 3; acquisition cost 6 gives total 14 and is harmful by 1.

`KeyConfirmationObservationRefinementExact` treats externally visible confirmation as an observation only when a constructive same-public hidden-state split is supplied. Primary reference: Gorjan Alagic, Elaine Barker, Lily Chen, Dustin Moody, Angela Robinson, Hamilton Silberg, Noah Waller, *Recommendations for Key-Encapsulation Mechanisms*, NIST SP 800-227 (2025), DOI `10.6028/NIST.SP.800-227`.

`MLKEMImplicitRejectProtocolObservationExact` separates internal Algorithm-18 route state from external observability. Different internal candidate/fallback routes can coexist with a constant public-factored observation. Directly exporting the route creates a hidden-dependent split. FIPS requires the comparison flag to remain secret intermediate data.

`MLKEMImplicitRejectTimingCompositionExact` treats runtime as another observation coordinate. Route-dependent finite runtimes yield a timing split; constant public-fibre timing yields no timing split. Primary timing reference: Paul C. Kocher, *Timing Attacks on Implementations of Diffie-Hellman, RSA, DSS, and Other Systems*, CRYPTO 1996, DOI `10.1007/3-540-68697-5_9`.

## Representation geometry and physical leakage geometry

`RepresentationLeakageGeometryExact` gives a cautious finite duality. Two implementations can encode the same logical transition with identical state count but different Hamming movement: the binary middle transition moves two bits, the Gray version one. If a physical model observes Hamming movement, representation choice changes the observation surface.

This does **not** say smaller Hamming movement is automatically safer. It proves only that computational transition geometry and physical observation geometry are not independent design questions.

## Frontier after the geometry tranche

The generic architecture is no longer the main obstacle. The shortest substantive questions are now:

1. instantiate the actual FIPS CBD/NTT conditioned residual system strongly enough to measure conditional survivor counts, rather than only structural dependency;
2. determine whether any conditional/separator theorem survives the connected dataflow graph and genuinely lowers reconciliation cost;
3. compare candidate traversal/update geometry in coefficient, NTT, and any alternative representations under the same candidate verifier;
4. audit real protocol/implementation observations and require a same-public hidden-dependent split witness;
5. value observations by total protected-label recovery cost **and** by how they alter search/separator geometry;
6. move from finite weighted rates/guessing counts to explicit probabilistic min-entropy or game-advantage semantics only after the finite carrier is stable.

The working thesis is now:

`protected-label quotient + candidate fibre + search graph + representation embedding + observation refinement + algorithm-relative recovery cost`.

No GitHub Actions or CodeRabbit run is required by this tranche. `scripts/check_crypto_ntt_prior_observation_round17.sh` fail-closes the source surface and invokes the Round-17 aggregate when Agda is locally available. No kernel-clean claim is made without an observed typecheck.
