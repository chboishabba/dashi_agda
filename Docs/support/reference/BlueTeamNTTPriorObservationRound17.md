# Blue-Team NTT Prior / Observation Cost — Round 17

This tranche continues both remaining defensive crypto programmes simultaneously:

1. determine whether the MLWE/ML-KEM search problem becomes genuinely simpler in transformed coordinates;
2. determine whether a protocol or implementation exposes a hidden-dependent observation that changes protected-label recovery cost.

It does not claim an ML-KEM break or security proof.

## FIPS NTT dataflow

`MLKEMNTTDataflowCouplingExact` follows NIST FIPS 203 Algorithm 9 and equations (4.10)–(4.13).

Algorithm 9 has seven butterfly stages with lengths

`128, 64, 32, 16, 8, 4, 2`.

The dependency width therefore doubles seven times from one source coefficient to 128 source coefficients for one scalar NTT residue component.

Reduction modulo a quadratic factor sends the 128 even source coefficients into the constant component and the 128 odd source coefficients into the linear component. Thus one quadratic residue pair structurally spans all 256 source coefficients of a polynomial.

For K-PKE module dimension `k`, one public scalar NTT coordinate structurally spans `128*k` source secret coefficients and one quadratic pair spans `256*k`. The exact approved counts are therefore:

- ML-KEM-512: scalar 256, quadratic pair 512;
- ML-KEM-768: scalar 384, quadratic pair 768;
- ML-KEM-1024: scalar 512, quadratic pair 1024.

These are structural/dataflow widths, not claims of statistical dependence or hardness.

Primary source: National Institute of Standards and Technology, *Module-Lattice-Based Key-Encapsulation Mechanism Standard*, FIPS 203 (2024), DOI `10.6028/NIST.FIPS.203`.

## No disconnected parity cut

`MLKEMNTTPriorCutNoGoExact` turns the shared-source structure into a finite separator statement over the exact 128-index carrier. Every two constant-part coordinates share an even source variable and every two linear-part coordinates share an odd source variable. Therefore neither parity family admits a nontrivial source-variable-disjoint cut with both sides inhabited.

This rules out the strongest possible local-search story — disconnected independent scalar lanes — at the structural dependency level. It does not rule out a useful bounded separator under stronger conditional structure.

## Positive two-block prior factorisation, followed by verifier recoupling

`MLKEMNTTParityBlockPriorExact` records the positive side.

If the source prior is a coefficient-product prior, the even and odd source coefficient families give a natural two-block prior transport. Their exact source block sizes are:

- 256 + 256 for ML-KEM-512;
- 384 + 384 for ML-KEM-768;
- 512 + 512 for ML-KEM-1024.

However, FIPS 203 BaseCaseMultiply immediately couples the two local components:

`c0 = a0*b0 + a1*b1*gamma`

`c1 = a0*b1 + a1*b0`.

Hence a two-block prior factorisation does not produce two independent public-verifier problems, and certainly does not produce 128 independent secret-search lanes.

## Combined prior/verifier graph connectivity

`MLKEMNTTCombinedCouplingConnectivityExact` composes the two observations above into a stronger structural theorem.

- same-component NTT scalar coordinates are connected directly through shared source variables;
- constant and linear coordinates at one residue are connected by the BaseCase verifier coupling.

Therefore **every two scalar NTT nodes are connected by a path of length at most two**. The module proves that the combined structural coupling graph has no nontrivial disconnected cut.

This is stronger than merely saying the NTT is invertible. It rules out a decomposition into disconnected independent scalar search components at this dataflow level. It still does **not** establish statistical dependence, treewidth growth, or MLWE hardness.

## Conditional reconciliation remains the positive search seam

The connectivity theorem deliberately does not end the search programme.

`ConditionalReconciliationSearchExact` formalises the important remaining possibility: after fixing one local block, a compatible mate in the other block may be constructible directly. A proof-bearing `LeftConditionedMate` turns one valid outer candidate into reconciled local witnesses; together with an assembly map, `leftCandidateGivesGlobal` constructs a genuine global witness.

The corresponding cost distinction is exact:

- conditional mate route: `n_outer * T_cond`;
- Cartesian pair route: `n_left * n_right * T_pair`.

The finite regression records `3*4 = 12` units for conditional reconstruction versus `3*5*2 = 30` units for Cartesian reconciliation.

So the highest-alpha NTT question has become very specific: **does the actual transported CBD prior plus the public FIPS equations admit a low-cost conditional mate/separator theorem despite the connected dataflow graph?**

## Observation acquisition cost

`ObservationAcquisitionCostExact` strengthens the existing algorithm-relative candidate-shrink accounting.

The complete comparison is now:

`recovery-before`

versus

`observation-acquisition-cost + recovery-after`.

On the finite 2x2 MLWE regression, the pre-observation recovery architecture costs 13 and the post-observation architecture costs 8.

- acquisition cost 2 gives total 10 and a net gain of 3;
- acquisition cost 6 gives total 14 and is net harmful by 1.

Thus strict candidate-fibre shrinkage is not enough. A useful observation must reduce total protected-label recovery work after paying for its acquisition.

## Key confirmation as a conditional observation surface

`KeyConfirmationObservationRefinementExact` uses the state-contract distinction recommended by NIST SP 800-227.

A visible confirmation outcome becomes security-relevant only when a constructive witness shows two same-public hidden states produce different outcomes for one presented tag. The finite Bool harness supplies such a 2-to-1 regression.

Primary reference: Gorjan Alagic, Elaine Barker, Lily Chen, Dustin Moody, Angela Robinson, Hamilton Silberg, Noah Waller, *Recommendations for Key-Encapsulation Mechanisms*, NIST SP 800-227 (2025), DOI `10.6028/NIST.SP.800-227`.

The theorem does not say key confirmation is unsafe. It says externally visible confirmation behaviour belongs in the adversary observation function and must be checked for same-public-fibre splits.

## ML-KEM implicit rejection

`MLKEMImplicitRejectProtocolObservationExact` separates internal route state from external observability.

FIPS 203 Algorithm 18 computes the re-encryption comparison and uses the fallback `J(z || c)` on mismatch. The internal route can differ while an external observation remains constant; the module proves that this public-factored opaque surface cannot yield an observable split. A second finite surface shows that directly exporting the route would create a hidden-dependent split.

This matches the source boundary: FIPS 203 explicitly requires the comparison flag to remain secret intermediate data and forbids returning it. Any downstream accept/retry/timing/confirmation distinction requires its own observation split witness.

## Timing composition

`MLKEMImplicitRejectTimingCompositionExact` puts implementation runtime into the same observation algebra.

A finite regression assigns different runtimes to the two internal routes and obtains an ordinary hidden-dependent timing split. A second constant-runtime regression proves that if timing is constant on each public fibre, no timing split exists even though the internal route itself may differ.

Primary timing reference: Paul C. Kocher, *Timing Attacks on Implementations of Diffie-Hellman, RSA, DSS, and Other Systems*, CRYPTO 1996, DOI `10.1007/3-540-68697-5_9`.

Again, neither regression claims an actual ML-KEM timing leak. The concrete defensive obligation is to measure or prove the real implementation surface.

## Composed finite MLWE confirmation regression

`FiniteMLWEConfirmationObservationExact` binds the confirmation abstraction back to the existing public collision in the finite MLWE lab.

The two hidden states producing public `(2,2)` have opposite first-secret-bit labels. A visible confirmation outcome for one presented tag separates them. Under the declared recovery architecture:

- query cost 2: net recovery gain 3;
- query cost 6: net harmful by 1.

This is the first exact regression in the branch where a protocol-visible split, finite candidate shrink, and observation acquisition cost are all composed in one theorem surface.

## Frontier after Round 17

The generic architecture is no longer the main obstacle. The next mathematical questions are concrete:

1. instantiate the actual FIPS NTT/CBD prior rather than another abstract transform and determine whether any useful *conditional* separator survives the connected dataflow graph;
2. quantify conditional mate/reconciliation work on actual public ML-KEM equations rather than counting NTT multiplication lanes;
3. audit real protocol/implementation observations and require a same-public hidden-dependent split witness;
4. recompute total recovery cost including acquisition/query cost before calling any observation useful.

No GitHub Actions or CodeRabbit run is required by this tranche. `scripts/check_crypto_ntt_prior_observation_round17.sh` fail-closes the source surface and invokes the Round-17 aggregate when Agda is locally available. No kernel-clean claim is made without an observed typecheck.
