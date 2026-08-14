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

`MLKEMNTTPriorCutNoGoExact` turns the shared-source structure into a finite separator statement. Every two constant-part coordinates share an even source variable and every two linear-part coordinates share an odd source variable. Therefore neither parity family admits a nontrivial source-variable-disjoint cut with both sides inhabited.

This rules out the strongest possible local-search story — disconnected independent scalar lanes — at the structural dependency level. It does not rule out a useful bounded separator under stronger conditional structure.

## Positive two-block prior factorisation, followed by verifier recoupling

`MLKEMNTTParityBlockPriorExact` also records the positive side.

If the source prior is a coefficient-product prior, the even and odd source coefficient families give a natural two-block prior transport. Their exact source block sizes are:

- 256 + 256 for ML-KEM-512;
- 384 + 384 for ML-KEM-768;
- 512 + 512 for ML-KEM-1024.

However, FIPS 203 BaseCaseMultiply immediately couples the two local components:

`c0 = a0*b0 + a1*b1*gamma`

`c1 = a0*b1 + a1*b0`.

Hence a two-block prior factorisation does not produce two independent public-verifier problems, and certainly does not produce 128 independent secret-search lanes.

The new search frontier is therefore a genuine reconciliation problem: prove a conditional/separator structure that is cheaper than generic recombination.

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

FIPS 203 Algorithm 18 computes the re-encryption comparison and uses the fallback `J(z || c)` on mismatch. The internal route can differ while an external observation remains constant. A second finite surface shows that directly exporting the route would create a hidden-dependent split.

This matches the source boundary: FIPS 203 explicitly requires the comparison flag to remain secret intermediate data and forbids returning it. Any downstream accept/retry/timing/confirmation distinction requires its own observation split witness.

## Composed finite MLWE confirmation regression

`FiniteMLWEConfirmationObservationExact` binds the confirmation abstraction back to the existing public collision in the finite MLWE lab.

The two hidden states producing public `(2,2)` have opposite first-secret-bit labels. A visible confirmation outcome for one presented tag separates them. Under the declared recovery architecture:

- query cost 2: net recovery gain 3;
- query cost 6: net harmful by 1.

This is the first exact regression in the branch where a protocol-visible split, finite candidate shrink, and observation acquisition cost are all composed in one theorem surface.

## Frontier after Round 17

The generic architecture is no longer the main obstacle. The next mathematical questions are concrete:

1. determine whether the actual transported CBD prior or residual score admits a useful *conditional* decomposition smaller than the two large parity components exposed here;
2. quantify the separator/reconciliation cost of such a decomposition rather than counting NTT multiplication lanes;
3. audit real protocol/implementation observations and require a same-public hidden-dependent split witness;
4. recompute total recovery cost including acquisition/query cost before calling any observation useful.

No GitHub Actions or CodeRabbit run is required by this tranche. `scripts/check_crypto_ntt_prior_observation_round17.sh` fail-closes the source surface and invokes the Round-17 aggregate when Agda is locally available. No kernel-clean claim is made without an observed typecheck.
