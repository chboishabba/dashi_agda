# Blue-Team NTT Prior / Observation / Search Geometry — Round 17

Round 17 is now at a natural research boundary. The defensive chain is source-facing and explicit:

`FIPS/CBD structure -> finite raw observation fibres -> representation/update geometry -> sufficient-state/readout and average-success resource bounds -> admitted physical observation channel`.

No ML-KEM break, generic runtime lower bound, or implementation leakage claim is made.

## Source and defensive threat-model provenance

Primary cryptographic source:

- National Institute of Standards and Technology, *Module-Lattice-Based Key-Encapsulation Mechanism Standard*, FIPS 203 (2024), DOI `10.6028/NIST.FIPS.203`.

Finite-field uncertainty source:

- Martino Borello and Patrick Solé, *The uncertainty principle over finite fields*, *Discrete Mathematics* 345 (2022) 112670, DOI `10.1016/j.disc.2021.112670`.

Defensive side-channel / partial-information context, never imported as theorem premises:

- Mike Hamburg, Julius Hermelink, Robert Primas, Simona Samardjiska, Thomas Schamberger, Silvan Streit, Emanuele Strieder and Christine van Vredendaal, *Chosen Ciphertext k-Trace Attacks on Masked CCA2 Secure Kyber*, IACR TCHES 2021(4), 88–113, DOI `10.46586/tches.v2021.i4.88-113`.
- Estuardo Alpirez Bock, Gustavo Banegas, Chris Brzuska, Łukasz Chmielewski, Kirthivaasan Puniamurthy and Milan Šorf, *Breaking DPA-Protected Kyber via the Pair-Pointwise Multiplication*, ACNS 2024, LNCS 14584, 101–130, DOI `10.1007/978-3-031-54773-7_5`.
- Yen-Ting Kuo and Atsushi Takayasu, *A Lattice Attack on CRYSTALS-Kyber with Correlation Power Analysis*, ICISC 2023, 202–220, DOI `10.1007/978-981-97-1235-9_11`; earlier version IACR ePrint 2023/1781.
- Zehua Qiao, Yuejun Liu, Yongbin Zhou, Mingyao Shao and Shuo Sun, *When NTT Meets SIS: Efficient Side-channel Attacks on Dilithium and Kyber*, IACR ePrint 2023/1866. No DOI is assigned in the ePrint record.
- Pierre-Alain Fouque, Damien Marion, Quyen Nguyen and Alexandre Wallet, *Avengers assemble! Supervised learning meets lattice reduction: A single power trace attack against CRYSTALS-Kyber Key Generation*, IACR TCHES 2025(4), 409–436, DOI `10.46586/tches.v2025.i4.409-436`.
- Guilhem Assael, Philippe Elbaz-Vincent and Guillaume Reymond, *Improving Single-Trace Attacks on the Number-Theoretic Transform for Cortex-M4*, IEEE HOST 2023, DOI `10.1109/HOST55118.2023.10133270`.
- Tianrun Yu, Chi Cheng, Zilong Yang, Yingchen Wang, Yanbin Pan and Jian Weng, *Hints from Hertz: Dynamic Frequency Scaling Side-Channel Analysis of Number Theoretic Transform in Lattice-Based KEMs*, IACR TCHES 2024(3), 200–223, DOI `10.46586/tches.v2024.i3.200-223`.

The generic Euler-criterion bridge additionally records Leonhard Euler's historical source, *Theoremata circa divisores numerorum in hac forma paa ± qbb contentorum*, Novi Commentarii Academiae Scientiarum Petropolitanae 14 (1770), 151–181; no DOI is assigned.

## Complete m=8 raw leakage-resolution profile

`MLKEMNTTActualCBD2EightCoefficientLeakageResolutionExact` records the complete `5^8 = 390625` raw-signature profiles pinned by `scripts/crypto_ntt_cbd_block_reconciliation_probe.py`:

| residues | candidates | images | collision pairs | conditional mass | mean list | max fibre |
|---|---:|---:|---:|---:|---:|---:|
| `(0,1)` | 390625 | 271441 | 151632 | 693889 | ≈1.77636 | 4 |
| `(0,2)` | 390625 | 369865 | 20805 | 432235 | ≈1.10652 | 3 |
| `(0,3)` | 390625 | 390625 | 0 | 390625 | 1 | 1 |

The module kernel-checks the mass identity `conditionalMass = candidates + 2*collisionPairs`, but deliberately does not treat the large Python enumeration as a semantic Agda injectivity proof.

The blue-team meaning is narrow: `(0,3)` is a high-resolution **raw** joint observation on this conditioned carrier. That makes it a priority surface to audit if a real implementation channel preserves those distinctions; it does not show that a real trace exposes the raw pair.

## Compact pair-(0,3) proof route — no 390625-case Agda proof

The finishing tranche found a much smaller mathematical certificate.

For two CBD2 candidates, each difference coordinate lies in `[-4,4]`. With the actual FIPS evaluation points

`a = gamma_0 = 17`, `b = gamma_3 = 568`,

`MLKEMFIPS203F3329ArithmeticExact` computes

`17^4 = 568^4 = 296 (mod 3329)`.

Therefore coordinates `j` and `j+4` compress to

`e_j = d_j + 296*d_(j+4)`, for `j=0,1,2,3`.

The compressed coefficient support has only `9*9 = 81` residues. The raw two-root condition becomes a cubic

`E(X) = e0 + e1*X + e2*X^2 + e3*X^3`

with roots 17 and 568.

`MLKEMNTTPair03CubicRootFactorReductionExact` proves generically over a commutative ring that, whenever multiplication by `b-a` reflects zero, two roots force the quadratic-factor relations. For the FIPS constants,

`17+568 = 585`, `17*568 = 2998 = -331 mod 3329`,

so with `p=e2+585*e3`, any kernel point must satisfy

`e0 = -331*p`,

`e1 = -585*p - 331*e3`.

`MLKEMNTTPair03ReducedKernelCertificateExact` then checks only `81^2 = 6561` reduced states. It proves every reduced survivor is zero and separately proves compressed residue zero has the unique digit pair `(0,0)`. Its theorem `compactPair03BoundedKernelOnlyZero` turns the two reduced coefficient equations into zero for all eight bounded differences.

The independent discovery producer `scripts/crypto_ntt_pair03_compact_injectivity_certificate.py` reports the same shape: 161 reduced pairs survive the first membership condition and exactly one survives both — zero.

This is the intended replacement for a 390625-case kernel enumeration.

### Remaining pair-(0,3) bridge

The compact algebra and bounded finite kernel are now present. One same-object leaf remains before claiming a full semantic Agda theorem for the actual raw map: instantiate the generic cubic theorem on a canonical `F_3329` field carrier and derive the two reduced coefficient equations directly from equality of the actual pair-(0,3) signatures.

Until that field bridge is checked, the large collision-free profile remains a pinned exhaustive computation and the compact route remains a proof decomposition rather than a completed end-to-end kernel theorem.

## F_3329 arithmetic and gamma nonsquare orbit

`MLKEMFIPS203F3329ArithmeticExact` now closes the concrete residue arithmetic needed by both the pair-(0,3) proof and the local-invertibility lane. Among the closed computations are

- `17^4 = 568^4 = 296 mod 3329`;
- `568-17 = 551` and `551*3184 = 1 mod 3329`;
- `2*1665 = 1 mod 3329`;
- `17^128 = -1`, `17^256 = 1`, and `17^1664 = -1 mod 3329`.

`MLKEMFermatNonsquareBridgeExact` proves the generic Euler/Fermat implication: if every nonzero `x` obeys `x^(2h)=1`, while `zeta^h=-1 != 1`, then `zeta` is not a square. It also proves `(x*x)^h = x^(h+h)` internally.

Combined with `MLKEMFIPS203GammaNonsquareTransportExact`, this means the old conceptual obligation “prove 128 unrelated gamma nonsquare facts” has collapsed to one standard prime-field leaf: realize the canonical `F_3329` carrier, supply Fermat's `x^3328=1` for nonzero `x`, identify the computed residue `3328` with `-1`, and instantiate `zeta=17`. The square-orbit transport then covers all FIPS quadratic constants.

## Observation coarsening is now an exact theorem boundary

`MLKEMNTTActualCBD2EightCoefficientLeakageResolutionExact` now defines

`ObservationReflectsRawOnSecretImage`:

observed equality must imply raw-signature equality **on the actual secret image**.

Raw injectivity plus this reflection property implies coarsened-observation injectivity. A separate collision-witness theorem proves how a coarsening can destroy raw resolution, and the existing finite constant-channel example demonstrates that raw injectivity alone says nothing about a physical side channel.

This is the correct target for future Hamming-weight/distance, timing, masked-share, frequency, cache or other implementation-specific observations. Global injectivity of the physical observation outside the reachable raw-image set is unnecessary.

## Structural/update/resource chain retained

The earlier Round-17 chain remains intact:

- `MLKEMNTTDataflowCouplingExact`, `MLKEMCandidateMoveFanoutExact`, `MLKEMLocalityAreaInvariantExact` and `MLKEMButterflyStageLocalityInvariantExact` expose the FIPS NTT dependency/locality geometry.
- `MLKEMNTTSingularBudgetUncertaintyExact` gives the conditional support law `128 <= sourceSupport*(survivingSupport+singularBudget)` from finite-field uncertainty plus the local singularity producer.
- `MLKEMExactResidualTouchLowerBoundExact` and `MLKEMResidualTouchPathLowerBoundExact` turn that into an exact materialised-residual touch resource, without relabelling support as generic runtime.
- `MLKEMFiniteStateTranscriptCapacityExact`, `MLKEMBoundedCellTranscriptCapacityExact`, `MLKEMFIPS203ProtectedSecretCapacityExact` and `MLKEMFIPS203UpdateCapacityResourceExact` give the independent sufficient-state/readout capacity side.
- `MLKEMFIPS203CBDPriorSuccessBoundExact` and `MLKEMFIPS203AverageSuccessResourceExact` replace support-cardinality-only reasoning with an average-success numerator bound under the explicitly stated independent uniform `SamplePolyCBD` input-bit product model.
- `ProtectedLabelSearchGeometryExact`, Gray/mixed-radix traversal, observation acquisition, language refinement and representation minimax remain separate coordinates; candidate shrink, raw injectivity, physical leakage, search cost and total runtime are not identified.

## Stopping criterion / remaining highest-alpha work

The abstract lane is now narrow enough that further generic scaffolding would have low value. The remaining high-alpha leaves are:

1. **Canonical `F_3329` field bridge for pair `(0,3)`.** Turn actual raw-signature equality into the already-proved cubic/reduced equations, using the concrete inverse of `568-17`.
2. **Canonical `F_3329` Fermat/Euler instance.** Supply the prime-field Fermat law and instantiate the generic nonsquare bridge for `17`; square-orbit transport then closes all 128 gamma nonsquare obligations.
3. **Actual implementation coarsening.** Only with real implementation semantics, code or traces should we instantiate Hamming/timing/masking/frequency observation maps and ask whether they satisfy or violate `ObservationReflectsRawOnSecretImage`.
4. **Optional deep theorem:** internalize the full 128-point finite-field Fourier uncertainty theorem for the actual FIPS transform `T_FIPS = P_bitrev F_omega D_17`. This is mathematically worthwhile but lower defensive ROI than the three same-object leaves above.

After (1) and (2), there is little value in growing the abstract ML-KEM lane without new implementation evidence or a genuinely new theorem idea.

No GitHub Actions/CI or CodeRabbit run is required. `scripts/check_crypto_ntt_prior_observation_round17.sh` remains fail-closed and runs the compact Python certificate plus the existing finite regressions when Python is available; it invokes Agda only when an executable is locally available. No kernel-clean claim is made without an observed typecheck.
