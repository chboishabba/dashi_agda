# Crypto Local-Constraint Search Geometry — Round 15

This tranche attacks the verification-to-search seam directly. It does not assert a break of any standardized primitive.

## Main theorem boundary

A global verifier can factor as local predicates plus a reconciliation relation. Local testability is therefore insufficient for independent global search. `SearchFactorisationExact` proves the constructive positive direction only when compatible local witnesses and an assembly map are supplied.

The cost audit separates two cases:

- generic Cartesian reconciliation: `T_L + T_R + n_L*n_R*T_C`;
- functional/direct reconciliation: `T_L + T_R + T_C`.

Thus the desired additive bound is not free: it requires an actual cheap reconciliation route.

## Transform / NTT-CRT boundary

`TransformLocalFibreGeometryExact` proves that an exact coordinate transform is injective and preserves distinctions. An invertible NTT/CRT-like representation change alone does not reduce candidate-state information. Search improvement needs extra verifier or coupling structure in transformed coordinates.

For ML-KEM, `MLKEMLocalSearchGeometryExact` requires an application-supplied same-object bridge from the concrete residual representation to local coordinates. No theorem asserts that the FIPS-203 NTT produces independently searchable local fibres.

Reference: NIST, *Module-Lattice-Based Key-Encapsulation Mechanism Standard*, FIPS 203 (2024), DOI `10.6028/NIST.FIPS.203`; Oded Regev, *On lattices, learning with errors, random linear codes, and cryptography* (STOC 2005), DOI `10.1145/1060590.1060603`.

## Coupling / separator geometry

`ConstraintCouplingSearchExact` proves disconnected local constraints compose directly and gives a connected Bool-equality example with an immediate witness, so connectedness alone has no hardness promotion. A proof-bearing bounded-separator certificate yields the explicit DP accounting formula `S*(L+R+C)`. A general treewidth theorem is intentionally not imported or asserted.

## Adaptive observation refinement

`AdaptiveFibreShrinkExact` converts an existing `ObservationSplitWitness` into a strict candidate refinement: the actual state survives while a distinct candidate is rejected. The finite Bool harness records an exact 2-to-1 candidate shrink.

`ThresholdPartitionGeometryExact` gives the complementary finite result: either single threshold bit is non-injective, but two independent lossy bits jointly reconstruct the entire two-bit state. This is a model of how repeated threshold/rounding observations can intersect without asserting that ML-KEM exposes such a predicate.

## Timing as an observation coordinate

`TimingObservationSideChannelExact` places runtime inside the same observation algebra. A `TimingSplit` consists of two hidden states with the same public projection and a query whose runtime differs; it refutes public-fibre-constant timing and induces an ordinary `ObservationSplitWitness`. Bucketed timing is represented separately so a coarse timer can still matter when buckets remain distinguishable.

Reference: Paul C. Kocher, *Timing Attacks on Implementations of Diffie-Hellman, RSA, DSS, and Other Systems*, CRYPTO 1996, DOI `10.1007/3-540-68697-5_9`.

Engineering provenance: Andres Freund's 2024 xz/liblzma investigation reported anomalous CPU/runtime behaviour around sshd as one clue leading into the compromised library path. This is not presented as a cryptographic theorem and no DOI is asserted for the oss-security report.

## Ten-candidate controls

`TopTenSearchGeometryControlsExact` keeps the earlier educational set of ten candidates and assigns a verification/search geometry rather than another generic security label:

1. OTP — affine reuse relation;
2. AES-GCM — authenticated partition;
3. ChaCha20-Poly1305 — authenticated partition;
4. RSA-OAEP — modular forward equation;
5. Diffie-Hellman — finite-group forward equation;
6. X25519 — elliptic scalar forward equation;
7. ElGamal — randomized re-encryption witness;
8. HPKE — component-local composition;
9. ML-KEM — noisy residual plus reconciliation;
10. QKD + symmetric follow-on — physical statistical partition.

Timing is orthogonal to primitive mathematics: attaching runtime to any candidate requires an actual split witness before it becomes evidence of leakage.

## Validation boundary

`scripts/check_crypto_local_constraint_search_round15.sh` fail-closes on holes/postulates/trust escapes, checks load-bearing theorem markers, cascades the newest available prior checker, and invokes the cumulative aggregate if Agda is locally available. No GitHub Actions or CodeRabbit run is required for this tranche, and no Agda kernel-clean claim is made without an observable typecheck.
