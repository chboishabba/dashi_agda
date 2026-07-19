# Verified FRACTRAN Crank Pipeline

## Purpose

This tranche separates two problems that had previously been conflated:

1. **translation:** deterministically compile declared machine or formal semantics into a FRACTRAN transition system;
2. **search:** generate many semantically equivalent candidates and select a preferred verified representative.

The implementation authority surface is:

- `DASHI/Interop/VerifiedFractranCrankPipeline.agda`

## Pipeline

```text
source program / binary / theorem artifact
  -> declared transition semantics
  -> architecture lowering to typed micro-operations
  -> semantics-preserving FRACTRAN compilation
  -> candidate population
  -> GA / artificial-life / annealing / LLM proposals
  -> compiler simulation + proof-checker + replay validation
  -> MDL / corpus-relative post-entropy accounting
  -> bounded no-cheaper-equivalent certificate
  -> CID / trace / proof identities
  -> ZK statement and witness relation
```

## Trusted and untrusted lanes

The proposal engines are deliberately outside the trusted kernel. Genetic algorithms, artificial life, simulated annealing, humans, and LLMs may all produce candidates. None of them establish correctness.

A candidate becomes a `VerifiedCrank` only when all three gates are witnessed:

- compiler witness present;
- proof checker accepted;
- receipt replay accepted.

## Translation contract

`CompilerSimulation` records:

- an encoder from source states to target states;
- a partial decoder;
- initialization correctness;
- forward simulation;
- backward simulation at declared instruction boundaries.

`MicroOpToFractran` factors cross-architecture translation through a small typed micro-operation language. This avoids treating raw x86, ARM, GPU, or VM instruction names as the universal semantic substrate.

`FractranMachine` represents each fraction by numerator and denominator exponent vectors and records the guarded update law

```text
exponent(apply f s, lane) + denominator(f, lane)
  = exponent(s, lane) + numerator(f, lane).
```

## Post-entropy and selection

`PostEntropyScore` is corpus-relative accounting. It separates model, residual, proof, and decoder deltas and requires their additive relation to the new corpus description length.

`CandidateOrdering` is lexicographic rather than an arbitrary weighted score:

1. verified before rejected;
2. stronger equivalence scope before compression;
3. lower MDL at equal scope;
4. lower physical cost only as a tie-break.

This prevents a tiny incorrect candidate or a narrow test-only candidate from defeating a broader proved implementation.

## What “every CPU cycle is necessary” may mean

The repository does **not** promote global or metaphysical cycle necessity. General program equivalence and unrestricted global minimization are not claimed.

`BoundedSearchCertificate` supports the precise statement:

> No cheaper equivalent candidate exists inside the declared search space.

The search boundary, equivalence relation, and cost ordering must therefore be included in every receipt.

## ZK/DASL/JMD interoperability

`ArtifactIdentity` binds CIDs/hashes for payload, toolchain, trace, and proof. `ZKCrankStatement`, `ZKCrankWitness`, and `ZKCrankRelation` provide the formal surface for proving that:

- the public source CID matches the private verified candidate’s source artifact;
- the public candidate CID matches the candidate artifact;
- the trace commitment matches the candidate receipt;
- cost and equivalence claims may be proved without exposing the full private witness.

DASL/MASL/CAR/DAG-CBOR remain transport and provenance formats. DASHI supplies typed semantics, admissibility, proof boundaries, MDL/post-entropy selection, and promotion governance.

## Honest boundary

The canonical boundary records:

- arbitrary binary-to-FRACTRAN translation is **not** implemented by this module;
- global program minimality is **not** proved;
- literal cycle necessity is **not** proved;
- bounded-search minimality is supported;
- the LLM is proposal-only.

The next executable tranche is an architecture-specific lowering plus a concrete FRACTRAN machine instance and translation-validation tests.