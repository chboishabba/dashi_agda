# Lean world: fibre-bounded exact intake (2026-11-09)

## Original goal and boundary

The first priority remains building **one source-pinned, queryable world** from accumulated Lean repositories. This module is a P0 indexing primitive, **not** a substitute for real Lean elaboration or kernel receipts. Translators and Lean↔Agda round trips are optional downstream tools.

## Existing foundations reused

- `DASHI/Core/ProjectionFibre.agda`: sharing a projected observable does not license identification of distinct hidden carriers.
- `DASHI/Core/FibreRestrictionCore.agda`: restricting a fibre is not recovery of its carrier or promotion of truth.
- This tranche applies those boundaries to retrieval: type-head/universe/foundation profiles select an indexing fibre without proving semantic equality.

## Implemented in this PR

- `scripts/lean_world_fibre_index.py`: stable origin identity (repository, revision, declaration); explicit proof-term digests and attribution; exact bytes equality after SHA-256 grouping; source occurrence retention; deterministic per-fibre bounded search; non-silent truncation accounting; fail-closed origin conflicts; idempotent imports.
- `tests/test_lean_world_fibre_index.py`: standalone regression tests, including conservative negative controls.

**Warning:** canonical_type bytes and projection fields must come from a source-pinned *elaborated Lean* exporter. The index does not establish that an exporter is sound or that its representation is canonical. Hashing does not replace byte comparison or kernel checks. A compatible profile string is necessary but may not be sufficient for semantic comparability.

Run tests locally without CI:
```sh
python3 -m unittest discover -s tests -p 'test_lean_world_fibre_index.py' -v
```

## Exact unpaid maximum cut

| Gate | Obligation | Acceptance |
| --- | --- | --- |
| W01 | Original corpus/source pinning | Complete revision IDs, licenses, provenance and acquisition receipts |
| W02 | Lean elaborated export admission | Real declaration types, term bytes and dependency references under pinned Lean profile |
| W03 | `canonicalTermIdentitySound` | Exporter representation is faithful to the intended kernel term identity in the specified fragment |
| W04 | `worldExactDedupeIdempotent` | Reimports preserve exactly the source-occurrence set |
| W05 | `worldAttributionSurvivesQuotient` | Statement quotient retains all proof/source occurrences |
| W06 | `fibreCandidateEnumerationBounded` | Bounded output and exact omitted-count reporting |
| W07 | `fibreBlockingCompleteForExactMatches` | Exact canonical types necessarily land in same indexed fibre under validated exporter contract |
| W08 | `fibreBlockingRecallCharacterised` | State scope and false-negative controls for non-identical semantic relationships |
| W09 | Real hyperfabric materialisation | Preserve original world/edge stalks and commuting restriction maps, without fabrication |
| W10 | AO integration | Rank genuine original unpaid obligations against actual imported Lean candidates |
| K01 | Proof payment | Lean kernel-check actual implication; original Agda consumer checked independently where required |
| K02 | Semantic quotient | Merge only checker-certified equivalence edges; never merge one-way implication |
| I01 | Incremental invalidation | Reverse dependency closure with stable unchanged receipts |

### Complexity policy

Never instantiate all theorem pairs by default. Exact bucket lookup is hash-indexed, and a chosen fibre's candidate retrieval returns at most budget occurrences. This bounds *retrieval output*, not source ingestion, proof-search time, total index memory, or global semantic matching cost. Do not interpret a budget-truncated search as exhaustive.

### Attribution rule

Retain donor repo, pinned revision, original declaration, theorem/proof fingerprints, authorship, licenses and independent proof lineage. No transfer of unpublished DASHI material to outside repositories without separate authorization.
