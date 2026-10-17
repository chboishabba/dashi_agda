# DA51 × repository intelligence × Aristotle × agda2lean max-cut

Date: 2026-10-17

This document fixes the repository-infrastructure cut after the unified DA51 ABI and the repository-intelligence consolidation.

## One product, distinct authorities

The product surface is `dashi-repo`, backed by the existing shared database:

```text
.dashi/repository.sqlite3
```

The proof router adds normalized DA51 and routing tables to that database. It does not create another registry file or JSON handoff.

```text
DA51 identity
  -> repository semantic discovery / dedupe / history
  -> fail-closed absence receipt
  -> proof-debt classification
  -> backend capability routing
       Agda preflight / Agda kernel
       agda2lean
       Aristotle + Lean
       Lean kernel
       evidence acquisition
  -> routing receipt
  -> independently checked evidence/provenance
```

Authority remains cut across owners:

- `dashi_lean4/DA51.Core` owns the formal DA51 wire ABI;
- `dashi-repo` owns repository discovery, dedupe, history and scheduling metadata;
- Agda preflight owns structural/native diagnostic observations at its declared evidence levels;
- `agda2lean` owns the translation capability represented by its proof-aware elaborated IR/catalog;
- Aristotle owns reasoning/reconstruction work assigned to it;
- Agda and Lean kernels own their own certification receipts;
- DA51 provenance/evidence edges do not inherit any of those authorities.

## Discover before prove

`dashi-repo prove route` always runs repository discovery before permitting proof generation.

Exact live owners and signature/body-equivalent owners route to `repository-reuse-review`.

Incomplete repository coverage routes to `repository-discovery` with generation disabled.

Only a complete, fail-closed no-candidate receipt permits a novel mathematical route to Aristotle.

Structural similarity and historical proximity remain useful search observations; neither proves theorem equivalence.

## Proof-debt partition

The runtime router mirrors the existing formal proof-debt separation:

```text
mathematical-debt
transcription-debt
certification-debt
empirical-evidence-debt
none
```

A source-established, source-aligned theorem with deferred proof is certification debt rather than automatically reopened mathematical debt. An experimentally supported deductive theorem remains mathematical debt. An empirical claim routes to evidence acquisition rather than theorem generation.

## agda2lean x-pollination

When a canonical Agda source declaration is supplied, the router reads the agda2lean semantic catalog at declaration granularity.

The existing agda2lean mapping modes are interpreted conservatively:

```text
exact / encoded
  -> agda2lean translation lane

reconstruct
  -> agda2lean + Aristotle/Lean reconstruction lane

quarantined / unsupported
  -> independent Aristotle/Lean formalisation lane
```

An agda2lean mapping mode is a translation capability. It does not establish a Lean theorem. The emitted Lean artifact still requires independent Lean validation.

## DA51 infrastructure

The router accepts an optional DA51 address as the stable cross-system join key.

New normalized tables:

```text
da51_objects
  address, type_code, data_hex, canonical_owner, authority

da51_symbol_links
  address, symbol_id, relation, source

da51_evidence
  address, producer, artifact, evidence_kind, revision, digest, authority

proof_routes
  query/status/debt/backend/absence/DA51/agda2lean capability

proof_route_matches
  exact/equivalent/similar/historical candidate rows
```

DA51 type-8 atlas fields are validated strictly, including zero reserved bits and known level/biome/status codes. The status nibble is returned as wire metadata only.

The following implications are forbidden:

```text
DA51 status=1 != proof term
DA51 evidence != theorem authority
agda2lean exact != Lean kernel receipt
preflight prediction != Agda theorem
similar symbol != same theorem
development narrative != formal truth
routing receipt != proof
```

## CLI

```sh
# Resolve the cross-system identity.
dashi-repo da51 resolve 0xDA51853000A00000

# Attach an indexed theorem/trace/artifact relation.
dashi-repo da51 link 0xDA51853000A00000 DASHI.Some.symbol \
  --relation statement --source dashi_agda

# Attach producer evidence without authority escalation.
dashi-repo da51 add-evidence 0xDA51853000A00000 \
  --producer zkperf --kind benchmark --artifact sha256:...

# Discover before proving.
dashi-repo prove discover "square root cancellation"

# Route a genuinely novel goal only after repository coverage can certify absence.
dashi-repo prove route "square root cancellation" --target-prover lean \
  --da51 0xDA51853000A00000

# Route a source-established Agda declaration using agda2lean capability.
dashi-repo prove route "source theorem" --target-prover lean \
  --mathematical-status source-established \
  --statement-status source-aligned \
  --certification-status proof-deferred \
  --source-declaration DASHI.Example.sourceTheorem \
  --semantic-catalog build/catalog.sqlite

# Inspect accumulated routing debt for an object.
dashi-repo da51 frontier 0xDA51853000A00000
```

## MCP / agent use

`dashi-repo-mcp` adds read-oriented agent surfaces:

```text
proof_route
proof_route_history
da51_resolve
da51_evidence
da51_frontier
```

These sit beside the existing symbol/discovery/history/lineage and Agda diagnostic tools. Aristotle or another agent can therefore receive a bounded route receipt before generating a proof candidate.

## Operational loop

```text
object / goal
 -> resolve DA51 if known
 -> exact/equivalent/similar/history discovery
 -> reuse if already owned
 -> otherwise require complete absence receipt
 -> classify debt
 -> inspect agda2lean capability if Agda source exists
 -> choose the least-authority backend
 -> run preflight/compiler feedback as observations
 -> Aristotle refinement/reconstruction only where actually needed
 -> independent kernel certification
 -> persist evidence/provenance
 -> selectively reopen only affected consumers
```

This is the infrastructure use of DA51: stable identity and provenance across independently governed proof/search/tooling systems, not a mechanism for transferring truth authority between them.
