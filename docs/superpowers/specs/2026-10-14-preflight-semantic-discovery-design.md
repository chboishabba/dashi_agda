# Preflight Semantic Discovery and Round Lineage Design

Date: 2026-10-14
Status: proposed implementation spec
Branch: `feat/preflight-semantic-discovery`

## Purpose

The repository is now large enough that filename/text search routinely produces two bad outcomes: agents incorrectly report that an object does not exist, or they find only one partial/obsolete fragment and treat it as the whole object. Numbered `RoundNNN` snapshot families amplify this by flooding search results with near-equivalent historical states.

This design makes the existing `tools/agda_preflight` persistent SQLite index the canonical discovery substrate. It adds first-class symbol discovery, exact/equivalent/similar declaration lookup, live-vs-historical surface classification, absence-confidence receipts, and read-only round-lineage analysis. It does not replace Agda and does not claim semantic proof equivalence beyond the structural evidence it computes.

## Scope of the first implementation tranche

The first tranche ships **M1 Discovery plus read-only Round lineage analysis**. It must be useful without moving or rewriting any theorem module.

In scope:

1. exact qualified/unqualified symbol search;
2. exported/re-exported symbol visibility where recoverable from existing interfaces;
3. declaration fingerprints for exact body, normalized signature, and structural similarity candidates;
4. live/historical surface-role classification, with conservative defaults;
5. `related` search that stratifies results as exact, signature-equivalent, structurally-similar, or historical;
6. discovery receipts that prevent unjustified absence claims;
7. RoundNNN family detection and consecutive-round novelty/noise reports;
8. CLI, service, MCP, tests, README documentation;
9. persistent SQLite schema migration from v5 while preserving existing caches when safe.

Deferred:

- physical relocation or deletion of historical RoundNNN modules;
- automatic theorem-owner migration;
- semantic theorem equivalence or general dependent unification;
- vector/LLM embeddings;
- automatic object-family ontology curation;
- hard CI failure for duplicate/similar declarations.

## Design principles

### One index, not a parallel database

All discovery data is derived into the existing `source-index.sqlite3`. The current module/import/API cache remains authoritative for source freshness and dependency structure. New tables are rebuildable derived indexes.

### Evidence levels are explicit

The tool must never blur structural similarity into semantic equality. Results use distinct classes:

- `exact_name`: qualified or unqualified symbol match;
- `exact_body`: normalized implementation/body fingerprint match;
- `signature_equivalent`: normalized telescope/type-shape fingerprint match;
- `structurally_similar`: ranked heuristic candidate only;
- `historical`: a match on a surface classified as historical/superseded.

The CLI/API includes the evidence class and score/rationale for every non-name match.

### Absence is a receipt, not a grep result

A query may only return `absence_claim_permitted=true` when the indexed search completed across the enabled canonical/current/adapter surfaces and found no exact, equivalent, or materially similar candidate above the configured threshold. Historical-only and partial/similar matches make absence unpermitted.

### Historical provenance is preserved but de-prioritized

RoundNNN and other historical snapshots remain queryable. Ordinary discovery ranks live/current/canonical modules first and places historical matches in a separate section. No source module is deleted in this tranche.

## Architecture

### 1. Declaration catalogue

Add a declaration-level derived index populated from the existing parsed interface/summary information and, when needed, the same tree-sitter parse already used by preflight.

Proposed persistent fields:

- module path and module name;
- local and qualified declaration name;
- declaration kind;
- exported/public visibility;
- source span when available;
- normalized signature text/hash;
- normalized body/definition hash when structurally available;
- compact structural-feature payload for similarity ranking;
- surface role;
- round family and round number when detected.

The initial implementation should favor simple normalized strings/hashes and deterministic feature sets over a new parser or external dependency.

### 2. Surface-role classifier

Roles:

- `canonical`
- `current`
- `adapter`
- `validation`
- `receipt`
- `candidate`
- `historical_snapshot`
- `superseded`
- `unknown`

The first classifier is conservative and deterministic. `Round[0-9]+` basename/module segments classify as `historical_snapshot` unless explicitly overridden. Existing obvious `Validation`/`Receipt` naming may be classified, but ambiguous modules stay `unknown` rather than being guessed canonical.

Search defaults include `canonical`, `current`, `adapter`, and `unknown`; historical snapshots are returned separately rather than silently excluded.

### 3. Fingerprints

Implement three independent structural fingerprints:

- **body fingerprint**: normalized declaration body/clauses where available; local binder names and insignificant formatting are normalized conservatively;
- **signature fingerprint**: normalized declaration telescope/type representation;
- **feature fingerprint**: declaration kind, arity/telescope shape, head constructors/operators, referenced-symbol multiset, and bounded AST-shape features.

A missing fingerprint is allowed. Search must degrade gracefully rather than inventing equivalence.

### 4. Search service

Add service operations conceptually equivalent to:

- `symbol(query, include_history=False, limit=...)`
- `related(symbol_or_qualified_name, include_history=False, limit=...)`
- `discover(query, include_history=True, similarity_threshold=...)`
- `lineage(family_or_module, limit=...)`

`symbol` handles exact name/qualification search. `related` begins from a resolved declaration and returns evidence-stratified neighbors. `discover` combines name and structural candidates into an agent-safe receipt. `lineage` reports RoundNNN family transitions.

### 5. CLI and MCP surfaces

Add CLI commands following existing `dashi-agda` conventions:

```text
dashi-agda symbol <query> [--history] [--json]
dashi-agda related <symbol> [--history] [--json]
dashi-agda discover <query> [--history] [--json]
dashi-agda lineage <family-or-module> [--json]
```

Expose matching MCP tools through `mcp_server.py` so agents can use discovery directly instead of falling back to repository text search.

### 6. Discovery receipt

`discover` JSON includes at minimum:

```json
{
  "query": "...",
  "exact_matches": [],
  "equivalent_matches": [],
  "similar_matches": [],
  "historical_matches": [],
  "coverage": {
    "symbol_catalogue": true,
    "signature_index": true,
    "body_index": true,
    "historical_surfaces_checked": true
  },
  "absence_claim_permitted": false,
  "absence_reason": "related candidates exist"
}
```

Human-readable output must use cautious wording. The preflight layer never asserts semantic nonexistence, only indexed structural absence.

### 7. Round lineage analysis

Detect numbered round families from module/file names, grouping variants by a normalized family key with the round number removed. For consecutive rounds, compare declaration catalogues and classify:

- unchanged/exact-body equivalent;
- signature-equivalent but body-changed;
- renamed/structurally equivalent candidate;
- genuinely new;
- removed;
- dependency/API changes when available.

Report:

```text
novelty_ratio = substantive_new_or_changed / total_current_declarations
snapshot_noise_ratio = 1 - novelty_ratio
```

This is read-only evidence for later consolidation. It must not rewrite imports or infer theorem supersession automatically.

## SQLite migration

Increment the source-index schema version. Add derived declaration/search tables without rewriting the existing `modules`, `imports`, or `promotion_receipts` semantics.

Requirements:

- old v5 databases migrate automatically;
- existing module/interface/diagnostic payloads remain reusable where analyzer fingerprints permit;
- derived declaration rows are invalidated/rebuilt per changed module;
- indexes support qualified name, local name, signature hash, body hash, module/family, surface role, and round number queries;
- no external database service or embedding store.

## Data flow

```text
source change
  -> existing freshness/interface pipeline
  -> declaration catalogue refresh for changed module
  -> fingerprints + role/round classification
  -> SQLite derived indexes

agent query
  -> exact symbol/name lookup
  -> equivalent hash lookup
  -> bounded structural candidate ranking
  -> live/history partition
  -> discovery receipt
```

Warm unchanged searches should perform no source parse. A changed module only refreshes its declaration rows and any existing preflight state already invalidated by the source/API change.

## Similarity ranking

The first release uses deterministic structural scoring, not ML embeddings. Suggested weighted features:

- normalized signature match: dominant weight;
- declaration kind match;
- telescope arity/shape;
- referenced-symbol overlap;
- bounded AST-shape overlap;
- name-token similarity as a weak signal;
- same normalized round family as contextual evidence only.

Exact/signature-equivalent results are never mixed into heuristic-score ordering. Similarity results expose their score and matched features.

## Error handling and trust boundary

- malformed/unparseable modules remain discoverable at module/name level where cached data exists, but fingerprint coverage is marked incomplete;
- incomplete indexing sets `absence_claim_permitted=false`;
- ambiguous unqualified symbols return all candidates rather than choosing one;
- heuristic similarity never produces an equivalence claim;
- preflight continues to make no proof-validity claim; Agda remains the kernel/typechecker.

## Testing

Add focused unit/integration tests for:

1. schema migration from v5;
2. declaration insert/update/delete on source refresh;
3. exact qualified/unqualified search;
4. ambiguous symbol handling;
5. signature-equivalent and exact-body matches;
6. structurally similar candidate ordering;
7. live-vs-historical partitioning;
8. RoundNNN family detection and transition metrics;
9. absence receipt behavior under complete and incomplete coverage;
10. CLI JSON/human output;
11. MCP tool registration and payloads;
12. warm-query invariant: no source parse for unchanged indexed discovery queries.

Existing preflight tests and benchmark/performance gates must remain green. New discovery tests should use small synthetic Agda fixtures rather than the whole repository where possible.

## Performance targets

The discovery feature must preserve the existing warm-cache philosophy.

Initial acceptance targets:

- exact symbol lookup: SQLite-only on a warm index;
- exact body/signature neighbor lookup: SQLite-only on a warm index;
- related/discover query: no source parse on unchanged indexed modules;
- similarity query bounded by indexed candidate narrowing before Python scoring;
- lineage analysis operates from persisted declaration/family rows after indexing.

No hard sub-millisecond target is imposed in the first tranche; regressions that make discovery materially slower than ordinary interactive preflight use are unacceptable.

## Compatibility

- Existing `diagnose`, `next-error`, `benchmark`, `affected`, `refresh`, semantic promotion, and MCP behavior remains unchanged.
- No Agda theorem module is modified in the first tranche.
- The derived discovery schema is internal and may evolve, while CLI/MCP result fields introduced here should be kept backward-compatible where practical.

## Delivery milestones

### M1A — catalogue + exact symbol search

Schema migration, declaration catalogue, surface-role classification, exact qualified/unqualified search, CLI/service/MCP, tests.

### M1B — equivalence/similarity + discovery receipt

Signature/body fingerprints, structural candidate ranking, `related`, `discover`, absence-confidence logic, tests.

### M1C — Round lineage

Round-family classifier, historical partitioning, `lineage`, novelty/noise metrics, NS-focused real-repo audit fixture/report command.

After M1C is tested on the user's environment, the next architectural project is physical/canonical consolidation: derive stable current programme owners, demote full rounds to provenance, then prevent new mature-lane snapshot rounds.

## Success criteria

The tranche is successful when:

1. an agent can locate a known symbol without GitHub/grep search;
2. an agent can ask for equivalent/similar declarations and see evidence level explicitly;
3. a discovery query that finds only partial/historical/similar objects refuses to authorize a categorical absence claim;
4. normal output separates live results from RoundNNN history;
5. NS/YM round families can be quantified by declaration-level novelty/noise from the persistent index;
6. warm discovery queries do not parse unchanged source files;
7. all existing preflight behavior remains compatible and Agda remains the semantic authority.
