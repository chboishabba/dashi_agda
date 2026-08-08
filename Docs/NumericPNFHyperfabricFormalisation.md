# Numeric multiscale PNF hyperfabric formalisation

This tranche formalises the proof-relevant contract behind SensibLaw draft PR
`#470`, **Stream spaCy into a numeric multiscale PNF hyperfabric**.

It is not a second implementation of PostgreSQL, spaCy, the hierarchy planner,
or the corpus scheduler. It separates:

1. properties proved by typed constructions;
2. contracts the Python/PostgreSQL implementation must witness; and
3. external implementation assumptions, such as PostgreSQL B-tree behaviour.

The aggregate target is:

```text
DASHI/Cognition/PNF/NumericPNFHyperfabricEverything.agda
```

## Existing PNF integration

The tranche extends the existing PNF spine rather than defining a parallel
semantic object:

- `DASHI.Cognition.PNF.EventAlgebra` remains the candidate/event algebra;
- `DASHI.Interop.SensibLawResidualLattice` remains the residual vocabulary;
- spaCy remains `spaCyProducer`, an observation producer rather than semantic
  authority;
- multiscale interfaces retain source candidates and publish only admitted
  numeric keys plus unresolved residual demand signatures.

## Numeric identity boundary

`NumericAuthority.agda` separates:

- dense database-local numeric ids used for joins;
- stable digest identity used across rebuild or transfer; and
- textual human references outside the hot carrier.

The formal carrier does not assert that an auto-allocated `BIGINT` remains equal
across independent database rebuilds. Rebuild correspondence is by symbol kind
and stable digest, not local id equality.

## Strict spaCy projection

`SpacyNumericProjection.agda` makes parser admission explicit.

A strict token requires admitted POS and dependency observations. Annotation
origin is represented independently from annotation value:

- parser lemma output;
- orthographic lemma fallback;
- parser tag output;
- coarse-POS tag fallback; and
- unavailable annotation.

Historical data with unknown provenance cannot be relabelled as parser output.

spaCy roots point to themselves. A self-head commits only when the parser
explicitly declares it. A non-self dependency head commits only after the full
head span resolves. Missing non-self heads are projection failures and cannot be
rewritten as roots.

SensibLaw migrations 052, 059 and 060, together with the strict producer, now
implement this runtime boundary. The focused workflow must still be observed
before a passing runtime claim is made.

## Bounded planner and exact sketch budget

`BoundedMDLPlanner.agda` and `BoundedInterfaceSketch.agda` distinguish:

```text
candidate-state work        = N*W*B
retained backpointer state  = N*B
exact bounded-sketch work   = N*W*(3C+B)
```

Here:

- `N` is authored region count;
- `W` is the semantic window;
- `B` is retained beam width; and
- `C` is the witnessed exact key budget for each object/factor/demand family.

A copied predecessor path cannot inhabit the constant-pointer storage
certificate. An unbounded exact key set cannot inhabit the bounded end-to-end
certificate. The runtime may claim the stronger exact-work theorem only while
it fails closed when `C` is exceeded.

SensibLaw now uses constant-size predecessor cells and reconstructs the selected
segmentation once. Exact interface keys are bounded without silent truncation.

## Demand planning and parent reduction

`SetBasedDemandPlanning.agda`, `DemandResolutionState.agda`,
`DirectDemandLookup.agda`, and `ParentInterfaceReduction.agda` formalise:

- normalised demand-key capacity `D*K`;
- bounded candidate output `D*M`;
- exclusion of a procedural loop per demand;
- exclusion of recursive validation per candidate;
- candidate availability as distinct from semantic resolution;
- resolved state requiring an explicit target;
- interface lookup as a projection of an admitted export; and
- retention of immutable child evidence when a parent rejects promotion.

The logarithmic B-tree probe remains an explicit external `ProbeContract`.
Agda composes that assumption with bounded output and DAG validation costs; it
does not claim to prove PostgreSQL's storage engine.

## Adjacent reconciliation

`AdjacentReconciliationWork.agda` represents adjacent sentence and paragraph
pairs as overlapping execution fibres, not replacement containment parents.
It formalises:

- ordered non-overlapping siblings under one canonical parent;
- durable work state and lease epochs;
- candidate evidence distinct from resolution evidence;
- no automatic resolution from adjacency alone;
- sentence and paragraph drains as wired; and
- at most one immediate pair per linear sibling boundary.

SensibLaw migrations 055, 056 and 058 plus the leased executor implement the
matching carrier and late ancestry binding.

## Ordered world fold and parser lookahead

`OrderedWorldParserLookahead.agda` formalises corpus execution as an indexed
world fold:

```text
W0 --compile D1--> W1 --compile D2--> W2 ... --compile Dn--> Wn
```

`publishNext` consumes a `WorldStep` indexed by the world produced by the
preceding prefix. This is the semantic ordering contract: a later document is
compiled against the accumulated prior world rather than concurrently against a
stale shared world.

Parser lookahead is a different authority:

```text
ParserLookahead D : parser observation only
WorldStep W D     : closed document publication
```

There is deliberately no constructor from `ParserLookahead` to `WorldStep`.
Parser observations cannot publish a document, discharge world-relative demands,
or extend the world.

The formal execution state contains:

- exactly one semantic frontier; and
- a `LookaheadSlot` that is either empty or contains one parser document.

This matches the runtime's bounded, size-aware lookahead. A large document such
as 0008 may begin spaCy parsing while earlier small documents close and publish,
but semantic document publication remains serial.

The worker allocation contains a proof that:

```text
foreground workers + parser-lookahead workers <= global worker budget
```

The canonical four-worker witness allocates two workers to each lane. Worker
allocation and heavy-document selection are declared physical scheduling
choices with no semantic-authority effect.

## Strict publication

`NumericPNFCompilation.agda` formalises fenced partition completion and a strict
publication type available only for closed document coverage. It records:

```text
legacy_document_materialisation = false
legacy_projection_invoked       = false
world_resolution_deferred       = true
```

A strict publication contains the closed document interface, residual demands,
and numeric counts. It does not reconstruct an arbitrary local mention carrier.

## Runtime correspondence

The current runtime correspondence is:

- strict parser capability and annotation-origin admission: implemented;
- explicit root/non-root dependency projection: implemented;
- constant-pointer planner with exact fail-closed key budget: implemented;
- set-based demand planning and explicit resolution state: implemented;
- lookup/export coherence and child-evidence retention: implemented;
- adjacent sentence and paragraph work: implemented and wired;
- ordered semantic publication: selected by the ordered tranche runner with
  `document_workers=1`;
- bounded parser-only lookahead: implemented for partition-worthy documents;
- global worker-budget split: implemented;
- duplicate parser work fence through checkpoint reuse: implemented.

The runtime and formal PRs remain drafts until their respective integration and
Agda checks are observed.

## Acceptance gates

Conformance requires all of the following:

1. missing non-self spaCy heads cannot become self-loops;
2. annotation absence cannot masquerade as a meaningful symbol;
3. planner paths use constant-size predecessors and exact key budgets fail
   closed;
4. candidate evidence cannot set resolved state without a target;
5. searchable parent lookup rows correspond to admitted exports;
6. adjacent evidence remains separate from semantic resolution;
7. exactly one document crosses the world-publication frontier at a time;
8. parser lookahead writes observation checkpoints only;
9. foreground and parser lanes remain within the global worker budget;
10. the focused Agda aggregate typechecks;
11. PostgreSQL migrations and real spaCy integration pass independently; and
12. document 0008 and synthetic scaling measurements report parser,
    post-parser, persistence, and peak-memory costs separately.

The formalisation proves the algorithmic and authority contract. It does not
substitute for migration tests, database execution plans, parser-quality
assessment, or measured scaling evidence.
