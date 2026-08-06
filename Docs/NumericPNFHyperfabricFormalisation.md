# Numeric multiscale PNF hyperfabric formalisation

This tranche formalises the proof-relevant contract behind SensibLaw draft PR
`#470`, **Stream spaCy into a numeric multiscale PNF hyperfabric**.

It is not a second implementation of PostgreSQL, spaCy, or the runtime planner.
It separates:

1. properties proved by the typed algorithm;
2. contracts that the Python/PostgreSQL implementation must witness; and
3. external implementation assumptions, such as PostgreSQL B-tree behaviour.

The aggregate target is:

```text
DASHI/Cognition/PNF/NumericPNFHyperfabricEverything.agda
```

## Existing PNF integration

The tranche reuses the existing PNF spine rather than defining a parallel
semantic object:

- `DASHI.Cognition.PNF.EventAlgebra` remains the candidate/event algebra;
- `DASHI.Interop.SensibLawResidualLattice` remains the residual vocabulary;
- spaCy remains `spaCyProducer`, an observation producer rather than semantic
  authority;
- multiscale interfaces retain source `CandidatePNF`s and publish only promoted
  numeric keys plus unresolved residual demand signatures.

## Identity theorem boundary

`NumericAuthority.agda` separates three strata:

- dense database-local numeric ids used for joins;
- stable digest identity used across rebuild or transfer;
- textual/hexadecimal human references outside the hot carrier.

The formal carrier does **not** assert that an auto-allocated `BIGINT` remains
equal across independent database rebuilds. Rebuild correspondence is by symbol
kind and stable digest, not local id equality.

## spaCy projection contract

`SpacyNumericProjection.agda` makes the parser boundary explicit.

### Sentence ownership

A sentence is one of:

- fully owned: commit it;
- boundary crossing: create a repair obligation;
- outside the owner range: ignore it.

There is no constructor that commits a partial crossing sentence as owned.

### Annotation absence

Capability absence is represented as `annotationUnavailable capability`.
It is not represented as a meaningful empty-string symbol. Lemma fallback to
orthography is also explicit through `orthFallbackLemma`.

This matters because the numeric operator loop compares symbol ids. An empty
symbol id must not accidentally satisfy or participate in a semantic rule when
the corresponding spaCy component was not present.

### Dependency-head fidelity

spaCy roots point to themselves. The formal projection therefore permits a
self-head only when the parser observation explicitly declares a self-head.
For a non-self head:

```text
head coordinate lookup succeeds -> commit dependency head id
head coordinate lookup fails    -> projection failure / repair obligation
```

A missing non-self head cannot be rewritten as a self-loop.

This exposes a concrete mismatch in the current PR `#470` Python draft. In
`src/storage/postgres/spacy_numeric_projection.py`, head resolution currently
uses a lookup with the current token id as the default. That silently conflates
"parser root" with "head lookup failed". The runtime must remove that fallback
or record an explicit boundary/projection failure before it can witness the
Agda contract.

The committed `token_id -> head_token_id` relation is already the dependency
graph. The PNF layer should consume it directly rather than project a second
parallel dependency graph.

## Progressive reduction and world barrier

`NumericHyperfabric.agda` formalises:

- sentence, adjacent-sentence, paragraph, adjacent-paragraph, adaptive block,
  provision, section, chapter, execution-window, document and tranche regions;
- typed DAG edges;
- direct typed ancestors and binary-lifting rows;
- promotion evidence and a proof-bearing promotion gate;
- closed interfaces containing promoted object/factor keys and residual demands;
- the impossibility of world publication while document coverage is open.

The current runtime executor status is represented honestly:

```text
sentence            wired
adjacent sentence   not yet wired
paragraph           wired
adjacent paragraph  not yet wired
adaptive block      wired
document            wired
```

Schema support is not treated as executor completion.

## Bounded MDL planner proof

`BoundedMDLPlanner.agda` proves the intended word-RAM cost model for `N` authored
regions, fixed semantic window `W`, and beam width `B`.

Candidate-state capacity:

```text
E(0,W,B)     = 0
E(N+1,W,B)   = W*B + E(N,W,B)
E(N,W,B)     = N*(W*B)
```

Retained backpointer-state capacity:

```text
M(0,B)       = 0
M(N+1,B)     = B + M(N,B)
M(N,B)       = N*B
```

Therefore, with fixed `W` and `B`, candidate construction is linear in `N` and
retained planner state is linear in `N` **provided every beam state stores a
constant-size backpointer**.

The proof deliberately rejects copied full paths. The current active planner in
PR `#470` still stores tuples of prior segments and constructs
`(*prior_segments, segment)`. That implementation has not yet witnessed the
backpointer premise, so the stated end-to-end `O(N*W*B)` time and `O(N*B)` memory
claims are not yet justified for that function. Candidate evaluation count may
still be bounded by `N*W*B`, but tuple copying adds path-length work and payload.

## Direct indexed lookup

`DirectDemandLookup.agda` proves two internal facts:

- one global lookup row per export is linear in export count;
- total lookup work composes as:

```text
probe cost + returned candidate count + DAG validation path height.
```

The logarithmic B-tree probe is an explicit `ProbeContract`. Agda composes that
assumption with the bounded-candidate and nearest-common-interface validation
costs; it does not claim to prove PostgreSQL's storage engine.

The old ancestor-payload-copy strategy is represented by a triangular recurrence
to make the source of potential quadratic growth visible.

## Strict publication

`NumericPNFCompilation.agda` formalises fenced partition completion and a strict
publication type that exists only for closed coverage. It records the same
bypass contract as PR `#470`:

```text
legacy_document_materialisation = false
legacy_projection_invoked       = false
world_resolution_deferred       = true
```

A strict publication contains the closed document interface, residual demands
and numeric counts. It does not reconstruct an arbitrary local mention carrier.

## Acceptance gates

The runtime may claim conformance to this tranche only after all of the following
hold:

1. non-self spaCy head lookup failure is explicit and cannot become a self-loop;
2. annotation capability absence cannot masquerade as a meaningful empty symbol;
3. the active MDL planner stores constant-size backpointers and reconstructs the
   selected segmentation afterward;
4. the focused Agda aggregate typechecks;
5. PostgreSQL migrations and real spaCy integration pass independently;
6. adjacent-sentence and adjacent-paragraph reconciliation remain labelled
   incomplete until their durable overlapping-pair executor is wired;
7. measured document performance is reported separately from the asymptotic
   proof.

The formalisation proves the algorithmic contract. It does not substitute for a
book-scale benchmark, database execution plan, migration test, or parser-quality
evaluation.
