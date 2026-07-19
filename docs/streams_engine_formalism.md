# Streams Engine Formalism

## Status

Candidate-only bridge surface. This module does **not** promote legal,
clinical, trading, causal, evidentiary, governance, or moral authority.

Formal modules:

- `DASHI/Social/StreamsEngineBoundary.agda`
- `DASHI/Social/StreamsEngineRegression.agda`
- `DASHI/Social/StreamsEngineEverything.agda`

## Fixed architecture

The formal surface preserves the agreed Layer-0-plus-six-layer split:

0. text and concept substrate;
1. events and actors;
2. claims and cases;
3. normative systems and sources;
4. wrong types and duties;
5. protected interests and harms;
6. value frames and remedies.

The streams carrier is not a replacement for these layers. It is a derived,
provenance-preserving view across them.

## First-class stream families

Finance, conversations, social feeds, legal pressure, obligations, event
density, and user-defined measures are represented by the same
`StreamDefinition` / `StreamPoint` carrier. This prevents financial and social
sources from becoming ad hoc attachments to a legal-only graph.

A stream definition records:

- family and measure;
- direction;
- unit;
- subject actor and relationship identifiers;
- derivation kind;
- a human-readable derivation description.

A point records:

- its stream definition;
- time and rational proxy value;
- typed provenance anchors;
- a plain-language explanation.

`AdmissibleStreamPoint` requires non-empty provenance. It does not certify the
truth of the source, the correctness of an inference, or causation.

## Typed provenance

`SourceAnchorKind` covers text blocks, documents, sentences, token spans,
utterances, events, transactions, transfers, provisions, claims, cases,
evidence items, and receipts. An anchor keeps both valid time and observation
time so backfilled or later-discovered material is not silently rewritten as
contemporaneous knowledge.

## Bidirectional integration

The formalism records both directions explicitly:

- source records aggregate upward into stream points and candidate patterns;
- reviewed patterns may feed downward into candidate events, review
  annotations, user corrections, classifier review, or ontology review.

`BidirectionalStreamLink` requires raw-source preservation and reviewability.
The stream layer therefore enriches the shared TiRC/SensibLaw graph without
mutating the underlying transaction, utterance, document, or event into its
interpretation.

## Pattern boundary

Pattern kinds include threshold crossings, rolling shifts, clustered change
points, relationship shifts, financial shock clusters, finance/conversation
alignment, and legal-pressure alignment.

An `AdmissibleStreamPattern` must:

- cite at least one stream;
- retain at least one provenance anchor;
- remain at `candidatePatternStatus`.

Candidate patterns can enter a review queue, become a user annotation, or emit
a candidate event. Direct promotion to legal finding, clinical diagnosis,
trading authority, moral verdict, or causal proof is uninhabited.

## Regression witness

The regression module constructs:

- a transaction-backed finance stream;
- an utterance-backed concern-language stream;
- admissible points for both;
- a candidate finance/conversation alignment pattern;
- a bidirectional review annotation that preserves raw evidence;
- equality witnesses confirming that legal, clinical, trading, causal, and
  moral-authority claims stay blocked.

The example deliberately states only temporal alignment. It does not classify
abuse, diagnose a person, infer liability, recommend a trade, or establish a
moral verdict.

## Focused checks

```sh
agda -i . DASHI/Social/StreamsEngineBoundary.agda
agda -i . DASHI/Social/StreamsEngineRegression.agda
agda -i . DASHI/Social/StreamsEngineEverything.agda
```
