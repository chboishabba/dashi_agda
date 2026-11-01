# Numeric incremental ITIR runtime constitution

This note records the runtime-economy constitution layered on the canonical ITIR / PNF branch. It is deliberately an implementation reference: Python/PostgreSQL is expected to instantiate these boundaries rather than invent parallel semantic authority.

## Runtime reference stack

The immediate runtime reference is the combination of:

- canonical reopenable PNF / dynamic-safety core on PR #521;
- future-observation quotient, exact/relevant residual, dynamic composition, path-dependence, finite optimal residual and concrete spoken/Wikidata examples on PR #530;
- query-factorisation sufficiency and policy-relative projection safety on PR #531;
- numeric/incremental execution economy on PR #533 (this branch).

These are sibling theorem surfaces, not permission to duplicate them in Python.

## Numeric hot path

After parser observation, ordinary semantic execution is numeric. Text is an explicit ingestion/external/rendering boundary. Regex has no semantic-hot-path permission. Finite lexical cue languages may be compiled to numeric trie/DFA/Aho-Corasick-style machines; runtime complexity remains an empirical receipt rather than an Agda theorem about a particular implementation.

The parser output is treated as a compiled numeric observation tape. `NumericTokenStorageReference` now distinguishes a mere SymbolId stream from the full committed `SpacyNumericProjection.NumericTokenRow` tape. Packed/delta/varint/bit-coded storage is permitted only through an exact lossless tape codec:

`decodeTape (encodeTape tape) = tape`.

A low integer value does not by itself imply narrower PostgreSQL storage. Physical compactness and lookup/decode cost must be measured.

## Contextual world fibres

A lexical label owns a fibre of cached world candidates; it is not globally rewritten into one external entity. Candidate context requirements and mention-local observations are separate carriers.

A context-qualified attachment now requires the positive witness:

`required(candidate) subset-of observed(mention)`.

Failure to construct that witness is unresolved context, not refutation. Signed/ternary context-axis evidence may support, remain neutral toward, or contradict a candidate, but contextual preference has no world-identity promotion permission. Existing proof-producing external-alignment machinery remains the authority seam.

## Lazy H3 / H6 / H9

Logical horizon staging is not enough. H6 consumes exactly the unresolved H3 residual and H9 exactly unresolved H6. Ordinary evidence updates recompute the reverse-dependency frontier rather than rescanning a whole document or corpus.

The companion query/policy safety theorems on PR #531 provide the stronger application criterion for what counts as settled for a particular consumer. Python should therefore eventually stop at the cheapest horizon sufficient for the authorised query/policy, while keeping the underlying demand reopenable when a broader consumer can expose the hidden distinction.

## Corpus learning economy

The monotone work theorem is conditional on a controlled repeated workload. Equal token count is only a throughput normalisation and does not prove workload identity. `CorpusReuseReceipt` therefore carries an opaque runtime `workloadId`, and cross-receipt comparison requires exact workload identity plus token-carrier equality.

Chronological document order alone proves nothing about learning improvement: an unrelated later book may be intrinsically harder than an earlier note. The intended empirical comparison is repeated/controlled task families under an enlarged proof-bearing reusable context.

## Frequency-adaptive codes

Canonical `SymbolId` is stable semantic identity. Frequency-adaptive physical codes are a rebuildable storage/index projection; common symbols may receive low codes without rewriting canonical foreign keys. Their physical benefit must be earned through measured encoded bytes and lookup/decode work.

## Hot/cold execution

Append-only semantic history remains authority. Materialized hot current state is allowed only as an exactly rebuildable projection of that history. The implementation verifier must establish extensional equality in both directions; stale extra hot rows are not permitted merely because every latest-history row is present.

## Structural support

Parser-to-argument support is a sparse numeric seam with measured fanout. An unbounded token x object cross product is not a permitted implementation of that seam. Narrowing should precede joins, and bounded output does not justify unbounded intermediate work.

## Relative octant address

Three binary refinement coordinates give eight relative child states, requiring three bits for one relative octant digit. This does not imply that a complete provenance-bearing PNF cell fits in one byte. Relative address, semantic payload, and reopening provenance remain separate obligations.

## Performance boundary

Tokens are the primary cross-document throughput denominator after tokenisation; note/article/book counts are not directly comparable. Parser dominance and affine scaling are runtime-supplied receipts on identified workloads. The target is to make post-parser semantics much cheaper than spaCy, never to satisfy the ratio by slowing spaCy.

## Freeze-point for the next SensibLaw pass

The runtime should now be able to point each major shortcut at a theorem/boundary:

- contextual world narrowing -> context requirement witness + preference != proof;
- horizon stopping -> query/policy sufficiency + reopenability;
- residual minimisation -> exact vs relevant residual / finite certified-safe selector;
- incremental wakeups -> reverse dependency / future-observation relevance;
- corpus reuse -> same-workload learning economy;
- packed storage -> exact numeric observation-tape reconstruction;
- current-state materialisation -> exact rebuild from append-only authority;
- semantic cue scanning -> numeric automaton, no regex authority.

If a Python/PostgreSQL optimisation cannot identify its corresponding boundary, either the runtime shortcut is unsound or the formal reference is genuinely missing a seam.

## Validation boundary

This branch's fail-closed checker requires the new contextual matching, workload-comparability, and full observation-tape markers. No GitHub Actions / CI or CodeRabbit run is requested. Until a local/pinned Agda run succeeds, the branch remains source/signature-audited rather than kernel-certified.
