# Digital-ESD declared database execution runbook

**Status:** operational review-work instructions. This document is not scholarly evidence and does not create a database execution receipt merely by existing.

## Current exact state

Remote Digital-ESD source generation currently has:

```text
Scopus              7/7 exact translations
Web of Science      7/7 exact translations
IEEE Xplore         7/7 exact translations
ERIC                 7/7 exact translations
ACM Digital Library  7/7 exact translations

total               35/35 frozen translations
```

Execution-attempt ledger:

```text
Scopus              7 attempts: HTTP 403 before submission
Web of Science      7 attempts: HTTP 403 before submission
ERIC                 7 attempts: current web transport failed before observed API response
IEEE Xplore          7 attempts: current web transport could not retrieve live query-bearing result pages
ACM Digital Library  7 attempts: current web transport could not retrieve live query-bearing result pages
```

Therefore:

```text
execution attempt != query submission
query submission != observed result set
observed result set != retained export
retained export != included corpus
```

## Execution Pareto

Use this order unless access conditions materially change:

1. **ERIC** — exact queries and official public API syntax are paid; run locally and retain raw result pages/exports.
2. **IEEE Xplore** — exact Command Search queries are paid; execute the frozen strings and retain count/export/query evidence.
3. **Scopus / Web of Science** — execute when authenticated/institutional access is available.
4. **ACM Digital Library** — exact translations are now pinned; execute through the official Advanced Search / ACM Full-Text / Anywhere scope and retain count/export/query evidence.

This is an operational readiness ordering, not a source-quality/evidence ranking.

## ERIC local execution

Canonical query strings live in:

`DASHI/Education/DigitalESDDatabaseTranslatedQueriesExact.agda`

as:

```text
ericQ1DigitalEducationESD
ericQ2Transformation
ericQ3ReflexiveSustainability
ericQ4LifecycleCircularity
ericQ5ParticipantGovernance
ericQ6LongitudinalInstitutional
ericQ7OpenInteroperableRepairable
```

Official API surface retained in:

`DASHI/Education/DigitalESDDatabaseTranslationSyntaxExact.agda`

Canonical request shape:

```text
https://api.ies.ed.gov/eric/?search=<URL-ENCODED-QUERY>&rows=200&format=json&start=<OFFSET>
```

For each Q1-Q7:

1. copy the exact `exactTranslatedQuery` string from the Agda owner;
2. URL-encode only for transport; retain the unencoded canonical query separately;
3. record an offset-aware execution timestamp;
4. request `start=0&rows=200&format=json`;
5. retain the raw response before transformation;
6. record `numFound`;
7. continue `start=200,400,...` until every record in that result set has been fetched;
8. retain every raw page or one lossless combined raw export;
9. retain any derived CSV separately from the raw export;
10. record a stable local path / artifact reference and preferably a SHA-256 digest.

A successful ERIC run should be capable of populating a future
`executedWithObservedResultSet` outcome. A transport failure, malformed query,
HTTP failure, or incomplete pagination must instead remain a failure/partial
execution state.

## IEEE Xplore

Use the seven exact `ieeeQ*` Command Search strings from
`DigitalESDDatabaseTranslatedQueriesExact.agda`.

For every query retain:

- the exact submitted string;
- execution date/time;
- the Command Search interface used;
- unfiltered result count;
- all filters subsequently applied, if any;
- exported result-set artifact;
- export format and artifact identity.

Do not silently replace a frozen Command Search string with a Basic Search,
different field scope, relevance-search paraphrase, or manually shortened
query.

## Scopus and Web of Science

The existing 2026-09-16 receipts document access failure before submission.
Those receipts are historical observations and must not be overwritten.

When authenticated execution becomes available, create new successful
execution receipts retaining:

- the exact existing translated query;
- platform/interface;
- timestamp;
- result count;
- retained result export;
- execution environment / account-access context sufficient for reproducibility.

A successful later execution does not make the earlier blocked attempt false;
both belong in append-only execution history.

## ACM Digital Library

The seven exact ACM Advanced Search translations are frozen in
`DigitalESDDatabaseTranslatedQueriesExact.agda`, sourced to official ACM
Digital Library documentation for Advanced Search, Boolean AND/OR/NOT,
exact-phrase quotation and the Anywhere search surface.

Use the ACM Full-Text collection / Anywhere scope retained by the syntax
receipt. Retain exact submitted string, timestamp, unfiltered count, filters,
export artifact and export format. The current web-transport attempt receipts
are failures before an observed result page and must not be treated as
zero-result searches.

## Mapping execution work into the Agda lineage

The existing dependent chain is:

```text
DatabaseExecutionReceipt × 5 surfaces
-> DeduplicationReceipt
-> EligibilityScreeningReceipt
-> StructuredExtractionReceipt
-> TransparentStructuredSearchClosureReceipt
```

The newer same-object weld then requires:

```text
TransparentStructuredSearchClosureReceipt
+ IncludedSourceLineage source
+ SourceAuditAdmission source
-> CorpusAuditedSource source
```

For every ultimately included source retain a source-specific locator into:

- included-set artifact;
- screening decision / exclusion-inclusion ledger;
- structured extraction row;
- exact source identity/provenance.

No pre-screen candidate, search hit, DOI, query result snippet or included-set
string reference is sufficient by itself.

## Deduplication and screening must wait for retained exports

Cross-database deduplication begins only after the declared executed surfaces
have retained exports sufficient to support identity comparison.

Screening then retains:

- eligibility-criteria version;
- screened set;
- included set;
- excluded set;
- exclusion-reason ledger.

The pre-screen acquisition/Pareto corpus remains discovery/calibration only and
cannot be inserted into the included set unless it is recovered/admitted
through the declared review lineage.

## Current stopping rule

Do not reopen generic source acquisition while database execution is unpaid.

Reopen source acquisition/formalism only if the admitted corpus exposes:

- a new P0 `who is not at the table?` residual;
- a new upstream eligibility-frame residual;
- a constructive `FactorsThrough` collision;
- or materially stronger same-object evidence required by a manuscript consumer.
