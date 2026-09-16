# Digital-ESD database search execution frontier

Status: operational review-execution note. This document records search-protocol and translation state; it does not create database execution receipts, result counts, exports, screening decisions, or evidence completeness.

## Governing boundary

```text
query family retained
!= platform syntax known
!= exact translated query frozen
!= query executed
!= export retained
!= search complete
!= study eligible
```

Every transition requires its own receipt.

## Query-family repair

The versioned protocol now contains seven planned queries covering all six canonical query families:

1. Q1 `digitalEducationESD` — A AND B;
2. Q2 `digitalEducationESD` transformation refinement — A AND B AND C;
3. Q3 `reflexiveDigitalSustainability` — A AND D;
4. Q4 `lifecycleCircularity` — D;
5. Q5 `participantAgencyGovernance` — A AND B AND E;
6. Q6 `longitudinalInstitutionalImpact` — A AND B AND F;
7. Q7 `openInteroperabilityRepairability` — A AND G.

The earlier six-query version duplicated the `digitalEducationESD` family for Q1/Q2 without an explicit `lifecycleCircularity` planned-query witness. The regression was strengthened before the production repair.

## Current platform status

### Scopus

Official Scopus support documentation pays the syntax receipt:

```text
TITLE-ABS-KEY(<query>)
```

for title, abstract and keyword searching, with documented Boolean operators and phrase syntax.

All seven protocol queries are now frozen as exact `TITLE-ABS-KEY(...)` strings in `DigitalESDDatabaseTranslatedQueriesExact`.

```text
syntax observed = true
seven exact translated queries frozen = true
execution observed = false
```

### Web of Science Core Collection

Official Clarivate help pays the Topic field syntax:

```text
TS=(<query>)
```

where Topic searches title, abstract, author keywords and Keywords Plus.

All seven protocol queries are now frozen as exact `TS=(...)` strings in `DigitalESDDatabaseTranslatedQueriesExact`.

```text
syntax observed = true
seven exact translated queries frozen = true
execution observed = false
```

### IEEE Xplore

Official IEEE Xplore Command Search documentation pays quoted field-name syntax and Boolean/proximity operators.

```text
syntax observed = true
seven exact translated queries frozen = false
execution observed = false
```

The remaining payment is to choose and pin the exact field combination for each protocol query without silently broadening from a title/abstract/keyword-like surface to all metadata, or narrowing away relevant indexed terms.

### ERIC

Current ERIC pages and field documentation identify searchable bibliographic/indexing fields, but the current work has not yet pinned an exact reproducible seven-query command/UI recipe at the same evidentiary standard used for Scopus/WoS.

```text
syntax observed for exact translation = false
seven exact translated queries frozen = false
execution observed = false
```

Older ERIC search guides are not promoted into a current-platform syntax receipt merely because they describe Boolean/field searching historically.

### ACM Digital Library

Current ACM user documentation confirms Advanced Search field choices such as title, abstract, full text and author keyword plus Boolean filtering. The present work has not yet pinned the exact current seven-query UI/command recipe.

```text
syntax observed for exact translation = false
seven exact translated queries frozen = false
execution observed = false
```

A UI screenshot or older guide is not treated as an execution receipt.

## Attribution

The formal syntax owner retains exact attributed institutional sources for:

- Elsevier / Scopus Support Center — Advanced Search field codes and Boolean syntax;
- Clarivate / Web of Science Help — Core Collection Advanced Search field tags;
- IEEE / IEEE Xplore Help — Command Search syntax.

Citation or documentation membership imports neither proof of execution nor authority over study eligibility.

## Immediate P0 frontier

1. pin IEEE Xplore's seven exact query translations;
2. recover current reproducible ERIC translation semantics and freeze seven exact recipes;
3. recover current reproducible ACM DL translation semantics and freeze seven exact recipes;
4. execute each database query set and retain:
   - exact query/recipe;
   - platform/database;
   - execution timestamp;
   - result count;
   - export identity/hash where available;
   - filters/limits actually applied;
5. only then begin cross-database deduplication and eligibility screening.

## Non-promotion

```text
exact translation
!= execution

execution
!= complete search

result count
!= deduplicated corpus

retrieved record
!= eligible study

eligible study
!= claim accepted above its source-specific evidence ceiling
```

No database execution, result count, export, deduplication, screening or final inclusion receipt is claimed by this document.
