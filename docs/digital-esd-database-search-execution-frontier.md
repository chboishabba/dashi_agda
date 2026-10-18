# Digital-ESD database search execution frontier

Status: operational review-execution note. The protocol, exact Scopus/WoS translations, and a typed execution-attempt/result-set receipt layer now exist. The current execution environment is blocked before query submission by both Scopus and Web of Science entrypoints, so no result counts or exports are claimed.

## Governing boundary

```text
query family retained
!= platform syntax known
!= exact translated query frozen
!= execution attempted
!= query submitted
!= result set observed
!= export retained
!= search complete
!= study eligible
```

Every transition requires its own receipt.

## Query-family repair

The versioned protocol contains seven planned queries covering all six canonical query families:

1. Q1 `digitalEducationESD` — A AND B;
2. Q2 `digitalEducationESD` transformation refinement — A AND B AND C;
3. Q3 `reflexiveDigitalSustainability` — A AND D;
4. Q4 `lifecycleCircularity` — D;
5. Q5 `participantAgencyGovernance` — A AND B AND E;
6. Q6 `longitudinalInstitutionalImpact` — A AND B AND F;
7. Q7 `openInteroperabilityRepairability` — A AND G.

The earlier six-query version duplicated the `digitalEducationESD` family for Q1/Q2 without an explicit `lifecycleCircularity` planned-query witness. The regression was strengthened before the production repair.

## Exact execution/result-set receipt owner

`DigitalESDDatabaseExecutionReceiptExact` now distinguishes successful execution from pre-submission failure by construction.

```text
ExecutionOutcome =
    executedWithObservedResultSet(count, result-set identity, export state, evidence)
  | accessBlockedBeforeSubmission(reason)
  | authenticationBlockedBeforeSubmission(reason)
  | interfaceFailureBeforeSubmission(reason)
```

The blocked constructors carry no result count or export payload. Therefore:

```text
HTTP 403 / authentication failure
!= zero results
```

and:

```text
execution attempt
!= query submission
!= observed result set
```

Fourteen query-specific execution receipts are retained: seven Scopus and seven Web of Science translations.

## Scopus

Official Scopus documentation pays the syntax receipt:

```text
TITLE-ABS-KEY(<query>)
```

All seven protocol queries are frozen as exact `TITLE-ABS-KEY(...)` strings in `DigitalESDDatabaseTranslatedQueriesExact`.

Execution attempt on 2026-09-16 from the available ChatGPT web environment reached:

```text
https://www.scopus.com/search/form.uri?display=advanced
```

but the platform returned HTTP 403 before the query could be submitted.

The corresponding seven execution receipts therefore retain:

```text
execution attempted = true
query submitted = false
outcome = accessBlockedBeforeSubmission
result count = structurally unavailable
export = structurally unavailable
```

The official Scopus Search API is a legitimate alternate execution path, but Elsevier requires an API key and, for subscriber entitlements, institutional/IP or token authentication. No API key/institution token is available in this execution environment, so the API does not provide a hidden substitute receipt.

## Web of Science Core Collection

Official Clarivate documentation pays:

```text
TS=(<query>)
```

for Topic search over title, abstract, author keywords and Keywords Plus. All seven protocol queries are frozen as exact `TS=(...)` strings.

Execution attempt on 2026-09-16 from the available ChatGPT web environment reached:

```text
https://www.webofscience.com/wos/woscc/basic-search
```

but the platform returned HTTP 403 before query submission.

The corresponding seven execution receipts therefore retain the same fail-closed state:

```text
execution attempted = true
query submitted = false
outcome = accessBlockedBeforeSubmission
result count = structurally unavailable
export = structurally unavailable
```

Clarivate's Web of Science APIs require an application/API key; available plans depend on subscription/registered credentials. No such credential is present in this execution environment.

## IEEE Xplore

Official IEEE Xplore Command Search documentation pays quoted field-name syntax and Boolean/proximity operators.

```text
syntax observed = true
seven exact translated queries frozen = false
execution observed = false
```

The remaining payment is to choose and pin the exact field combination for each protocol query without silently broadening from a title/abstract/keyword-like surface to all metadata, or narrowing away relevant indexed terms.

## ERIC

Current ERIC pages and field documentation identify searchable bibliographic/indexing fields, but the current work has not yet pinned an exact reproducible seven-query command/UI recipe at the same evidentiary standard used for Scopus/WoS.

```text
syntax observed for exact translation = false
seven exact translated queries frozen = false
execution observed = false
```

Older ERIC search guides are not promoted into a current-platform syntax receipt merely because they describe Boolean/field searching historically.

## ACM Digital Library

Current ACM user documentation confirms Advanced Search field choices such as title, abstract, full text and author keyword plus Boolean filtering. The present work has not yet pinned the exact current seven-query UI/command recipe.

```text
syntax observed for exact translation = false
seven exact translated queries frozen = false
execution observed = false
```

A UI screenshot or older guide is not treated as an execution receipt.

## Attribution / same-object discipline

The execution owner retains the exact translated query object, search surface, timestamp, entrypoint, execution environment and outcome. A result-set count/export may exist only in an executed-result constructor.

```text
same canonical family
!= same translated query
!= same execution object
!= same result set
```

Likewise:

```text
same translated query at another date/interface/account
!= definitionally the same result-set receipt
```

This follows the repository's broader proposition-local and same-observable discipline: labels and source identity do not manufacture the exact consumed value/result object.

## Current P0 status

```text
P0a query-family protocol                  PAID
P0b Scopus/WoS exact translations          PAID
P0b IEEE translation                       PARTIAL (syntax only)
P0b ERIC/ACM translation                   UNPAID
P0c execution/result-set receipt model     PAID
P0d Scopus/WoS execution attempts          PAID AS ATTEMPTS
P0d Scopus/WoS submitted executions        BLOCKED / UNPAID
P0d Scopus/WoS result counts + exports     UNPAID
P0e deduplication/screening/extraction     UNPAID
```

The next exact payment for Scopus/WoS is not another query-design theorem. It is execution in an authenticated browser/institutional session or with legitimately provisioned API credentials, producing `executedWithObservedResultSet` receipts.

## Non-promotion

```text
exact translation
!= execution attempt

execution attempt
!= query submission

access block
!= zero results

query submission
!= complete search

result count
!= deduplicated corpus

retrieved record
!= eligible study

eligible study
!= claim accepted above its source-specific evidence ceiling
```

No result count, export, deduplication, screening or final inclusion receipt is claimed by the blocked attempts.
