# Consumer restriction / aggregation intertwiner

This note records the formal correction exposed by the 2026-08-19 SensibLaw
hierarchy-close forensic audit.

## Corrected runtime diagnosis

The parent hierarchy implementation was initially described too broadly as an
accumulated-history reconstruction. That is false. `_close_parent_interface()`
already reads only the direct child interface fibres.

The measured cost sits inside that local composition:

```text
large overlapping child lookup fibre
-> quotient/group/min(rank)
-> selective parent-export admission
-> parent lookup
```

The candidate optimisation is therefore:

```text
large overlapping child lookup fibre
-> parent-export admission
-> quotient/group/min(rank)
-> parent lookup
```

provided the two routes are extensionally equal.

## Exact theorem shape

`DASHI.Cognition.PNF.ConsumerRestrictionAggregationIntertwinerExact` separates:

- the fine row carrier;
- the quotient/grouping key;
- the consumer/parent admission router;
- the fibre-local fold;
- the exact commuting equation.

The central law is:

```text
restrictAggregate c p (aggregate xs)
==
aggregate (restrictFine c p xs)
```

This is deliberately an exact intertwiner, not a generic claim that SQL
predicates should always be pushed down.

## Saturation / factorisation boundary

A legal early restriction must select or reject whole quotient fibres. The
module therefore provides `FibreSaturatedRestriction` and the negative witness
`AdmissionFactorizationDefect`.

One witness of the shape

```text
fineKey x == fineKey y
but
admission x != admission y
```

refutes fibre saturation and blocks the pushdown.

A `KeyIndexedRestriction` is saturated structurally because admission is defined
on the quotient key itself.

This mirrors the factorisation discipline cross-pollinated in PR #584: exact
factorisation/naturality is distinct from separation, reconstruction and future
safety.

## Consumer indexing

Restriction is indexed by consumer/parent, and a role/query-indexed carrier is
provided as well. A lookup key may be irrelevant to one parent publication while
remaining relevant to another consumer.

Therefore:

```text
locally inadmissible for consumer C
!=
globally irrelevant
!=
semantic erasure permission.
```

This follows the variable-rank active-obligation and indexed-interpretation
pattern converged by PR #582.

## Relation to exact intertwiners

PR #583's transfer work uses exact intertwiners rather than loose compatibility.
The same proof-engineering rule applies here. The desired implementation square
is:

```text
child rows -----------------> grouped parent candidates
   |                                  |
   | consumer restriction             | parent restriction
   v                                  v
admitted child rows --------> grouped admitted candidates
```

and the square must commute exactly.

## Aggregation-fibre interpretation

PR #587 makes aggregation fibres and their lost distinctions explicit. The
runtime analogue here is complementary: the generic grouping quotient may
construct quotient classes that the current consumer has already declared
inactive.

The optimisation principle is therefore:

```text
apply consumer-known irrelevance at the earliest carrier for which an exact
intertwiner has been proved.
```

This is stronger than "avoid global history scans" because the source carrier can
already be perfectly local and still contain consumer-inactive quotient fibres.

## Physical economy remains empirical

`PushdownEconomyReceipt` keeps semantic legality separate from measured benefit:

```text
rowsScanned
rowsAdmitted
rowsGrouped
rowsOutput
rowsAttemptedWrite
rowsCommittedWrite
```

A reduction in `rowsGrouped` does not prove a reduction in `rowsScanned`.
PostgreSQL planner and buffer evidence remain empirical obligations.

The retained SensibLaw baseline found a highly skewed parent-close distribution:
one document-root close accounted for 42.4% of lookup input and the top ten for
77.7%. At that root, parent admission before grouping would reduce grouping input
from 358,965 rows to 125,933 rows while retaining the same 42,836 parent lookup
rows under the read-only parity audit.

These measurements motivate the optimisation; they are not Agda theorems.

## Falsifier-driven optimisation ladder

The resulting runtime workflow matches the repo's observer-refinement ladders:

```text
hotspot
-> identify amplification fibre
-> prove legal consumer restriction
-> microbenchmark
-> optimise
-> reprofile residual cost
-> repeat
```

A successful pushdown does not certify the entire hierarchy stage as optimal.
The next residual may be index fetch, hashing, WAL, ancestor publication, or
another consumer-specific projection.
