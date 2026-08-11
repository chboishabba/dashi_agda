# Work-conserving persistence formalisation

`DASHI.Cognition.PNF.WorkConservingPersistence` formalises the authority and
worker-allocation boundary implemented by SensibLaw migration 061 and the
work-conserving ordered runner.

## Provisional rows are not publication authority

The formalisation distinguishes:

```text
provisionalExecutionOnly
closedDocumentAuthority
```

`PublicationPermission` has a constructor only for
`closedDocumentAuthority`. Therefore:

```text
PublicationPermission provisionalExecutionOnly → ⊥
```

A `ProvisionalDocumentStage` may contain typed execution rows, but it cannot
inhabit a document publication. A `ClosedPersistenceMerge` contains the
ordinary `WorldStep` and is the only persistence value accepted by
`publishClosedPersistenceMerge`.

This preserves the indexed ordered fold:

```text
W0 --D1--> W1 --D2--> ... --Dn--> Wn
```

Parallel PostgreSQL staging does not create a second semantic frontier.

## Work-conserving budget transfer

Before persistence, the canonical four-worker allocation is:

```text
foreground semantic kernel: 2
parser lookahead:            2
```

During persistence, the parser lane is quiesced and the critical kernel owns:

```text
PostgreSQL persistence: 4
reserved elsewhere:     0
```

Both allocations carry proofs that active and reserved workers remain within
the same global budget. `persistenceReceivesWholeBudget` proves the active
persistence worker count equals the total worker count.

The transfer record also declares that the parser lane resumes only after the
persistence interval ends. Parser observations retain observation authority
only throughout the transfer.

## Physical execution shape

The current runtime status records:

- typed parallel staging followed by set-based authority merge;
- no JSON authority in the staging carrier;
- no publication permission for provisional rows;
- several physical COPY backends;
- one ordered document publication; and
- full-budget ownership by the active critical kernel.

The fixed family statement bound is an execution contract, not a proof of
PostgreSQL implementation internals. Runtime migration tests, query plans,
receipts, and the controlled 0007 benchmark remain required independently.
