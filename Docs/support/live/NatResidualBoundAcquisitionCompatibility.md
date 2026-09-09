# Nat residual-bound acquisition compatibility

Date: 2026-09-09

The Nat/Wikidata branch represents a blocking Q/P coverage state as an exact `NatCoverageResidual` carrying subject, property, coverage status, graph revision, coverage policy, consumer, and missing coordinate. `NatCoverageAcquisitionDemand residual` derives the producer from that coordinate and keeps the exact subject/property representation requirement explicit.

Concrete live shape:

`P14143 uninspected -> targetPropertyFamily -> empiricalEvidenceProducer -> acquire the same subject/P14143 family under a certified representation -> recompute coverage`

A P31 fetch, a peer-item fetch, successful shard transport, or a returned row does not pay the P14143 residual by existence.

## Runtime counterpart

SensibLaw PR #493, branch `agent/nat-batch-prerequisite-runner`, now carries the same discipline into the executable Nat acquisition lane:

`row-local Q/P residual -> bound acquisition demand -> one coalesced shared transport -> task projection -> residual-local recomputation`.

The shared network execution is deliberately many-to-one, but semantic identity is not:

`many live residuals -> one shared fetch -> many exact residual-local recomputations`.

The hosted QID scan is bounded, rate-limited and parallel, but semantic commit remains ordered. One unresolved union QID no longer blocks statement acquisition for unrelated resolved QIDs: the resolved subset proceeds to revision-locked Wikidata entity export, while the unresolved QID remains a live identity residual.

For a projected entity snapshot, exact recomputation requires the same Q, the same requested property family and the same revision-bound representation. Under that exact-family view both outcomes are legitimate:

- `P14143 present -> queryCoverageComplete for the exact Q/P family`;
- `P14143 absent -> queryCoverageComplete for the exact Q/P family at that entity revision`.

That narrow recomputation may pay the **coverage coordinate only**. It does not pay source support, semantic correspondence, consumer closure, migration safety, edit authority or semantic promotion.

The runtime receipt therefore distinguishes:

- transport/execution outcome;
- QID identity resolution;
- projected statement snapshot;
- exact Q/P coverage recomputation;
- `coverage_coordinate_paid`;
- still-separate source-support and consumer-verification obligations.

## #823 compatibility

This branch intentionally does **not** import an unmerged #823 branch. #823 now owns the generic repository-wide `DASHI.Core.BoundAcquisitionDemandExact` carrier, with `IntrospectiveProofLoopExact` as a specialization. After that owner is available from the declared base, the intended weld is small:

`NatCoverageAcquisitionDemand residual -> BoundAcquisitionDemand alignment selected residual`

with the dependent equalities that the selected requirement denotes this exact Nat residual and the acquisition producer equals `producerForCoverageCoordinate (coordinate residual)`.

Firewalls remain:

- transport != coverage payment;
- another property != this property;
- returned row != query-family completeness;
- acquisition demand != migration authority;
- coverage payment != source-support payment;
- coverage payment != consumer closure;
- coverage payment != semantic promotion.
