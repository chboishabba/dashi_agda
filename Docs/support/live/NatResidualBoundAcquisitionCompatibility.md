# Nat residual-bound acquisition compatibility

Date: 2026-09-08

The Nat/Wikidata branch now represents a blocking Q/P coverage state as an exact `NatCoverageResidual` carrying subject, property, coverage status, graph revision, coverage policy, consumer, and missing coordinate. `NatCoverageAcquisitionDemand residual` derives the producer from that coordinate and keeps the exact subject/property representation requirement explicit.

Concrete live example:

`P14143 uninspected -> targetPropertyFamily -> empiricalEvidenceProducer -> acquire the same subject/P14143 family under a certified representation -> recompute coverage`

A P31 fetch, a peer-item fetch, successful shard transport, or a returned row does not pay the P14143 residual by existence.

This branch intentionally does **not** import PR #823-only `IntrospectiveProofLoopExact` while #823 is unmerged. After #823 lands, the intended dependent weld is from `NatCoverageAcquisitionDemand residual` to the exact `ConsumerDefectSourceDemand` for the live Nat residual.

Firewalls:

- transport != coverage payment;
- another property != this property;
- returned row != query-family completeness;
- acquisition demand != migration authority;
- acquisition result still requires coverage recomputation.
