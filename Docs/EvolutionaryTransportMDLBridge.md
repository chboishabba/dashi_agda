# Evolutionary Transport MDL Bridge

`DASHI.Biology.EvolutionaryTransportMDLBridge` is a bounded biology bridge for
the thread:

```text
physics -> chemistry -> molecular machine -> cell signalling -> body/behaviour
```

The module records conserved molecular machinery as MDL-guided persistent
transport motifs. It reuses the canonical transport motif basis from
`DASHI.Computation.PersistentTransportMotifs` and stages evidence through:

1. an observation trace over physics, chemistry, and lineage context;
2. candidate physics, chemistry, molecular machine, cell signal, and
   body/behaviour surfaces;
3. conserved molecular machinery and persistent motif evidence;
4. an MDL score used as a guide, not as an optimizer theorem;
5. an MDL receipt, provenance trail, and bounded meaning promotion.

## Canonical Toy Inhabitants

The module includes canonical toy inhabitants for:

- `EvolutionaryTransportMDLBridge`
- `EvolutionaryTransportObservation`
- `CandidateEvolutionaryTransportState`
- `EvolutionaryMDLTransportReceipt`
- `PromotedBoundedEvolutionaryMeaning`
- `EvolutionaryTransportNonPromotionCertificate`

These witnesses demonstrate type-level coverage only. They are not empirical
origin-of-life, molecular simulation, or evolutionary biology receipts.

## Non-Promotion Guards

The only admissible route is:

```text
boundedMDLTransportReceiptRoute
```

The following routes reduce to the empty `Never` type:

- biology inevitability theorem
- explicit MDL optimizer claim
- abiogenesis proof
- full molecular simulation
- fitness universality
- origin-of-life closure

The promoted meaning also pins each corresponding claim to `false`.
