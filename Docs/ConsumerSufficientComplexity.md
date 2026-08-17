# Consumer-sufficient operational complexity

This note records the complexity theorem surface extracted from the SensibLaw
runtime audit.

Exact Kolmogorov complexity `K(x)` is uncomputable, so the Agda layer does not
pretend to calculate it.  The formal target is instead the admissibility boundary
for a computable operational-description surrogate: a smaller carrier is an
optimization only when the relevant consumer observation, residual and
provenance projections are unchanged.

`DASHI/Cognition/PNF/ConsumerSufficientComplexityExact.agda` defines an
`OperationalCarrierCost` with node, edge, residual, encoded-unit and boundary
coordinates.  `ConsumerSafeCompression` requires

```text
same consumer observation
same residual
same provenance
non-increasing operational description cost.
```

The composition theorem shows that certified consumer-safe reductions may be
chained without losing those invariants.  `FrontierBoundedTransition` separately
requires measured transition work to be bounded by the active frontier plus the
dependency edges actually touched.  Compact stored state therefore does not hide
an implementation that repeatedly scans inactive structure.

`OwnerFibreReductionComplexityExact.agda` gives a concrete physical witness for
that distinction.  Eight unit proposal waves produce

```text
1 + 2 + ... + 8 = 36
```

full-fibre scan units versus eight append-only input units.  This witness does
not license an incremental reducer.  Same-owner incremental execution requires
`IncrementalReductionSufficiency`, whose central obligation is an append
homomorphism between full reduction and prefix-summary/delta-summary
composition.  Independent-owner commutation is represented separately and is
strictly weaker.

`SignatureBucketReductionFactorizationExact.agda` isolates the next runtime
optimization boundary.  The concrete SensibLaw reducer performs compatibility
grouping inside exact semantic signature buckets, so a future internal cache may
combine bucket semantic outputs only after the concrete reducer discharges the
bucket-factorization premise.  Global dependency validity remains a separate
invalidation axis and is not erased by this theorem.

These modules are imported by `NumericPNFHyperfabricEverything.agda` alongside
the edit-transport and dependency-derived occurrence identity surfaces.  The
resulting intended chain is

```text
consumer-safe carrier projection
-> frontier-bounded transition
-> dependency-validity frontier
-> signature-local reduction
-> residual/provenance preservation
-> reopenable execution.
```

No external paper, author or DOI is asserted for this exact construction.  It is
an internal ITIR/PNF formalization extracted from the runtime architecture and
its measured/reachable complexity failure modes.
