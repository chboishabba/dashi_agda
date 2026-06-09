# Yang-Mills Constructive QFT Flag Route

This document is the reader-facing companion to:

```text
DASHI/Physics/Closure/YMConstructiveQFTFlagRouteReceipt.agda
```

Sprint 6 keeps the finite 43-step reading retracted.  Since the KP ratio at
the physical coupling expands rather than contracts, the first YM theorem
target must be continuum-uniform:

```text
YMBalabanContinuumLimit
```

The target requires, for every sufficiently small initial cutoff, a selected
scale where the strict Balaban seed inequality is crossed, followed by uniform
post-seed contraction and leakage control as the initial cutoff tends to zero.

## Corrected YM Chain

```text
YMBalabanContinuumLimit
-> HyperbolicShimuraToEuclideanUniversality
-> SelfAdjointYangMillsHamiltonian
-> MassGapSurvivesContinuumLimit
-> OSWightmanReconstruction
-> Nontrivial4DSU3YangMills
-> clayYangMillsPromoted = true
```

## Boundary

This receipt records the constructive-QFT flag route only.  It does not prove
continuum-uniform Balaban control, Shimura-flat universality, self-adjointness,
mass-gap survival, OS/Wightman reconstruction, nontriviality, or Clay
Yang-Mills promotion.
