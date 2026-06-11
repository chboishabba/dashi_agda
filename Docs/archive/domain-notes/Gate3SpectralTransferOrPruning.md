# Gate3 Spectral Transfer Or Pruning

This document is the reader-facing companion to:

```text
DASHI/Physics/Closure/Gate3SpectralTransferOrPruningReceipt.agda
```

Sprint 6 corrects the nearest Gate3 blocker.  The p-adic carrier frame is
essentially closed inside `L2(Q_p)`: the Kozyrev/BT Gram is tight with
`A_N = 1`, and the model spread values remain strongly below the PAWOTG
collapse threshold.  That does not automatically prove a continuum frame lower
bound.

The observed Archimedean Gram collapse around finite cutoff means the live
lemma is now:

```text
SSPIsometricEmbeddingOrSpectralTransfer
```

not merely:

```text
SSPFrameCarrierEqualsOKTensorZ3
```

## Corrected Gate3 Chain

```text
SSPFrameCarrierEqualsOKTensorZ3
-> BTIdentityGramUniformFrame in L2(Q_p)
-> SSPIsometricEmbeddingOrSpectralTransfer
-> UniformContinuumFrameLowerBound
-> Gate3MoscoNoPollutionTransfer
-> gate3Closed = true
```

Because the direct unweighted Archimedean embedding has near-duplicate images,
the receipt records two allowed transfer routes:

```text
WeightedSSPSpectralTransfer
PrunedSSPSpectralTransfer
```

The pruned route is the first computable path: find a representative subframe
with admissible density and a uniform lower Gram eigenvalue after the
continuum map.

## Boundary

This is a support-flag route, not a Clay theorem.  The receipt records that the
p-adic frame is closed and the Archimedean collision has been observed, but it
does not prove weighted transfer, pruned transfer, Mosco convergence, no
spectral pollution, or Gate3 closure.
