# Pruned SSP Spectral Transfer

Companion to:

```text
DASHI/Physics/Closure/PrunedSSPSpectralTransferReceipt.agda
```

Sprint 7 changes the Gate3 state.  The weighted embedding route fails across
the tested power-law exponents because the collapse is angular, not radial.
The greedy pruning route does produce a finite Archimedean frame:

```text
retained atoms:        55 of 120
retention rate:        0.458
lower frame bound:     A_N >= 0.010 for N <= 55
levels represented:    all six levels 1-4
level 4 retention:     6.9 percent
```

This is a real support advance, but it is not Gate3 closure.  Mosco/no-pollution
transfer needs the pruned atoms to span a dense continuum subspace.  The new
Gate3 blocker is therefore:

```text
AdmissibleDensityThreshold
```

## Updated Gate3 Route

```text
PrunedSSPSpectralTransfer at finite cutoff
-> AdmissibleDensityThreshold
-> UniformContinuumFrameLowerBound
-> Gate3MoscoNoPollutionTransfer
-> gate3Closed = true
```

## Boundary

The receipt proves only the ledger facts for the finite pruned frame and the
weighted-route failure.  It does not prove admissible density, Mosco transfer,
no spectral pollution, Gate3 closure, or Clay.
