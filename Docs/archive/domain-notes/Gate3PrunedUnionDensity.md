# Gate3 Pruned Union Density Receipt

Sprint 10 discharges the Gate3 pruned-union density blocker.  Single-level
Nyquist remains blocked, but the union of pruned levels is dense: the
`O_K` argument/coset map is dense in `S1`, the cumulative fill distance
decays at the recorded `1/J` scale, and the pruned union is dense in angular
`L2`.

The live support path is:

```text
cumulativeFillDistanceGoesToZero ✓
→ PrunedUnionTrigonometricDensity ✓
→ PrunedFrameDenseInHContinuum ✓
→ PrunedSSPSpectralTransfer
→ Gate3MoscoNoPollutionTransfer
→ gate3Closed
```

The recorded proof route is algebraic/functional:

- `OKCosetsDenseInS1`
- `CumulativeFillDistanceGoesToZero`
- `PrunedUnionDenseInAngularL2`

It does not prove the Mosco recovery sequence or no-spectral-pollution
transfer.  Gate3 remains false until those transfer steps are inhabited.
