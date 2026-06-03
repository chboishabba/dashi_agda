# YM One-Loop Balaban Steps 1-3

Companion to:

```text
DASHI/Physics/Closure/YMOneLoopBalaban1to3Receipt.agda
```

Sprint 7 records what the one-loop diagnostic can honestly complete for the
Balaban target.

```text
1. Scale selection:
   k0 ~= 42.2 crosses the strict seed in the one-loop model.

2. Post-seed contraction:
   q(k=43) ~= 0.973 and q(k=50) ~= 0.757 in the one-loop model.

3. Leakage summability:
   the one-loop geometric leakage sum is about 10^-37.

4. Continuum uniformity:
   open; this is the nonperturbative Balaban programme.
```

The one-loop calculation is useful because it sharpens the scale of the
problem.  It is not a substitute for constructive QFT control.  The live YM
blocker remains:

```text
NonperturbativeContinuumUniformity
```

## Updated YM Route

```text
NonperturbativeContinuumUniformity
-> YMBalabanContinuumLimit
-> HyperbolicShimuraToEuclideanUniversality
-> SelfAdjointYangMillsHamiltonian
-> MassGapSurvivesContinuumLimit
-> OSWightmanReconstruction
-> Nontrivial4DSU3YangMills
-> clayYangMillsPromoted = true
```

## Boundary

The receipt records one-loop diagnostic success for steps 1-3 only.  It does
not prove nonperturbative Balaban transfer, continuum YM, mass-gap survival,
OS/Wightman reconstruction, nontriviality, or Clay YM.
