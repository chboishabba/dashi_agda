# Clay Kernel Reduction

This note answers what the current DASHI programme buys for Clay after the
latest compression. The answer is narrower than a proof and more useful than
another broad roadmap: the repo now has three killable kernel routes.

## Kernel Compression

The Clay-facing content is:

```text
YM:
  Does DASHI give a real polymer/KP/Balaban route?

NS:
  Can the Bernoulli danger-shell pressure bound prove a non-circular
  H^{11/8} a priori estimate?

Gate3:
  Can the physical 3D SSP/Hecke embedding prove a uniform frame lower bound?
```

The shared gain is fault localisation. Each lane has one lemma whose failure
stalls the route, and each lemma has a finite computational kill-test.

## Yang-Mills

The corrected computation changes the YM value proposition.  The direct
`T7A` KP series is proved, but it is not the best counting bound:

```text
naive BT count:
  beta* ~= 8.04

connected-animal count:
  beta* ~= 9.593637
  KP-only gap from beta = 6: 3.593637

optimal min(count, T7A):
  beta* ~= 8.86

direct T7A count:
  beta* ~= 16.56
  Balaban gap from beta = 6: 10.56
```

Two additional KP-margin conventions must remain visible in Balaban-facing
statements:

```text
p=7 BT-tree convergence threshold:
  beta* ~= 10.13086
  gap from beta = 6: 4.13086

stricter p=7 KP activity-absorption margin:
  exact target: beta*c_min-a>log(2p)
  robust numeric target: beta_eff >= 13.7
```

So `T7A` is worse as a count replacement.  Its useful role is narrower:
`T7A(d)` is positive, computable, and eventually smaller than the BT counts,
but depths 1-4 dominate the threshold.  The corrected route is:

```text
ConnectedAnimalBound
-> ConnectedAnimalBalabanTransfer
-> OS/Wightman reconstruction
-> Clay YM
```

The T7-specific improvement route is still open:

```text
T7APerPolymerActivitySuppression:
  |z(Gamma)| <= (T7A(d) / (d * p^(d-1))) * exp(-beta*c_min*d)
```

That is the corrected `T7ActivityIdentificationLemma`.  Proving it would let
T7A act as activity suppression rather than polymer counting.  Without that
lemma, the best computable YM KP path is the connected-animal threshold
`9.593637`,
not the direct T7A threshold `16.56`.

## Navier-Stokes

The NS route is:

```text
ShellFluxBalance
-> DangerShellMaximumPrinciple
-> KStarDriftBarrier
-> BernoulliBandToH118
-> H118Continuation
-> smooth global existence
```

The hard lemma is `DangerShellMaximumPrinciple`: at the first danger shell,
incoming flux must be dominated by local dissipation without importing
Serrin, BKM, global regularity, or an `H^{1/2}` assumption.

This buys a precise non-circularity test. The question is not whether a
Leray-type bound exists; it is whether the first pressure-danger shell has
`dP_K/dt <= 0` from local shell bookkeeping alone.

## Gate3

Gate3 must avoid the arithmetic confusion:

```text
7+7+1 = semantic atom/frame grammar.
Q(sqrt(-7)) CM split table = 5 split + 9 inert + 1 ramified, with p71 split.
```

The frame route is therefore amplitude/phase/sign, not literal
split/inert/71 arithmetic. The current kernel is:

```text
OneDPhaseBlindNoGo
ThreeDPhaseSectorOverlap
FrameSymbolLowerBound
PhaseCompleteSymbolPositivity
PhaseBlindSymbolDegeneracy
NoSpectralPollution
```

The useful Gate3 computational test is the smallest 3D overlapping
phase-sector dictionary. The desired result is:

```text
phaseBlind:     lambda_min ~= 0
phaseComplete: lambda_min > 0
```

If the phase-complete Gram still has near-zero modes, MirrorB7 is not enough.

## Shared Pressure Kernel

The reusable abstraction is a scale-pressure system:

```text
Pressure(next k) <= q * Pressure(k) + Creation(k) - Absorption(k)
q < 1
Absorption >= Creation
summable leakage
```

Then `ScalePressureBound` would give uniform pressure control. The same shape
covers:

```text
YM:    polymer activity vs RG contraction and new polymer creation
NS:    unresolved shell pressure vs viscosity and nonlinear cascade flux
Gate3: frame defect vs lower-bound recovery and cutoff tail error
```

## Six Worker Kill-Tests

1. `W-YM-Count`: compare connected-animal, naive BT, optimal-min, and direct
   `T7A` KP thresholds and keep `9.593637` as the standard computable
   KP-convergence route.
2. `W-YM-Activity`: prove or refute small-depth per-polymer T7A activity
   suppression, especially depths 1-4.
3. `W-NS-Danger`: compute `dP_K/dt = incomingFlux - dissipation` at the first
   danger shell in synthetic shell models.
4. `W-G3-Gram`: compute phase-blind and phase-complete Gram eigenvalues in
   the smallest 3D overlapping phase-sector dictionary.
5. `W-Pressure`: formalize the shared `ScalePressureSystem` and identify
   which lane has the strongest existing absorption/creation data.
6. `W-Gov`: keep every route fail-closed until its kernel lemma is actually
   proved.

## Promotion Boundary

This reduction proves no Clay theorem, no Yang-Mills mass gap, no
Navier-Stokes regularity theorem, no Gate3 spectral gap, no gravity
prediction, no W4 mass calibration, and no terminal programme claim.
