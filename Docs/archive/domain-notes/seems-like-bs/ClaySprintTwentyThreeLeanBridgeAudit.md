# Clay Sprint 23 Lean-Bridge / Audit Receipt

Sprint 23 consumes Sprint 22 and records the next formalisation layer.
It does not claim a Clay proof.

## Gate3

The pruned fill-distance power law remains the closest positive support lane:

```text
h_pruned(J) <= C / J^alpha
alpha = 0.92
C ~= 0.07549
```

The power-law arithmetic target is:

```text
alpha > 0
=> C / J^alpha -> 0
=> cumulative pruned density
```

Open gates:

```text
PrunedPowerLawToCumulativeDensity
MoscoRecoveryFromPrunedUnionDensity
Gate3MoscoNoPollutionTransfer
```

## Navier-Stokes

The dynamic braid criterion remains:

```text
r * sqrt(2) < 1
```

The new audit surface is the physical bridge:

```text
Q_K =
  |PhysicalShellStretching_K|
  / (2^(K/2) * DissipationShell_K)
```

The route only matters if:

```text
Q_K <= C * R_K
```

where:

```text
R_K =
  unbalanced expansive trit-braid transitions
  / admissible trit-braid transitions
```

Open gates:

```text
BraidResidue369AnalyticFunctional
BraidResidueControlsPhysicalStretching
QKControlledByResidueRatio
DynamicResidueDecayBelowCritical
```

Counting transitions does not solve NS unless the residue controls physical
vortex stretching and actual NS dynamics deterministically depletes it below
the critical ratio.

## Yang-Mills

The useful contraction target remains:

```text
rho <= 0.90
beta_true >= 14.16373
```

Sprint 23 keeps the safe-scale budget from Sprint 22:

```text
k0 = 67
eta_67 ~= 0.9180
eta_100 ~= 5.3911
```

Open gates:

```text
NonperturbativeCorrectionBoundAtSafeScale
ContinuumUniformRhoBoundAtSafeScale
ContinuumUniformLeakageBound
```

## Lean Port Targets

The Lean-side theorem targets are useful support surfaces only:

```text
braid_threshold_closes
one_third_beats_half_derivative
fill_distance_power_law_goes_to_zero
Base369 carrier arithmetic support
```

They do not import external authority into Agda. They must be re-proved or
receipt-bound in DASHI Agda before any gate can consume them.

## Workers

1. Gate3 power-law to density port.
2. Gate3 Mosco recovery consumer.
3. NS residue functional and Q_K bridge.
4. NS dynamic ratio below critical.
5. YM safe-scale correction and leakage.
6. Lean-port governance and validation.

All Gate3, Navier-Stokes, Yang-Mills, and Clay promotion flags remain false.
