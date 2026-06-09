# Clay Sprint Seventy Two YM Legacy Mixed-Plaquette Residual Audit

Sprint 72 records a legacy mixed-plaquette residual fallback audit, this local
documentation note, and the executable absorption audit:

```text
scripts/ym_sprint72_mixed_plaquette_absorption_audit.py
```

## Sprint 70 Legacy Blocker

Sprint 70's legacy correction-bucket accounting established that the default
direct leakage route blocks crude `BoundaryCorrectionSmall`.

```text
q = 0.23178189475262734
fourQ = 0.9271275790105094
default c = 0.3592814371257485
```

The default full-residual correction is too large for the direct per-face
leakage route. Sprint 71 corrects the active bookkeeping by treating mixed
temporal plaquettes as transfer-matrix face action. Sprint 72 records the
fallback question: if any contribution remains outside that face action, how
small must the residual be?

## Legacy Fallback Target

The residual fallback target stack is:

```text
MixedPlaquetteDecomposition
MixedPlaquettesAbsorbIntoFaceActionWithoutEntropyCost
ResidualLeakageBound
TenPercentResidualLeakageClosesKP
```

The intended fallback shape is that any non-face-action remainder decomposes
into an absorbed part plus a residual. The absorbed part must not introduce an
independent entropy cost. The residual must then be bounded tightly enough for
the anisotropic KP arithmetic.

## Residual Arithmetic

Recorded constants:

```text
strict max residual fraction > 0.1073164020
safe residual fraction = 0.10
safe effective_total_leakage_times_4q = 0.994944290301034
```

The ten-percent residual fraction is the safe target. The current maximum
residual fraction is above that target, so the receipt records the target and
the arithmetic boundary rather than a proved absorption theorem.

## Audit Results

Generated outputs:

```text
outputs/sprint72_ym_mixed_plaquette_absorption/
outputs/sprint72_ym_mixed_plaquette_absorption_residual10/
outputs/sprint72_ym_mixed_plaquette_absorption_residual20/
```

Default face absorption:

```text
residual_fraction = 0.0
effective_total_leakage_factor = 1.0
effective_total_leakage_times_4q = 0.9271275790105094
route_decision = MIXED_PLAQUETTE_ABSORPTION_CONFIRMED
```

Manual ten-percent residual:

```text
residual_fraction = 0.10
absorption_fraction = 0.90
effective_total_leakage_factor = 1.0731471189357813
effective_total_leakage_times_4q = 0.994944290301034
route_decision = RESIDUAL_LEAKAGE_BELOW_10_PERCENT_CONFIRMED
```

Manual twenty-percent residual:

```text
residual_fraction = 0.20
absorption_fraction = 0.80
effective_total_leakage_factor = 1.1488759008928249
effective_total_leakage_times_4q = 1.0651545325782825
route_decision = MIXED_PLAQUETTES_TRUE_LEAKAGE_REBLOCKS_KP
```

This makes the fork quantitative: absorb all mixed plaquettes as transfer
matrix face action, or prove that no more than ten percent of the legacy mixed
correction remains true entropy-producing leakage.

## Governance

All promotion flags remain false.

```text
Corrected mixed-plaquette transfer-matrix bookkeeping = handled by Sprint 71
Legacy residual fallback = diagnostic only
ResidualLeakageBound = false
TenPercentResidualLeakageClosesKP = false
Clay/YM promotion = false
```

This receipt does not prove KP closure, lattice mass gap, continuum transfer,
OS/Wightman reconstruction, mass gap survival, or Clay Yang-Mills.
