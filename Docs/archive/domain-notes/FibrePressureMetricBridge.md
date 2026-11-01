# Fibre Pressure Metric Bridge

Date: `2026-05-19`
Status: theorem-thin, candidate-only

`DASHI/Metric/FibrePressureMetricBridge.agda` connects the existing arithmetic
pressure surfaces to observation-transport gating:

```text
prime fibre
  -> weighted local pressure
  -> weighted support residual
  -> global residual metric
  -> transport admissibility gate
  -> candidate-only promotion boundary
```

## Formal Surface

The canonical arithmetic instance uses:

- `SSP` as the fibre carrier;
- `Int` as the state carrier;
- `weight`, `weightedDeltaAt`, and `weightedSupportAt` for local fibre weight,
  pressure, and residual;
- `weightedPressure` and `weightedSupport` for the residual metric and budget;
- `totalPressure` plus `totalPressure≡wallPressure` for compatibility with the
  existing wall-filtered global pressure surface.

The bridge reuses the existing theorem:

```text
weightedPressure x y <= weightedSupport x y
```

It also exposes an agreement-residual socket over the existing prefix
ultrametric in `DASHI/Metric/AgreementUltrametric.agda`.

## Promotion Discipline

`TransportResidualGate` only says that a selected residual budget can be used as
an admissibility gate. `FibrePressurePromotionGate` is intentionally
candidate-only in the canonical inhabitant:

- calibration receipt: missing;
- metric-completeness receipt: missing;
- optimizer receipt: missing;
- promoted: `false`.

This bridge does not prove every domain metric complete, construct a global
optimizer, or calibrate universal thresholds.

