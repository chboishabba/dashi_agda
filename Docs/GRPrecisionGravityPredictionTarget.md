# GR Precision Gravity Prediction Target

Source of record:

`DASHI/Physics/Closure/GRPrecisionGravityPredictionTargetReceipt.agda`

This target sits above the executable weak-field baseline in
`GRWeakFieldPredictionReceipt`.  It records what must be proved before DASHI
can claim an internal Earth/solar-system gravity prediction or a
higher-curvature coefficient prediction.

The current gravity frontier source of record is also:

```text
DASHI/Physics/Closure/GravityVladimirovFrameReceipt.agda
```

It keeps the lane suspended: Vladimirov spectrum known on the p-adic side, the
3D Archimedean image frame theorem open at
`sigma_crit_3D(p=3) ~= 0.3025113508228815`, and Schwarzschild/W4 calibration
blocked.  The precision target cannot move until that pre-bridge surface is
advanced.

## Current Executable Surface

The repo can run the external GR baseline diagnostic:

`scripts/run_solar_weak_field_gr_baseline_diagnostic.py`

It records standard weak-field GR comparison values such as Mercury
perihelion, solar-limb light deflection, Shapiro delay, and gravitational
redshift.  These are authority-backed baselines, not carrier-derived
predictions.

## Precision Target

The higher-precision goal is to derive the effective action coefficients:

```text
S_eff = integral sqrt(-g)
  ((R - 2 Lambda)/(16 pi G)
   + alpha1 R^2
   + alpha2 R_munu R^munu
   + ...)
```

The carrier must predict `alpha1`, `alpha2`, and any matter-coupling correction
coefficients tightly enough to compare against precision gravity benchmarks.

## Blockers

| Gate | Existing repo surface | Current fail-closed state |
|---|---|---|
| Physical mass sourcing | `Candidate256PhysicalCalibrationExternalReceipt` and `W4MatterStressEnergyInterfaceReceipt` | Candidate256/W4 authority remains missing; no matter field or stress-energy tensor is constructed. |
| Radial valuation and Schwarzschild match | `SchwarzschildLimitCandidate` | First missing primitive is `missingRadialValuation`; weak-field Newtonian potential and metric match remain unproved. |
| Discrete-to-smooth Einstein limit | `DiscreteToSmoothEinsteinLimitReceipt` | First missing proof is `missingDiscreteToSmoothCurvatureConvergence`; Ricci identification and stress-energy convergence remain open. |
| Higher-curvature coefficient derivation | `GRPrecisionGravityPredictionTargetReceipt` | `carrierHigherCurvatureCoefficientsDerived = false`. |

## Diagnostic Budget

The new diagnostic script is:

`scripts/gr_precision_higher_curvature_budget.py`

It writes:

`scripts/data/outputs/gr_precision_higher_curvature_budget.json`

`scripts/data/outputs/gr_precision_higher_curvature_budget.csv`

The model is deliberately simple:

```text
fractional_correction ~= |alpha| / L^2
```

For a benchmark bound `b` at length scale `L`, the target coefficient scale is:

```text
|alpha| <= b L^2
sqrt(|alpha|) <= sqrt(b) L
```

Generated benchmark rows:

| Benchmark | sqrt alpha bound | alpha bound | Status |
|---|---:|---:|---|
| Cassini-style PPN gamma, solar radius scale | `3.336460e+06 m` | `1.113197e+13 m^2` | `NO_PROMOTION` |
| Earth surface gravity fractional target | `2.014687e+02 m` | `4.058964e+04 m^2` | `NO_PROMOTION` |
| MICROSCOPE-style WEP proxy, Earth-Moon scale | `4.382834e+01 m` | `1.920924e+03 m^2` | `NO_PROMOTION` |

These are external benchmark budgets.  They are not derived carrier
coefficients.

## Promotion Fence

The canonical receipt records:

```text
carrierEarthGravityPredictionDerived = false
carrierHigherCurvatureCoefficientsDerived = false
carrierInternalPrediction = false
precisionGravityPredictionPromoted = false
continuumGRPromoted = false
promotions = []
```

The next mathematical work is to inhabit the calibration, W4 stress-energy,
Schwarzschild limit, and discrete-to-smooth Ricci convergence surfaces.  Only
after those are proved can the carrier attempt an internal alpha-coefficient
prediction.
