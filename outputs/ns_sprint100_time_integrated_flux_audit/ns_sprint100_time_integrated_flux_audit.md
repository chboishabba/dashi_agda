# NS Sprint 100 Time-Integrated Flux Surplus Audit

- Contract: `ns_sprint100_time_integrated_flux_audit`
- Surface: `NSSprint100 Sprint100 time-integrated flux surplus fail_closed Clay Navier-Stokes`
- Agda path: `DASHI/Physics/Closure/NSSprint100TimeIntegratedFluxSurplus.agda`
- Complete: `False`
- Fail closed: `True`
- Route decision: `FAIL_CLOSED_TIME_INTEGRATED_FLUX_SURPLUS`
- Final decision: `FAIL_CLOSED_TIME_INTEGRATED_FLUX_SURPLUS`
- Time-integrated flux surplus closed: `False`
- Residence time against viscosity closed: `False`
- Finite-time K-star collapse closed: `False`
- Clay Navier-Stokes promoted: `False`
- Accepted source count: `0`
- Evidence audit passed: `True`
- Forbidden marker count: `0`

## Missing Analytic Objects
- `SignedLowModeFluxLowerBound`
- `FluxDissipationBalance`
- `PositiveSurplusWindow`
- `LerayEnergyFluxBudget`
- `NonCircularSurplusSource`

## Required Anchors
- `NSSprint100TimeIntegratedFluxSurplus`
- `canonicalNSSprint100TimeIntegratedFluxSurplus`
- `requiredTimeIntegratedFluxSurplusObjects`
- `TimeIntegratedFluxSurplus`
- `SignedLowModeFluxLowerBound`
- `FluxDissipationBalance`
- `PositiveSurplusWindow`
- `LerayEnergyFluxBudget`
- `NonCircularSurplusSource`
- `MissingTimeIntegratedFluxSurplusObject`
- `failClosedTimeIntegratedFluxSurplus`
- `timeIntegratedFluxSurplusLedgerClosed`
- `timeIntegratedFluxSurplusClosed`
- `residenceTimeAgainstViscosityClosed`
- `finiteTimeKStarCollapseClosed`
- `clayNavierStokesPromoted`

## Boolean Gates
- `timeIntegratedFluxSurplusLedgerClosed` expected `True` actual `true` passed `True`
- `timeIntegratedFluxSurplusClosed` expected `False` actual `false` passed `True`
- `residenceTimeAgainstViscosityClosed` expected `False` actual `false` passed `True`
- `finiteTimeKStarCollapseClosed` expected `False` actual `false` passed `True`
- `clayNavierStokesPromoted` expected `False` actual `false` passed `True`
- `failClosedTimeIntegratedFluxSurplus` expected `True` actual `true` passed `True`

## Source Results
- `DASHI/Physics/Closure/NSSprint100TimeIntegratedFluxSurplus.agda` present `True` status `PASS`

## Gate Results

| Gate | Expected | Actual | Passed | Status |
| --- | --- | --- | --- | --- |
| `timeIntegratedFluxSurplusLedgerClosed` | `true` | `true` | `True` | `PASS` |
| `timeIntegratedFluxSurplusClosed` | `false` | `false` | `True` | `PASS` |
| `residenceTimeAgainstViscosityClosed` | `false` | `false` | `True` | `PASS` |
| `finiteTimeKStarCollapseClosed` | `false` | `false` | `True` | `PASS` |
| `clayNavierStokesPromoted` | `false` | `false` | `True` | `PASS` |
| `failClosedTimeIntegratedFluxSurplus` | `true` | `true` | `True` | `PASS` |
| `SignedLowModeFluxLowerBound` | `recorded` | `present` | `True` | `PASS` |
| `FluxDissipationBalance` | `recorded` | `present` | `True` | `PASS` |
| `PositiveSurplusWindow` | `recorded` | `present` | `True` | `PASS` |
| `LerayEnergyFluxBudget` | `recorded` | `present` | `True` | `PASS` |
| `NonCircularSurplusSource` | `recorded` | `present` | `True` | `PASS` |
| `required_anchors` | `all present` | `all present` | `True` | `PASS` |
| `forbidden_markers` | `none` | `none` | `True` | `PASS` |
