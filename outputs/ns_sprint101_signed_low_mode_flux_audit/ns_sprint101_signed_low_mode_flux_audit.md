# NS Sprint 101 Signed Low-Mode Flux Lower-Bound Audit

- Contract: `ns_sprint101_signed_low_mode_flux_audit`
- Surface: `NSSprint101 Sprint101 signed low-mode flux lower bound fail_closed Clay Navier-Stokes`
- Agda path: `DASHI/Physics/Closure/NSSprint101SignedLowModeFluxLowerBound.agda`
- Complete: `False`
- Fail closed: `True`
- Route decision: `FAIL_CLOSED_SIGNED_LOW_MODE_FLUX_LOWER_BOUND`
- Final decision: `FAIL_CLOSED_SIGNED_LOW_MODE_FLUX_LOWER_BOUND`
- Signed low-mode flux lower bound closed: `False`
- Time-integrated flux surplus closed: `False`
- Finite-time K-star collapse closed: `False`
- Clay Navier-Stokes promoted: `False`
- Accepted source count: `0`
- Evidence audit passed: `True`
- Forbidden marker count: `0`

## Missing Analytic Objects
- `SignedLowModeFluxLowerBound`
- `TriadicSignCoherence`
- `LowModeProjectionSignControl`
- `CancellationDefectBound`
- `PressureTransportSignAccounting`
- `NonCircularFluxSignSource`

## Required Anchors
- `NSSprint101SignedLowModeFluxLowerBound`
- `canonicalNSSprint101SignedLowModeFluxLowerBound`
- `requiredSignedLowModeFluxLowerBoundObjects`
- `SignedLowModeFluxLowerBound`
- `TriadicSignCoherence`
- `LowModeProjectionSignControl`
- `CancellationDefectBound`
- `PressureTransportSignAccounting`
- `NonCircularFluxSignSource`
- `MissingSignedLowModeFluxLowerBoundObject`
- `failClosedSignedLowModeFluxLowerBound`
- `signedLowModeFluxLowerBoundLedgerClosed`
- `signedLowModeFluxLowerBoundClosed`
- `timeIntegratedFluxSurplusClosed`
- `finiteTimeKStarCollapseClosed`
- `clayNavierStokesPromoted`

## Boolean Gates
- `signedLowModeFluxLowerBoundLedgerClosed` expected `True` actual `true` passed `True`
- `signedLowModeFluxLowerBoundClosed` expected `False` actual `false` passed `True`
- `timeIntegratedFluxSurplusClosed` expected `False` actual `false` passed `True`
- `finiteTimeKStarCollapseClosed` expected `False` actual `false` passed `True`
- `clayNavierStokesPromoted` expected `False` actual `false` passed `True`
- `failClosedSignedLowModeFluxLowerBound` expected `True` actual `true` passed `True`

## Source Results
- `DASHI/Physics/Closure/NSSprint101SignedLowModeFluxLowerBound.agda` present `True` status `PASS`

## Gate Results

| Gate | Expected | Actual | Passed | Status |
| --- | --- | --- | --- | --- |
| `signedLowModeFluxLowerBoundLedgerClosed` | `true` | `true` | `True` | `PASS` |
| `signedLowModeFluxLowerBoundClosed` | `false` | `false` | `True` | `PASS` |
| `timeIntegratedFluxSurplusClosed` | `false` | `false` | `True` | `PASS` |
| `finiteTimeKStarCollapseClosed` | `false` | `false` | `True` | `PASS` |
| `clayNavierStokesPromoted` | `false` | `false` | `True` | `PASS` |
| `failClosedSignedLowModeFluxLowerBound` | `true` | `true` | `True` | `PASS` |
| `SignedLowModeFluxLowerBound` | `recorded` | `present` | `True` | `PASS` |
| `TriadicSignCoherence` | `recorded` | `present` | `True` | `PASS` |
| `LowModeProjectionSignControl` | `recorded` | `present` | `True` | `PASS` |
| `CancellationDefectBound` | `recorded` | `present` | `True` | `PASS` |
| `PressureTransportSignAccounting` | `recorded` | `present` | `True` | `PASS` |
| `NonCircularFluxSignSource` | `recorded` | `present` | `True` | `PASS` |
| `required_anchors` | `all present` | `all present` | `True` | `PASS` |
| `forbidden_markers` | `none` | `none` | `True` | `PASS` |
