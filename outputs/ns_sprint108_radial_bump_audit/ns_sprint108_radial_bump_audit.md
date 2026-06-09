# NS Sprint 108 Radial Bump Function Construction Audit

- Contract: `ns_sprint108_radial_bump_audit`
- Agda path: `DASHI/Physics/Closure/NSSprint108RadialBumpFunctionConstruction.agda`
- Target present: `True`
- Fail closed: `True`
- Route decision: `FAIL_CLOSED_RADIAL_BUMP_FUNCTION_CONSTRUCTION`
- Promotion decision: `hold`
- Evidence audit passed: `True`
- Accepted source count: `0`
- Radial bump function construction decomposition ledger closed: `True`
- All subgates false: `True`
- Clay Navier-Stokes promoted: `False`

## Open Radial Bump Function Construction Subgates
- `SmoothCompactSupportWitness`
- `RadialProfileDefinition`
- `NonnegativeBumpWitness`
- `AnnularDifferenceBump`
- `NonCircularRadialBumpSource`

## Gate Results

| Gate | Expected | Actual | Passed | Status |
| --- | --- | --- | --- | --- |
| `radialBumpFunctionConstructionDecompositionLedgerClosed` | `true` | `true` | `True` | `PASS` |
| `smoothCompactSupportWitnessClosed` | `false` | `false` | `True` | `PASS` |
| `radialProfileDefinitionClosed` | `false` | `false` | `True` | `PASS` |
| `nonnegativeBumpWitnessClosed` | `false` | `false` | `True` | `PASS` |
| `annularDifferenceBumpClosed` | `false` | `false` | `True` | `PASS` |
| `nonCircularRadialBumpSourceClosed` | `false` | `false` | `True` | `PASS` |
| `radialBumpFunctionConstructionClosed` | `false` | `false` | `True` | `PASS` |
| `smoothDyadicCutoffPartitionClosed` | `false` | `false` | `True` | `PASS` |
| `littlewoodPaleyShellProjectorClosed` | `false` | `false` | `True` | `PASS` |
| `dyadicShellEnergyDensityClosed` | `false` | `false` | `True` | `PASS` |
| `highFrequencyConcentrationMeasureClosed` | `false` | `false` | `True` | `PASS` |
| `strainCompressionAtHighFrequencyConcentrationPointsClosed` | `false` | `false` | `True` | `PASS` |
| `signedLowModeFluxLowerBoundClosed` | `false` | `false` | `True` | `PASS` |
| `timeIntegratedFluxSurplusClosed` | `false` | `false` | `True` | `PASS` |
| `finiteKStarCollapseClosed` | `false` | `false` | `True` | `PASS` |
| `clayNavierStokesPromoted` | `false` | `false` | `True` | `PASS` |
| `failClosedRadialBumpFunctionConstructionDecomposition` | `true` | `true` | `True` | `PASS` |
| `SmoothCompactSupportWitness` | `name, open constructor, and false closure flag` | `recorded, open constructor, and false` | `True` | `PASS` |
| `RadialProfileDefinition` | `name, open constructor, and false closure flag` | `recorded, open constructor, and false` | `True` | `PASS` |
| `NonnegativeBumpWitness` | `name, open constructor, and false closure flag` | `recorded, open constructor, and false` | `True` | `PASS` |
| `AnnularDifferenceBump` | `name, open constructor, and false closure flag` | `recorded, open constructor, and false` | `True` | `PASS` |
| `NonCircularRadialBumpSource` | `name, open constructor, and false closure flag` | `recorded, open constructor, and false` | `True` | `PASS` |
| `required_anchors` | `all present` | `all present` | `True` | `PASS` |
| `forbidden_markers` | `none` | `none` | `True` | `PASS` |
