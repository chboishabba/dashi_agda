# NS Sprint 114 Thin-Core Reconnection Audit

- Contract: `ns_sprint114_thin_core_reconnection_audit`
- Agda path: `DASHI/Physics/Closure/NSSprint114ThinCoreCrowReconnectionWindow.agda`
- Target present: `True`
- Route decision: `THIN_CORE_RECONNECTION_LEDGER_CLOSED_FAIL_CLOSED_NO_CLAY_PROMOTION`
- Promotion decision: `hold`
- Promotion hold: `True`
- Evidence audit passed: `True`
- Ledger coherent fail-closed: `True`
- Required true flags: `True`
- Downstream flags false: `True`
- Sprint114 thin-core correction ledger closed: `True`
- Sprint112 thick-core condition corrected: `True`
- Thin-core Crow dominance regime closed: `True`
- Elliptic backreaction bound closed: `True`
- Clay Navier-Stokes promoted: `False`

## Required Strings

| String | Present |
| --- | --- |
| `thin-core` | `True` |
| `Crow reconnection` | `True` |
| `elliptic` | `True` |
| `ReconnectionWindowLowerBound / finite flux surplus` | `True` |

## Gate Results

| Gate | Expected | Actual | Passed | Status |
| --- | --- | --- | --- | --- |
| `sprint114ThinCoreCorrectionLedgerClosed` | `true` | `true` | `True` | `PASS` |
| `sprint112ThickCoreConditionCorrected` | `true` | `true` | `True` | `PASS` |
| `thinCoreCrowDominanceRegimeClosed` | `true` | `true` | `True` | `PASS` |
| `ellipticBackreactionBoundClosed` | `true` | `true` | `True` | `PASS` |
| `reconnectionWindowLowerBoundClosed` | `false` | `false` | `True` | `PASS` |
| `viscousDecayWindowClosed` | `false` | `false` | `True` | `PASS` |
| `nonlinearDeformationControlClosed` | `false` | `false` | `True` | `PASS` |
| `positiveFluxAccumulationWindowClosed` | `false` | `false` | `True` | `PASS` |
| `finiteTimeFluxSurplusFromCrowDominance` | `false` | `false` | `True` | `PASS` |
| `finiteKStarCollapseClosed` | `false` | `false` | `True` | `PASS` |
| `strainCompressionAtHighFrequencyConcentrationPointsClosed` | `false` | `false` | `True` | `PASS` |
| `clayNavierStokesPromoted` | `false` | `false` | `True` | `PASS` |
| `keyword_true:sprint114ThinCoreCorrectionLedgerClosed` | `true` | `true` | `True` | `PASS` |
| `keyword_true:thinCoreCrowDominanceRegimeClosed` | `true` | `true` | `True` | `PASS` |
| `keyword_true:ellipticBackreactionBoundClosed` | `true` | `true` | `True` | `PASS` |
| `required_string:thin-core` | `present` | `present` | `True` | `PASS` |
| `required_string:Crow reconnection` | `present` | `present` | `True` | `PASS` |
| `required_string:elliptic` | `present` | `present` | `True` | `PASS` |
| `required_string:ReconnectionWindowLowerBound / finite flux surplus` | `present` | `present` | `True` | `PASS` |
| `target_module` | `DASHI/Physics/Closure/NSSprint114ThinCoreCrowReconnectionWindow.agda` | `present` | `True` | `PASS` |
| `route` | `THIN_CORE_RECONNECTION_LEDGER_CLOSED_FAIL_CLOSED_NO_CLAY_PROMOTION` | `THIN_CORE_RECONNECTION_LEDGER_CLOSED_FAIL_CLOSED_NO_CLAY_PROMOTION` | `True` | `PASS` |
| `required_anchors` | `all present` | `all present` | `True` | `PASS` |
| `forbidden_markers` | `none` | `none` | `True` | `PASS` |
