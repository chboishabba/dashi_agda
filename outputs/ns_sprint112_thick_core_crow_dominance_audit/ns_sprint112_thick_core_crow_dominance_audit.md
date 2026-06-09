# NS Sprint 112 Thick-Core Crow Dominance Audit

- Contract: `ns_sprint112_thick_core_crow_dominance_audit`
- Agda path: `DASHI/Physics/Closure/NSSprint112ThickCoreCrowDominanceRegime.agda`
- Target present: `True`
- Route decision: `THICK_CORE_CROW_DOMINANCE_REGIME_CLOSED_FAIL_CLOSED_NO_PROMOTION`
- Evidence audit passed: `True`
- Thick-core Crow dominance regime closed: `True`
- Downstream flags false: `True`
- Promotion flags false: `True`
- Clay Navier-Stokes promoted: `False`

## Required Strings

| String | Present |
| --- | --- |
| `Crow` | `True` |
| `elliptic` | `True` |
| `rate` | `True` |
| `rates` | `True` |
| `delta/b >= 1/2` | `True` |

## Gate Results

| Gate | Expected | Actual | Passed | Status |
| --- | --- | --- | --- | --- |
| `thickCoreCrowDominanceRegimeClosed` | `true` | `true` | `True` | `PASS` |
| `downstreamNavierStokesClosed` | `false` | `false` | `True` | `PASS` |
| `downstreamNSPromotion` | `false` | `false` | `True` | `PASS` |
| `downstreamPromotion` | `false` | `false` | `True` | `PASS` |
| `navierStokesPromotion` | `false` | `false` | `True` | `PASS` |
| `clayNavierStokesPromoted` | `false` | `false` | `True` | `PASS` |
| `required_string:Crow` | `present` | `present` | `True` | `PASS` |
| `required_string:elliptic` | `present` | `present` | `True` | `PASS` |
| `required_string:rate` | `present` | `present` | `True` | `PASS` |
| `required_string:rates` | `present` | `present` | `True` | `PASS` |
| `required_string:delta/b >= 1/2` | `present` | `present` | `True` | `PASS` |
| `target_module` | `DASHI/Physics/Closure/NSSprint112ThickCoreCrowDominanceRegime.agda` | `present` | `True` | `PASS` |
| `route` | `THICK_CORE_CROW_DOMINANCE_REGIME_CLOSED_FAIL_CLOSED_NO_PROMOTION` | `THICK_CORE_CROW_DOMINANCE_REGIME_CLOSED_FAIL_CLOSED_NO_PROMOTION` | `True` | `PASS` |
| `required_anchors` | `all present` | `all present` | `True` | `PASS` |
| `forbidden_markers` | `none` | `none` | `True` | `PASS` |
