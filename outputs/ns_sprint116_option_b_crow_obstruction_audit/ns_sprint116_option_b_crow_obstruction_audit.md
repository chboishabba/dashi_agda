# NS Sprint 116 Option B Crow Obstruction Audit

- Contract: `ns_sprint116_option_b_crow_obstruction_audit`
- Agda path: `DASHI/Physics/Closure/NSSprint116OptionBCrowObstruction.agda`
- Target present: `True`
- Route decision: `OPTION_B_CROW_OBSTRUCTION_LEDGER_CLOSED_FAIL_CLOSED_ALTERNATIVE_ROUTE_OPEN`
- Promotion decision: `hold`
- Promotion hold: `True`
- Evidence audit passed: `True`
- Ledger coherent fail-closed: `True`
- Required true flags: `True`
- Downstream flags false: `True`
- Sprint116 Option B Crow obstruction ledger closed: `True`
- Sprint115 flux budget imported: `True`
- Thin-core Crow scaling law recorded: `True`
- Thin-core Crow route obstructed: `True`
- Option B Crow lane closed: `True`
- Axisymmetric swirl route open: `True`
- Burgers vortex route open: `True`
- Clay promoted: `False`

## Required Strings

| String | Present |
| --- | --- |
| `Sprint 116 Option B thin-core Crow obstruction.` | `True` |
| `This receipt imports the Sprint115 reconnection flux budget and records` | `True` |
| `that the thin-core Crow Option B lane is closed by the budget scaling.` | `True` |
| `FluxBudget / E0 ~ (delta / b)^2 / log(b / delta)` | `True` |
| `Option B thin-core Crow route is obstructed` | `True` |
| `axisymmetric with swirl remains open` | `True` |
| `Burgers vortex concentration remains open` | `True` |
| `Sprint116 records the Option B obstruction without closing finite KStar collapse, the blowup bridge, or the Clay assembly.` | `True` |

## Gate Results

| Gate | Expected | Actual | Passed | Status |
| --- | --- | --- | --- | --- |
| `sprint116OptionBCrowObstructionLedgerClosed` | `true` | `true` | `True` | `PASS` |
| `sprint115FluxBudgetImported` | `true` | `true` | `True` | `PASS` |
| `thinCoreCrowScalingLawRecorded` | `true` | `true` | `True` | `PASS` |
| `thinCoreCrowRouteObstructed` | `true` | `true` | `True` | `PASS` |
| `optionBCrowLaneClosed` | `true` | `true` | `True` | `PASS` |
| `axisymmetricSwirlRouteOpen` | `true` | `true` | `True` | `PASS` |
| `burgersVortexRouteOpen` | `true` | `true` | `True` | `PASS` |
| `finiteKStarCollapseClosed` | `false` | `false` | `True` | `PASS` |
| `blowupCriterionBridgeClosed` | `false` | `false` | `True` | `PASS` |
| `navierStokesClayAssemblyClosed` | `false` | `false` | `True` | `PASS` |
| `clayNavierStokesPromoted` | `false` | `false` | `True` | `PASS` |
| `keyword_true:sprint116OptionBCrowObstructionLedgerClosed` | `true` | `true` | `True` | `PASS` |
| `keyword_true:sprint115FluxBudgetImported` | `true` | `true` | `True` | `PASS` |
| `keyword_true:thinCoreCrowScalingLawRecorded` | `true` | `true` | `True` | `PASS` |
| `keyword_true:thinCoreCrowRouteObstructed` | `true` | `true` | `True` | `PASS` |
| `keyword_true:optionBCrowLaneClosed` | `true` | `true` | `True` | `PASS` |
| `keyword_true:axisymmetricSwirlRouteOpen` | `true` | `true` | `True` | `PASS` |
| `keyword_true:burgersVortexRouteOpen` | `true` | `true` | `True` | `PASS` |
| `keyword_false:finiteKStarCollapseClosed` | `false` | `false` | `True` | `PASS` |
| `keyword_false:blowupCriterionBridgeClosed` | `false` | `false` | `True` | `PASS` |
| `keyword_false:navierStokesClayAssemblyClosed` | `false` | `false` | `True` | `PASS` |
| `keyword_false:clayNavierStokesPromoted` | `false` | `false` | `True` | `PASS` |
| `required_string:Sprint 116 Option B thin-core Crow obstruction.` | `present` | `present` | `True` | `PASS` |
| `required_string:This receipt imports the Sprint115 reconnection flux budget and records` | `present` | `present` | `True` | `PASS` |
| `required_string:that the thin-core Crow Option B lane is closed by the budget scaling.` | `present` | `present` | `True` | `PASS` |
| `required_string:FluxBudget / E0 ~ (delta / b)^2 / log(b / delta)` | `present` | `present` | `True` | `PASS` |
| `required_string:Option B thin-core Crow route is obstructed` | `present` | `present` | `True` | `PASS` |
| `required_string:axisymmetric with swirl remains open` | `present` | `present` | `True` | `PASS` |
| `required_string:Burgers vortex concentration remains open` | `present` | `present` | `True` | `PASS` |
| `required_string:Sprint116 records the Option B obstruction without closing finite KStar collapse, the blowup bridge, or the Clay assembly.` | `present` | `present` | `True` | `PASS` |
| `target_module` | `DASHI/Physics/Closure/NSSprint116OptionBCrowObstruction.agda` | `present` | `True` | `PASS` |
| `route` | `OPTION_B_CROW_OBSTRUCTION_LEDGER_CLOSED_FAIL_CLOSED_ALTERNATIVE_ROUTE_OPEN` | `OPTION_B_CROW_OBSTRUCTION_LEDGER_CLOSED_FAIL_CLOSED_ALTERNATIVE_ROUTE_OPEN` | `True` | `PASS` |
| `required_anchors` | `all present` | `all present` | `True` | `PASS` |
| `forbidden_markers` | `none` | `none` | `True` | `PASS` |
