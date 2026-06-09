# NS Sprint 115 Reconnection Flux-Budget Audit

- Contract: `ns_sprint115_reconnection_flux_budget_audit`
- Agda path: `DASHI/Physics/Closure/NSSprint115ReconnectionFluxBudget.agda`
- Target present: `True`
- Route decision: `RECONNECTION_FLUX_BUDGET_LEDGER_CLOSED_FAIL_CLOSED_NO_CLAY_PROMOTION`
- Promotion decision: `hold`
- Promotion hold: `True`
- Evidence audit passed: `True`
- Ledger coherent fail-closed: `True`
- Required true flags: `True`
- Downstream flags false: `True`
- Sprint115 reconnection flux-budget ledger closed: `True`
- Sprint114 thin-core correction imported: `True`
- Reconnection flux-budget formula recorded: `True`
- Reconnection timescale recorded: `True`
- Viscous Reynolds condition recorded: `True`
- KStar collapse threshold recorded: `True`
- Clay promoted: `False`

## Required Strings

| String | Present |
| --- | --- |
| `Sprint 115 quantitative reconnection-window flux budget.` | `True` |
| `It closes only the formula ledger.` | `True` |
| `FluxBudget = integral_0_to_T_reconnect Pi_HH_to_L(t) dt` | `True` |
| `Re_delta = Gamma / nu >> b^2 / delta^2` | `True` |
| `FluxBudget >= KStarCollapseThreshold` | `True` |
| `No finite KStar collapse or Clay Navier-Stokes promotion follows from this Sprint115 quantitative receipt alone.` | `True` |

## Gate Results

| Gate | Expected | Actual | Passed | Status |
| --- | --- | --- | --- | --- |
| `sprint115ReconnectionFluxBudgetLedgerClosed` | `true` | `true` | `True` | `PASS` |
| `sprint114ThinCoreCorrectionImported` | `true` | `true` | `True` | `PASS` |
| `fluxIntegralFormulaRecorded` | `true` | `true` | `True` | `PASS` |
| `reconnectionTimescaleRecorded` | `true` | `true` | `True` | `PASS` |
| `viscousReynoldsConditionRecorded` | `true` | `true` | `True` | `PASS` |
| `kstarCollapseThresholdRecorded` | `true` | `true` | `True` | `PASS` |
| `reconnectionWindowLowerBoundClosed` | `false` | `false` | `True` | `PASS` |
| `viscousDecayWindowClosed` | `false` | `false` | `True` | `PASS` |
| `nonlinearDeformationControlClosed` | `false` | `false` | `True` | `PASS` |
| `positiveFluxAccumulationWindowClosed` | `false` | `false` | `True` | `PASS` |
| `finiteTimeFluxSurplusFromCrowDominance` | `false` | `false` | `True` | `PASS` |
| `finiteKStarCollapseClosed` | `false` | `false` | `True` | `PASS` |
| `blowupCriterionBridgeClosed` | `false` | `false` | `True` | `PASS` |
| `clayNavierStokesPromoted` | `false` | `false` | `True` | `PASS` |
| `keyword_true:sprint115ReconnectionFluxBudgetLedgerClosed` | `true` | `true` | `True` | `PASS` |
| `keyword_true:sprint114ThinCoreCorrectionImported` | `true` | `true` | `True` | `PASS` |
| `keyword_true:fluxIntegralFormulaRecorded` | `true` | `true` | `True` | `PASS` |
| `keyword_true:reconnectionTimescaleRecorded` | `true` | `true` | `True` | `PASS` |
| `keyword_true:viscousReynoldsConditionRecorded` | `true` | `true` | `True` | `PASS` |
| `keyword_true:kstarCollapseThresholdRecorded` | `true` | `true` | `True` | `PASS` |
| `keyword_false:reconnectionWindowLowerBoundClosed` | `false` | `false` | `True` | `PASS` |
| `keyword_false:viscousDecayWindowClosed` | `false` | `false` | `True` | `PASS` |
| `keyword_false:nonlinearDeformationControlClosed` | `false` | `false` | `True` | `PASS` |
| `keyword_false:positiveFluxAccumulationWindowClosed` | `false` | `false` | `True` | `PASS` |
| `keyword_false:finiteTimeFluxSurplusFromCrowDominance` | `false` | `false` | `True` | `PASS` |
| `keyword_false:finiteKStarCollapseClosed` | `false` | `false` | `True` | `PASS` |
| `keyword_false:blowupCriterionBridgeClosed` | `false` | `false` | `True` | `PASS` |
| `keyword_false:clayNavierStokesPromoted` | `false` | `false` | `True` | `PASS` |
| `required_string:Sprint 115 quantitative reconnection-window flux budget.` | `present` | `present` | `True` | `PASS` |
| `required_string:It closes only the formula ledger.` | `present` | `present` | `True` | `PASS` |
| `required_string:FluxBudget = integral_0_to_T_reconnect Pi_HH_to_L(t) dt` | `present` | `present` | `True` | `PASS` |
| `required_string:Re_delta = Gamma / nu >> b^2 / delta^2` | `present` | `present` | `True` | `PASS` |
| `required_string:FluxBudget >= KStarCollapseThreshold` | `present` | `present` | `True` | `PASS` |
| `required_string:No finite KStar collapse or Clay Navier-Stokes promotion follows from this Sprint115 quantitative receipt alone.` | `present` | `present` | `True` | `PASS` |
| `target_module` | `DASHI/Physics/Closure/NSSprint115ReconnectionFluxBudget.agda` | `present` | `True` | `PASS` |
| `route` | `RECONNECTION_FLUX_BUDGET_LEDGER_CLOSED_FAIL_CLOSED_NO_CLAY_PROMOTION` | `RECONNECTION_FLUX_BUDGET_LEDGER_CLOSED_FAIL_CLOSED_NO_CLAY_PROMOTION` | `True` | `PASS` |
| `required_anchors` | `all present` | `all present` | `True` | `PASS` |
| `forbidden_markers` | `none` | `none` | `True` | `PASS` |
