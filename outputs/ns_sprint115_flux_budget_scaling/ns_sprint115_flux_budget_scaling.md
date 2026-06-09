# ns_sprint115_flux_budget_scaling

Deterministic thin-core reconnection flux-budget scaling calculator.

Formula surface:

- elliptic_factor = (delta / b)^4
- crow_growth_time_factor = 7.9
- reconnect_time_factor = 1.0
- viscous_condition_required = (b / delta)^2
- viscous_window_ok = Re_delta > viscous_condition_required
- accumulation_fraction = reconnect_time_factor / crow_growth_time_factor
- net_positive_factor = max(0, 1 - elliptic_factor)
- certified_surplus_margin = accumulation_fraction * net_positive_factor when viscous_window_ok else 0

Closure status: incomplete. No analytic threshold proof flag is available.
Route decision: fail_unproved_kstar_collapse_threshold.

| delta/b | Re_core | elliptic | required | Re_delta | viscous ok | surplus margin |
| --- | --- | --- | --- | --- | --- | --- |
| 0.1 | 1000 | 0.0001 | 100 | 100 | false | 0 |
| 0.1 | 10000 | 0.0001 | 100 | 1000 | true | 0.126569620253 |
| 0.1 | 100000 | 0.0001 | 100 | 10000 | true | 0.126569620253 |
| 0.2 | 1000 | 0.0016 | 25 | 200 | true | 0.126379746835 |
| 0.2 | 10000 | 0.0016 | 25 | 2000 | true | 0.126379746835 |
| 0.2 | 100000 | 0.0016 | 25 | 20000 | true | 0.126379746835 |
| 0.3 | 1000 | 0.0081 | 11.1111111111 | 300 | true | 0.125556962025 |
| 0.3 | 10000 | 0.0081 | 11.1111111111 | 3000 | true | 0.125556962025 |
| 0.3 | 100000 | 0.0081 | 11.1111111111 | 30000 | true | 0.125556962025 |
| 0.4 | 1000 | 0.0256 | 6.25 | 400 | true | 0.123341772152 |
| 0.4 | 10000 | 0.0256 | 6.25 | 4000 | true | 0.123341772152 |
| 0.4 | 100000 | 0.0256 | 6.25 | 40000 | true | 0.123341772152 |
| 0.48 | 1000 | 0.05308416 | 4.34027777778 | 480 | true | 0.119862764557 |
| 0.48 | 10000 | 0.05308416 | 4.34027777778 | 4800 | true | 0.119862764557 |
| 0.48 | 100000 | 0.05308416 | 4.34027777778 | 48000 | true | 0.119862764557 |
