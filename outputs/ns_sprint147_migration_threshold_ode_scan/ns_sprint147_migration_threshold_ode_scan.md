# ns_sprint147_migration_threshold_ode_scan

## Status

Deterministic reduced ODE evidence scan. 14 of 42 scanned rows initiate migration before suppression.

This artifact is evidence only. It does not prove a theorem, does not prove blowup existence, does not solve full Clay Navier-Stokes, and does not promote a Clay claim.

## ODE Model

* P: plane baseline source amplitude.
* A: off-axis source amplitude.
* L: logarithmic feedback state.
* S: accumulated suppression index.

Migration is initiated when both `A/(P+eps)` and `A` cross their thresholds before suppression. Suppression is triggered by the accumulated suppression index or by plane baseline decay below the configured floor.

## Guards

* `ode_scan_supports_some_regimes`: `true`
* `theorem_proved`: `false`
* `blowup_existence_proved`: `false`
* `full_clay_ns_solved`: `false`
* `clay_navier_stokes_promoted`: `false`

## Scan Snapshot

| Regime | Variant | Event | t | Max A/P | Max A | Guard |
|---|---:|---|---:|---:|---:|---|
| Balanced threshold competition | nominal | no_event_by_horizon | 24.00 | 0.645 | 0.212 | suppressed/no event |
| High viscosity suppressed | nominal | suppressed | 8.23 | 0.138 | 0.054 | suppressed/no event |
| Log feedback favorable | log_high | migration_initiated | 5.50 | 0.721 | 0.474 | migration before suppression |
| Log feedback favorable | log_low | migration_initiated | 7.17 | 0.721 | 0.418 | migration before suppression |
| Log feedback favorable | nominal | migration_initiated | 6.26 | 0.721 | 0.447 | migration before suppression |
| Log feedback favorable | source_high | migration_initiated | 5.19 | 0.721 | 0.483 | migration before suppression |
| Log feedback favorable | source_low | migration_initiated | 7.91 | 0.720 | 0.398 | migration before suppression |
| Log feedback favorable | viscosity_high | migration_initiated | 6.53 | 0.720 | 0.409 | migration before suppression |
| Log feedback favorable | viscosity_low | migration_initiated | 6.03 | 0.720 | 0.481 | migration before suppression |
| Off-axis source favorable | log_high | migration_initiated | 4.73 | 0.720 | 0.481 | migration before suppression |
| Off-axis source favorable | log_low | migration_initiated | 5.31 | 0.720 | 0.458 | migration before suppression |
| Off-axis source favorable | nominal | migration_initiated | 5.03 | 0.721 | 0.469 | migration before suppression |
| Off-axis source favorable | source_high | migration_initiated | 4.23 | 0.722 | 0.500 | migration before suppression |
| Off-axis source favorable | source_low | migration_initiated | 6.23 | 0.720 | 0.428 | migration before suppression |
| Off-axis source favorable | viscosity_high | migration_initiated | 5.20 | 0.721 | 0.443 | migration before suppression |
| Off-axis source favorable | viscosity_low | migration_initiated | 4.89 | 0.721 | 0.493 | migration before suppression |
| Plane baseline viscous suppression | nominal | suppressed | 14.80 | 0.192 | 0.067 | suppressed/no event |
| Weak feedback no migration | nominal | suppressed | 23.86 | 0.355 | 0.127 | suppressed/no event |

## O/R/C/S/L/P/G/F

* O: Sprint 147 lane 3 owns only scripts/ns_sprint147_migration_threshold_ode_scan.py and outputs/ns_sprint147_migration_threshold_ode_scan/.
* R: Emit a deterministic reduced ODE/parameter scan for the migration initiation threshold, with explicit fail-closed proof guards.
* C: Four-variable toy ODE: P plane baseline decay, A off-axis source gain/damping, L logarithmic feedback, S accumulated suppression.
* S: Named regimes are scanned under nominal, source, log, and viscosity perturbation variants using fixed-step RK4.
* L: Rows classify first threshold ordering only; migration before suppression is numerical evidence in this reduced model, not a Navier-Stokes theorem.
* P: Use positive rows to prioritize analytic migration-threshold obligations and negative rows to identify damping-dominated toy regimes.
* G: Validation requires some deterministic rows, stable hashes, hard false theorem/proof/Clay guards, and at least one migrated regime before setting ode_scan_supports_some_regimes.
* F: Any accidental theorem proof, blowup proof, full Clay solution, Clay promotion, missing row hashes, or non-positive dt fails the artifact.

## Hashes

* `rows_hash`: `a205edc0615c41265161f4670998f50976d9a17be7aa1318e70f15d14737b6b4`
* `summary_payload_hash_without_self`: `e0083ff450d2dd46d88ffa2ee4ae9a36117144d5b04a27aa3f9759c09b9a02dd`
