# Sprint 156 Corrected Width ODE Equilibrium Scan

- Contract: `ns_sprint156_width_ode_equilibrium_scan`
- Width ODE: `delta_dot = -Umax*logOmega*delta + nu/delta`
- Equilibrium: `delta_eq = sqrt(nu/(Umax*logOmega))`
- Omega growth cap: `Omega_dot <= C*Umax*Omega*logOmega`
- Finite-T bound: `Omega(t) <= exp(log(Omega0)*exp(C*Umax*T))`
- Rows: 4320
- Validation passed: `true`
- Sign counts: `{'positive': 1728, 'zero': 864, 'negative': 1728}`

## Flags
- `model_validity_support`: `true`
- `bkm_finite`: `false`
- `full_clay_ns_solved`: `false`
- `clay_navier_stokes_promoted`: `false`
- `promotion_allowed`: `false`
- `evidence_only`: `true`

## O/R/C/S/L/P/G/F
- **O**: Worker 3 owns scripts/ns_sprint156_width_ode_equilibrium_scan.py and outputs/ns_sprint156_width_ode_equilibrium_scan/.
- **R**: Scan the corrected scalar width ODE equilibrium, compatible Omega growth inequality, and finite-T double-exponential control.
- **C**: A deterministic Python stdlib emitter writes rows JSON, rows CSV, summary JSON, Markdown, and manifest through an atomic directory swap.
- **S**: The corrected equilibrium delta_eq=sqrt(nu/(Umax*logOmega)) is algebraically supported for positive nu, Umax, and logOmega.
- **L**: The finite-T double-exponential bound supports scalar model validity only; BKM and full Navier-Stokes theorem obligations remain separate.
- **P**: Use these rows as reduced-model validity evidence and invariant checks, with no promotion beyond model-validity support.
- **G**: Validation requires positive parameters, equilibrium sign consistency, growth inequality compliance, finite double-exponential bounds, and hard false BKM/Clay promotion flags.
- **F**: No full localized Navier-Stokes derivation, no BKM integrability theorem, and no Clay Navier-Stokes solution are claimed.

## Boundary

This scan records corrected reduced-model equilibrium evidence and finite-time scalar double-exponential control only. It does not promote BKM finiteness, full Clay Navier-Stokes, or any theorem beyond model-validity support.
