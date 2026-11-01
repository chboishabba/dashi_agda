# Sprint 151 Width ODE Extraction Evidence Ledger

- Contract: `ns_sprint151_width_ode_extraction`
- Formula: `delta_dot = -Omega*log(Omega) + nu/delta`
- Equilibrium: `delta_eq = nu/(Omega*log(Omega))` for `Omega > 1`
- Derivation rows: 4
- Scan rows: 60
- Subcritical projection rows: 36
- Scan sign counts: `{'positive': 24, 'zero': 12, 'negative': 24}`

## Flags
- `width_ode_extracted_from_ns`: `false`
- `equilibrium_model_supported`: `true`
- `subcritical_ode_conditional`: `true`
- `bkm_finite`: `false`
- `full_clay_ns_solved`: `false`

## O/R/C/S/L/P/G/F
- **O**: Worker 4 owns scripts/ns_sprint151_width_ode_extraction.py and outputs/ns_sprint151_width_ode_extraction/.
- **R**: Create a deterministic evidence ledger for the reduced width ODE dot(delta) = -Omega log Omega + nu/delta from localized enstrophy term accounting.
- **C**: The artifact is a Python stdlib emitter producing JSON, CSV, Markdown, and manifest files with stable hashes and fail-closed flags.
- **S**: For Omega > 1 the equilibrium model delta_eq = nu/(Omega log Omega) is supported algebraically, and the scan confirms dot(delta) is positive below equilibrium, zero at equilibrium, and negative above it.
- **L**: Localized stretching is represented by the compressive term -Omega log Omega and viscosity by +nu/delta; this is a reduced scalar projection, not a derivation from the full Navier-Stokes system.
- **P**: Use the ledger as evidence for reduced-model bookkeeping and for conditional beta-positive subcritical projection only.
- **G**: Validation requires exact theorem flags, positive scan parameters, Omega > 1 for equilibrium rows, beta > 0 for subcritical rows, and the expected sign relation to delta_eq.
- **F**: Gaps remain: no rigorous extraction from localized Navier-Stokes enstrophy identities, no BKM finite integral theorem, and no full Clay Navier-Stokes solution.

## Boundary

This artifact supports only the reduced equilibrium model and a conditional beta-positive subcritical projection. It does not extract the width ODE from the full Navier-Stokes equations, does not prove BKM finiteness, and does not solve the Clay problem.
