# Sprint 153 Core Source Constant Scan

- Contract: `ns_sprint153_core_source_constant_scan`
- Expected scale: `2*u1*v*Omega*delta^2`
- Localized source proxy: `cutoff_mass_constant*2*u1*v*Omega*delta^2`
- Rows: 540
- Classification counts: `{'support': 216, 'open': 216, 'blocker': 108}`
- Random seed dependence: `false`

## Flags
- `core_source_constant_scan_complete`: `true`
- `expected_scale_control_supported`: `true`
- `full_localized_source_theorem_proved`: `false`
- `full_navier_stokes_theorem_proved`: `false`
- `full_theorem_proved`: `false`
- `bkm_finite`: `false`
- `full_clay_ns_solved`: `false`
- `clay_navier_stokes_promoted`: `false`

## O/R/C/S/L/P/G/F
- **O**: Worker 3 owns scripts/ns_sprint153_core_source_constant_scan.py and outputs/ns_sprint153_core_source_constant_scan/.
- **R**: Scan deterministic delta, Omega, u1, v, and cutoff-mass constants to test whether the localized core source is controlled by the expected 2*u1*v*Omega*delta^2 scale.
- **C**: A stdlib Python emitter writes rows JSON, rows CSV, summary JSON, Markdown, and manifest through an atomic output-directory swap.
- **S**: Rows with cutoff ratio at most 1.0 are support; rows up to 1.2 are open constant slack; larger rows are blockers for the sharp expected scale control.
- **L**: The scan lattice is constant-level evidence only: source row < cutoff mass control < localized source theorem < BKM/Clay boundary.
- **P**: Use support rows as admissible constant regimes, open rows as near-miss constants requiring tightening, and blocker rows as explicit obstruction cases.
- **G**: Validation requires positive scan parameters, exact scale-ratio accounting, support/open/blocker coverage, stable file hashes, and all full-theorem and Clay flags false.
- **F**: No analytic cutoff-mass lemma is proved here; the full localized source theorem, BKM finiteness, and Clay Navier-Stokes claims remain closed.

## Boundary

This scan records deterministic constant-level evidence for the localized source scale. It does not prove the full localized source theorem, BKM finiteness, or any Clay Navier-Stokes claim.
