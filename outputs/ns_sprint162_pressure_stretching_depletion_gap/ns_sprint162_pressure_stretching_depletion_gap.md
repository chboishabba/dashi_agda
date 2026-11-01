# Sprint 162 Pressure Stretching Depletion Gap

- Surface: `PressureStretchingDepletionGap`
- Decision: `pressure_stretching_depletion_gap_fail_closed`
- PressureStretchingDepletionLemma: `False`
- Validation passed: `True`

| symbol | name | scale_status | role |
| --- | --- | --- | --- |
| u | velocity | critical_input | 3D incompressible Navier-Stokes velocity field |
| p | pressure | critical_not_depleting | nonlocal Riesz-transform pressure p = R_i R_j(u_i u_j) |
| omega | vorticity | critical_concentration_carrier | curl u, source carrier for vortex stretching |
| S | strain tensor | alignment_sensitive | symmetric part of grad u controlling omega dot S omega |
| e_max | maximal strain eigenvector | alignment_sensitive | direction of strongest stretching |
| A_r | alignment defect | missing_depletion | localized integral of |omega|^2 positive alignment with e_max(S) |
| D_r | local defect | critical_quantity | scale-critical local |u|^3 + |p|^(3/2) defect |
| Phi_r | pressure flux | critical_not_depleting | localized pressure flux integral p u dot grad phi_r |
| E_r | dissipation | absorbing_term_if_gain_exists | localized viscous control term |

## O/R/C/S/L/P/G/F

- O: Sprint162 lane 2 owns the pressure/stretching depletion gap ledger.
- R: Name the exact missing alpha-positive estimate blocking local defect monotonicity.
- C: One deterministic JSON summary with variables, invariants, and false theorem flags.
- S: Calderon-Zygmund controls pressure at the critical scale but supplies no alpha gain.
- L: critical control -> alpha-zero wall -> alpha-positive depletion lemma -> Clay route if supplied.
- P: Keep the lemma false while preserving a concrete theorem target.
- G: Validation requires all Clay and depletion flags false.
- F: The missing object is a pressure/stretching depletion inequality with alpha > 0.
