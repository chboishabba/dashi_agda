# Sprint 134 Axisymmetric Equation Correction

Contract: `ns_sprint134_axisymmetric_equation_correction`

This artifact retracts the old pure-diffusion assertion for `u1` and records the corrected Hou-Luo axisymmetric PDE surface.

## Corrected Equations

- `D_t u1 = 2 u1 partial_z psi1 + nu Ltilde u1`
- `D_t omega1 = partial_z(u1^2) + nu Ltilde omega1`
- `(partial_t + u^r partial_r + u^z partial_z) Gamma = nu (Delta - 2/r partial_r) Gamma`
- `r in [r0, 1], r0 > 0, ||Gamma(t)||_inf <= M0 => ||u1(t)||_inf <= M0 / r0^2`

## Rows

| Row | Status | Lemma | Corrected statement |
| --- | --- | --- | --- |
| `axisymmetric_variable_definitions` | `corrected` | `StandardAxisymmetricSwirlVariables` | Use u1 = u^theta/r, omega1 = omega^theta/r, psi1 = psi^theta/r, Gamma = r u^theta = r^2 u1, and Ltilde = partial_r^2 + (3/r)partial_r + partial_z^2. |
| `u1_equation_has_stretching_source` | `corrected` | `AxisymmetricSwirlEquationCorrection.U1EquationHasStretchingSource` | D_t u1 = 2 u1 partial_z psi1 + nu Ltilde u1 |
| `omega1_equation_has_quadratic_source` | `intact_corrected_surface` | `AxisymmetricSwirlEquationCorrection.Omega1EquationHasQuadraticSource` | D_t omega1 = partial_z(u1^2) + nu Ltilde omega1 |
| `old_u1_pure_diffusion_retraction` | `retracted_superseded` | `PureDiffusionU1MaximumPrinciple` | The statement D_t u1 = nu Ltilde u1 is false in the standard Hou-Luo variables; u1 has the source 2 u1 partial_z psi1. |
| `gamma_maximum_principle` | `replacement_gate` | `SwirlCirculationMaximumPrinciple` | (partial_t + u^r partial_r + u^z partial_z) Gamma = nu (Delta - 2/r partial_r) Gamma; hence \|\|Gamma(t)\|\|_inf <= \|\|Gamma(0)\|\|_inf. |
| `boundary_annulus_u1_bound` | `replacement_gate` | `BoundaryAnnulusU1Bound` | r in [r0, 1], r0 > 0, \|\|Gamma(t)\|\|_inf <= M0 => \|\|u1(t)\|\|_inf <= M0 / r0^2 |

`axisymmetric_swirl_equation_corrected=true`
`old_u1_pure_diffusion_retracted=true`
`full_clay_ns_solved=false`
`clay_navier_stokes_promoted=false`
