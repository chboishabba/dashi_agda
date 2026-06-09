# ns_sprint135_hou_luo_source_viscosity_phase

## Summary

- Sprint 134 inputs acknowledged: `True`
- Hou-Luo route status: `open_live_candidate`
- Polynomial obstruction model retracted: `True`
- Log-Gronwall source can beat viscosity: `True`
- Full Clay NS solved: `False`
- Clay Navier-Stokes promoted: `False`

## Representative Tail Rows

| model | expected phase | log10(source/viscosity) | trend |
|---|---:|---:|---|
| polynomial_gamma_annulus_gradient | source_over_viscosity_tends_to_0 | -15 | decreasing_as_tau_to_0 |
| polylog_gradient_loss | source_over_viscosity_tends_to_0 | -12.2756 | decreasing_as_tau_to_0 |
| formal_bkm_quadratic_source | source_over_viscosity_tends_to_infinity | 7.5 | increasing_as_tau_to_0 |
| corrected_log_gronwall_source | source_over_viscosity_tends_to_infinity | 3147.28 | increasing_as_tau_to_0 |
| actual_pde_source_with_alignment_and_sign | unresolved | unresolved | unresolved_no_scalar_trend |

## Interpretation

The phase table separates scalar asymptotic regimes from PDE-level proof. A fixed polynomial source model supports viscous dominance as an asymptotic calculation, but Sprint 134 prevents promoting that calculation to a Hou-Luo obstruction theorem. The corrected log-Gronwall model can overwhelm polynomial viscosity, so the axisymmetric Hou-Luo route remains open/live.
