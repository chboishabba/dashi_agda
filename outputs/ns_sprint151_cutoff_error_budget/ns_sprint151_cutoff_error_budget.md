# ns_sprint151_cutoff_error_budget

## Decision

- Decision: `fail_closed_cutoff_budget_has_open_and_blocker_rows`
- Delta sample: `1/16`
- Validation passed: `True`
- Claim closed: `False`
- Proof flags true: `[]`
- Clay promotion: `False`

## Classification Counts

- absorbed: `3`
- support: `2`
- open: `2`
- blocker: `1`

## Rows

| row_id | category | class | symbolic term | numeric load | capacity | ratio | theorem required |
| --- | --- | --- | --- | ---: | ---: | ---: | --- |
| cutoff_gradient_scale_delta_inverse | cutoff_derivative_scale | support | /grad phi_delta/ <= C_grad / delta | 24 | None | None | SmoothCutoffDerivativeBoundGradient |
| cutoff_laplacian_scale_delta_inverse_square | cutoff_derivative_scale | support | /lap phi_delta/ <= C_lap / delta^2 | 960 | None | None | SmoothCutoffDerivativeBoundLaplacian |
| transport_flux_cutoff_boundary | transport_flux | absorbed | int /u/ /omega/^2 /grad phi_delta/ | 15/4 | 80 | 3/64 | CutoffTransportFluxAbsorption |
| diffusion_leakage_cutoff_laplacian | diffusion_leakage | absorbed | nu int /omega/^2 /lap phi_delta/ | 15 | 75 | 1/5 | CutoffDiffusionLeakageAbsorption |
| source_localization_core_window | source_localization | open | int phi_delta source_core | 21/5 | 4 | 21/20 | LocalizedSourceDominanceOrCancellation |
| annular_leakage_outer_shell | annular_leakage | blocker | int_{annulus(delta)} leakage_outer /grad phi_delta/ | 108/5 | 12 | 9/5 | AnnularLeakageExclusionOrDomination |
| absorption_margin_transport_diffusion | absorption_margin | absorbed | M_td - transport_flux - diffusion_leakage | 30 | 240 | 1/8 | JointTransportDiffusionAbsorptionMargin |
| absorption_margin_annular_source | absorption_margin | open | M_as - source_localization - annular_leakage | 95 | 90 | 19/18 | JointAnnularSourceAbsorptionMargin |

## Governance

This ledger is deterministic cutoff-budget accounting.  It records symbolic delta powers and fixed numeric samples, but it emits no theorem-level proof, no global closure, and no Clay promotion.
