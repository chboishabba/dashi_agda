# ns_boundary_empirical_summary summary

- lambda3 JSON: `scripts/data/outputs/ns_boundary_component_frame10/ns_boundary_component_lambda3_N128_frame10_component2_20260619.json`
- f123 JSON: `scripts/data/outputs/ns_boundary_component_frame10/ns_boundary_f123_absorption_N128_frame10_component2_20260619.json`

- overall status: `ok`

## Validation

- `f123_authority_ok`: `True`
- `f123_loaded`: `True`
- `f123_status_ok`: `True`
- `lambda3_authority_ok`: `True`
- `lambda3_loaded`: `True`
- `lambda3_status_ok`: `True`
- `lambda3_status_present`: `True`
- `overall_pass`: `True`

## Warnings

- none

## lambda3

- status: `'ok'`
- authority_ok: `True`
- source_path: `scripts/data/outputs/ns_boundary_component_frame10/ns_boundary_component_lambda3_N128_frame10_component2_20260619.json`

### Control card
- O: Emit fail-closed frame/component lambda3 diagnostics from derived NS boundary archives.
- R: Produce bounded-away-from-zero and distribution diagnostics for selected {lambda2 <= beta} components.
- C: scripts/ns_boundary_component_lambda3_diagnostic.py
- S: Validate derived NPZ fields, select a beta component (requested or auto), and compute boundary/tight layer diagnostics.
- L: Status is ok only when selected component and analysis layer have finite cells; otherwise fail-closed.
- P: FAIL_CLOSED_LAMBDA3_COMPONENT_DIAGNOSTIC
- G: No theorem or theorem-analogue promotion is claimed; this is synthetic boundary telemetry.
- F: The run provides empirical telemetry only and does not establish a proof or Clay promotion.

### Key fields
- `beta`: `0.0`
- `boundary_cell_count`: `162`
- `boundary_lambda3_stats.max`: `31.306277536963513`
- `boundary_lambda3_stats.mean`: `12.992313287056529`
- `boundary_lambda3_stats.min`: `2.0910865534885876`
- `boundary_lambda3_stats.sum`: `2104.7547525031578`
- `component_cell_count`: `984827`
- `component_count`: `20380`
- `component_id`: `2`
- `contract`: `'ns_boundary_component_lambda3_diagnostic'`
- `frame`: `None`
- `lambda2_band`: `0.001`
- `lambda3_bounded_away_from_zero`: `True`
- `lambda3_gap_threshold`: `1e-08`
- `lambda3_min_abs`: `2.0910865534885876`
- `lambda3_stats.max`: `31.306277536963513`
- `lambda3_stats.mean`: `12.992313287056529`
- `lambda3_stats.min`: `2.0910865534885876`
- `lambda3_stats.sum`: `2104.7547525031578`
- `min_g12`: `{'index': [18, 107, 49], 'value': 2.0907661810286142}`
- `min_rho`: `{'index': [77, 106, 124], 'value': 0.23098019784845852}`
- `script`: `'scripts/ns_boundary_component_lambda3_diagnostic.py'`
- `status`: `'ok'`
- `tight_band_cell_count`: `984827`
- `tight_band_lambda3_stats.max`: `50.75194356831483`
- `tight_band_lambda3_stats.mean`: `17.115015478048335`
- `tight_band_lambda3_stats.min`: `1.214646326418094`
- `tight_band_lambda3_stats.sum`: `16855329.348199908`

## f123

- status: `'ok'`
- authority_ok: `True`
- source_path: `scripts/data/outputs/ns_boundary_component_frame10/ns_boundary_f123_absorption_N128_frame10_component2_20260619.json`

### Control card
- O: Emit a deterministic empirical F123 boundary-band absorption diagnostic from NS-derived or pairfield NPZ inputs.
- R: Compute |lambda2|-band density and compare it against configured positive-commutator proxy channels.
- C: scripts/ns_boundary_f123_absorption_diagnostic.py
- S: Load required fields, form analysis masks, compute finite damping density and optional proxy dominance ratios.
- L: Status is ok only when boundary+component analysis cells exist and contain at least one finite damping sample.
- P: FAIL_CLOSED_F123_ABSORPTION_DIAGNOSTIC
- G: No analytic theorem, Clay theorem, or route promotion is claimed by this diagnostic.
- F: Fail-closed: missing required fields, empty analysis masks, non-finite core fields, or unavailable requested proxy fields produce non-ok status.

### Key fields
- `abs_damping_stats.max`: `686.8605587246625`
- `abs_damping_stats.mean`: `52.0848218197137`
- `abs_damping_stats.min`: `0.00013140575886578512`
- `abs_damping_stats.sum`: `8437.74113479362`
- `boundary_cell_count`: `370`
- `component_id`: `2`
- `contract`: `'ns_boundary_f123_absorption_diagnostic'`
- `density_stats.max`: `-0.00013140575886578512`
- `density_stats.mean`: `-52.0848218197137`
- `density_stats.min`: `-686.8605587246625`
- `density_stats.sum`: `-8437.74113479362`
- `lambda2_band`: `0.001`
- `route_decision`: `'FAIL_CLOSED_F123_ABSORPTION_DIAGNOSTIC'`
- `script`: `'scripts/ns_boundary_f123_absorption_diagnostic.py'`
- `status`: `'ok'`
