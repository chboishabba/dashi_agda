# ns_sprint124_route_classifier

Deterministic Sprint124 classifier for NS route status after the rotating-flux obstruction.

Recommended next lemma: VortexStretchingAmplificationVsDepletionBound
Recommended route id: vortex_stretching
Recommended classification: live_primary_next
Primary route: vortex_stretching
Required classifications met: true
Complete: false
Clay: false

Exit status: 1 because NS Clay is not complete.

| route_id | classification | complete | clay | next_action |
| --- | --- | --- | --- | --- |
| favorable_phase_lag_window_lower_bound | closed | true | false | retain as a closed Sprint123 input |
| zero_mean_flux_over_rotation_cycle | closed_obstruction | false | false | record as the controlling rotation-cycle obstruction |
| rotating_strain_flux_budget | obstructed_by_zero_mean | false | false | do not promote without defeating the zero-mean obstruction |
| vortex_stretching | live_primary_next | false | false | prove VortexStretchingAmplificationVsDepletionBound |
| non_resonant_triads | partial_open | false | false | keep as a secondary partial route after vortex stretching |
