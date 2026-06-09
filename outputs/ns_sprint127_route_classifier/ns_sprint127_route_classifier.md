# ns_sprint127_route_classifier

Deterministic Sprint127 classifier for NS route state.

Recommended next lemma: BoundaryVorticityAmplificationLaw
Recommended route id: boundary_vorticity_amplification_law
Recommended classification: open_required
Primary route: axisymmetric_boundary_vortex_stretching_gate
Required classifications met: true
Complete: false
Clay: false

Exit status: 1 because NS is incomplete.

| route_id | classification | complete | clay | next_action |
| --- | --- | --- | --- | --- |
| axisymmetric_boundary_vortex_stretching_gate | live_primary_open | false | false | keep as the live primary route |
| boundary_vorticity_amplification_law | open_required | false | false | prove BoundaryVorticityAmplificationLaw |
| strain_alignment_near_axis_or_boundary | open_required | false | false | prove after the amplification law is framed |
| viscous_boundary_layer_dominance_check | open_required | false | false | check viscous dominance against boundary amplification |
| hou_luo_scaling_compatibility | recorded_compatible | false | false | retain as compatible scaling evidence |
| nonresonant_pressure_triads | secondary_open | false | false | keep as a secondary open route |
| clay_navier_stokes | not_promoted | false | false | do not promote until required open lemmas close |
