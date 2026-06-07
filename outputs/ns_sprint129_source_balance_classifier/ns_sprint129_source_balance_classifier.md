# ns_sprint129_source_balance_classifier

Deterministic Sprint129 classifier for the NS source balance.

Source balance: partial_z(u1^2)=2 u1 partial_z u1
Recommended next lemma: AdvectiveConcentrationVsDiffusionBound
Recommended action: prove_or_obstruct_AdvectiveConcentrationVsDiffusionBound
Primary open scenario: advective_concentration_formal
Primary obstruction scenario: source_collapse_obstruction
Required classifications met: true
Clay promoted: false

Exit status: 1 because the advective concentration versus diffusion bound remains unresolved and Clay is not promoted.

| scenario_id | classification | u1_ratio_to_omega | gradient_tracks_omega | source_scales_quadratic | bkm_blowup_route | clay_promoted | next_action |
| --- | --- | --- | --- | --- | --- | --- | --- |
| lower_bound_closes | formal_identity_lower_bound | comparable | true | true | true | false | use only as the formal target case |
| lower_bound_missing | open_required | uncontrolled | false | false | false | false | prove or obstruct AdvectiveConcentrationVsDiffusionBound |
| diffusion_dominates | obstruction | subcritical | false | false | false | false | record as obstruction to source dominance |
| advective_concentration_formal | formal_primary_open | comparable_assumed | true | true | true | false | prove or obstruct AdvectiveConcentrationVsDiffusionBound |
| source_collapse_obstruction | obstruction_primary | collapses | false | false | false | false | treat as the decisive obstruction alternative |
