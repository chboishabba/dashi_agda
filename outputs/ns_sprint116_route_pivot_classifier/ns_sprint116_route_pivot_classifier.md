# ns_sprint116_route_pivot_classifier

Deterministic classifier for post-Crow Navier-Stokes route choices.

Recommended next route: axisymmetric_with_swirl_option_a
Next lemma: SwirlingVelocityStrainSign
Complete: false
Clay: false

Exit status: 1 because no candidate route is Clay-complete.

| route_id | status | reuses_in_repo | next_lemma | clay_promoted | rank |
| --- | --- | --- | --- | --- | --- |
| thin_core_crow_option_b | obstructed | Sprint113-115 Crow persistence, thin-core reconnection window, and flux-budget classifiers | NoUnforcedCrowFluxCollapse | false | 3 |
| axisymmetric_with_swirl_option_a | open_high_value | axisymmetric Navier-Stokes structure, swirl sign bookkeeping, and strain/vorticity closure surfaces | SwirlingVelocityStrainSign | false | 1 |
| burgers_vortex_concentration_option_b | open_long_shot | vortex concentration heuristics and local strain amplification interfaces | BurgersVortexConcentrationBarrier | false | 2 |
| general_data_kstar_regular_option_a | blocked_by_sprints87_94 | general-data k-star regularity attempts and Sprint87-94 blocker records | GeneralDataKStarRegularityBlockerDischarge | false | 4 |
