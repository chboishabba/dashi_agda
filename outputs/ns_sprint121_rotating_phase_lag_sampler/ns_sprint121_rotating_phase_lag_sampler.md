# ns_sprint121_rotating_phase_lag_sampler

Deterministic sampler for rotating strain phase-lag.

Formula surface:

- phi(t)=omega*t
- packet memory lag = tau
- phase_lag = omega*tau
- positive_flux_window iff cos(2*phase_lag)>0
- amplification_survives iff sin(2*phase_lag)>0
- favorable iff both gates hold

Summary:

- favorable_row_count: 14
- only_some_parameter_rows_are_favorable: true
- non_circular_persistence_established: false
- rotating_strain_decorrelation_mechanism_closed: false
- clay: false

| omega | tau | phase lag | cos(2 lag) | sin(2 lag) | positive flux | amplification survives | favorable |
| --- | --- | --- | --- | --- | --- | --- | --- |
| 0.25 | 0.1 | 0.025 | 0.998750260395 | 0.0499791692707 | true | true | true |
| 0.25 | 0.25 | 0.0625 | 0.992197667229 | 0.124674733385 | true | true | true |
| 0.25 | 0.5 | 0.125 | 0.968912421711 | 0.247403959255 | true | true | true |
| 0.25 | 1 | 0.25 | 0.87758256189 | 0.479425538604 | true | true | true |
| 0.5 | 0.1 | 0.05 | 0.995004165278 | 0.0998334166468 | true | true | true |
| 0.5 | 0.25 | 0.125 | 0.968912421711 | 0.247403959255 | true | true | true |
| 0.5 | 0.5 | 0.25 | 0.87758256189 | 0.479425538604 | true | true | true |
| 0.5 | 1 | 0.5 | 0.540302305868 | 0.841470984808 | true | true | true |
| 1 | 0.1 | 0.1 | 0.980066577841 | 0.198669330795 | true | true | true |
| 1 | 0.25 | 0.25 | 0.87758256189 | 0.479425538604 | true | true | true |
| 1 | 0.5 | 0.5 | 0.540302305868 | 0.841470984808 | true | true | true |
| 1 | 1 | 1 | -0.416146836547 | 0.909297426826 | false | true | false |
| 2 | 0.1 | 0.2 | 0.921060994003 | 0.389418342309 | true | true | true |
| 2 | 0.25 | 0.5 | 0.540302305868 | 0.841470984808 | true | true | true |
| 2 | 0.5 | 1 | -0.416146836547 | 0.909297426826 | false | true | false |
| 2 | 1 | 2 | -0.653643620864 | -0.756802495308 | false | false | false |
| 4 | 0.1 | 0.4 | 0.696706709347 | 0.7173560909 | true | true | true |
| 4 | 0.25 | 1 | -0.416146836547 | 0.909297426826 | false | true | false |
| 4 | 0.5 | 2 | -0.653643620864 | -0.756802495308 | false | false | false |
| 4 | 1 | 4 | -0.145500033809 | 0.989358246623 | false | true | false |
