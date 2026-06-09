# ns_sprint129_feasibility_window_sampler

Deterministic Sprint129 sampler for the NS viscous feasibility window.

Formula surface:

- alpha is sampled on a fixed rational grid across [0.75, 1.75]
- beta = alpha - 1
- recommended_alpha_window = (1, 3/2)
- viable iff BKM, concentration, u1 viscosity, NSE consistency, and open-window gates all hold
- endpoints and exterior samples are recorded as boundary or gate failures

Summary:

- row_count: 21
- viable_window_count: 9
- boundary_failures: 12
- recommended_alpha_window: (1, 3/2)
- clay_navier_stokes_promoted: false
- complete: false
- exit_code: 1

Exit status: 1 because the sampler identifies a model window but does not prove or promote Clay Navier-Stokes.

| row | alpha | beta | BKM | concentration | u1 viscosity | NSE | in (1,3/2) | viable |
| --- | --- | --- | --- | --- | --- | --- | --- | --- |
| r000 | 0.75 | -0.25 | true | false | false | true | false | false |
| r001 | 0.8 | -0.2 | true | false | false | true | false | false |
| r002 | 0.85 | -0.15 | true | false | false | true | false | false |
| r003 | 0.9 | -0.1 | true | false | false | true | false | false |
| r004 | 0.95 | -0.05 | true | false | false | true | false | false |
| r005 | 1 | 0 | true | false | false | true | false | false |
| r006 | 1.05 | 0.05 | true | true | true | true | true | true |
| r007 | 1.1 | 0.1 | true | true | true | true | true | true |
| r008 | 1.15 | 0.15 | true | true | true | true | true | true |
| r009 | 1.2 | 0.2 | true | true | true | true | true | true |
| r010 | 1.25 | 0.25 | true | true | true | true | true | true |
| r011 | 1.3 | 0.3 | true | true | true | true | true | true |
| r012 | 1.35 | 0.35 | true | true | true | true | true | true |
| r013 | 1.4 | 0.4 | true | true | true | true | true | true |
| r014 | 1.45 | 0.45 | true | true | true | true | true | true |
| r015 | 1.5 | 0.5 | false | true | false | true | false | false |
| r016 | 1.55 | 0.55 | false | true | false | true | false | false |
| r017 | 1.6 | 0.6 | false | true | false | true | false | false |
| r018 | 1.65 | 0.65 | false | true | false | true | false | false |
| r019 | 1.7 | 0.7 | false | true | false | true | false | false |
| r020 | 1.75 | 0.75 | false | true | false | true | false | false |
