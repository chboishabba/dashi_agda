# ns_sprint124_rotation_cycle_integral_sampler

Deterministic calculator for Sprint124 rotation-cycle flux cancellation.

Formula surface:

- sampled ratios satisfy Omega/C > 1
- T = pi/Omega is one full strain-axis rotation cycle for cos(2*Omega*t)
- theta_rel(t) = (Omega-C)*t
- favorable dwell iff cos(2*theta_rel)>0
- favorable_dwell_fraction = measure{s in [0,(Omega-C)*T]: cos(2s)>0}/((Omega-C)*T)
- signed flux integrand F(t)=cos(2*Omega*t)
- closed form: integral_0^T F(t) dt = 0
- symmetry check: F(t+T/2)=-F(t)

Summary:

- row_count: 8
- favorable_dwell_fraction_min: 0.571428571429
- favorable_dwell_fraction_max: 1
- max_abs_flux_mean_numeric: 0
- max_half_cycle_symmetry_residual: 0
- zero_mean_flux_established: true
- rotating_strain_blowup_route_closed: true
- clay: false

| row | Omega/C | C | rel advance | dwell fraction | flux mean numeric | sym residual | class |
| --- | --- | --- | --- | --- | --- | --- | --- |
| r000 | 1.05 | 0.952380952381 | 0.149599650171 | 1 | 0 | 0 | initial_favorable_dwell_bias_but_zero_mean_flux |
| r001 | 1.125 | 0.888888888889 | 0.349065850399 | 1 | 0 | 0 | initial_favorable_dwell_bias_but_zero_mean_flux |
| r002 | 1.25 | 0.8 | 0.628318530718 | 1 | 0 | 0 | initial_favorable_dwell_bias_but_zero_mean_flux |
| r003 | 1.5 | 0.666666666667 | 1.0471975512 | 1 | 0 | 0 | initial_favorable_dwell_bias_but_zero_mean_flux |
| r004 | 2 | 0.5 | 1.57079632679 | 1 | 0 | 0 | initial_favorable_dwell_bias_but_zero_mean_flux |
| r005 | 3 | 0.333333333333 | 2.09439510239 | 0.75 | 0 | 0 | initial_favorable_dwell_bias_but_zero_mean_flux |
| r006 | 5 | 0.2 | 2.51327412287 | 0.625 | 0 | 0 | initial_favorable_dwell_bias_but_zero_mean_flux |
| r007 | 8 | 0.125 | 2.74889357189 | 0.571428571429 | 0 | 0 | initial_favorable_dwell_bias_but_zero_mean_flux |
