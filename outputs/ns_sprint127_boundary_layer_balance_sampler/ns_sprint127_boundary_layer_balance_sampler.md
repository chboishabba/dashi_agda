# ns_sprint127_boundary_layer_balance_sampler

Deterministic sampler for axisymmetric boundary vortex-stretching balance.

Checks:

- BKM candidate: alpha >= 1
- bounded energy: beta + gamma >= 2*alpha/3
- stretching beats viscosity: omega_over_r0_indicator > viscous_indicator

Dimensionless proxies:

- omega_over_r0_indicator = alpha + beta - (r0 - 1)
- viscous_indicator = nu + 2*beta

The Hou-Luo compatible scaling row alpha=1, beta=0, gamma=4/3 is included.
Balance-compatible rows: 2 of 6.
Proof established: false.
Clay: false.

| row | label | alpha | beta | gamma | nu | r0 | BKM | energy | stretch | compatible |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| r000 | hou_luo_compatible_boundary_scaling | 1 | 0 | 4/3 | 1/2 | 1 | true | true | true | true |
| r001 | thin_radial_high_viscosity_control | 1 | 1/4 | 1 | 3/2 | 1 | true | true | false | false |
| r002 | supercritical_growth_energy_defect | 3/2 | 1/4 | 1/4 | 1/2 | 1 | true | false | true | false |
| r003 | sub_bkm_bounded_reference | 3/4 | 1/3 | 5/4 | 1/2 | 1 | false | true | false | false |
| r004 | large_boundary_radius_damped | 1 | 0 | 4/3 | 5/4 | 2 | true | true | false | false |
| r005 | strong_stretching_bounded_candidate | 4/3 | 2/3 | 1/2 | 1/3 | 1 | true | true | true | true |
