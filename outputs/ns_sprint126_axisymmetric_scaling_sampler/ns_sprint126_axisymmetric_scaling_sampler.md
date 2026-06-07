# ns_sprint126_axisymmetric_scaling_sampler

Deterministic exponent sampler for the Hou-Luo/Hou-Li axisymmetric boundary candidate.

Constraint surface:

- NSE consistency: alpha - beta == 1 within tolerance
- finite energy: beta + gamma >= 2*alpha/3
- BKM candidate: alpha >= 1

The row alpha=1, beta=0, gamma=4/3 is included and marked compatible.
Compatible rows: 2 of 6.
Analytic proof established: false.
Clay promoted: false.

| row | label | alpha | beta | gamma | NSE | energy finite | BKM | compatible | class |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| r000 | hou_luo_hou_li_boundary_example | 1 | 0 | 4/3 | true | true | true | true | compatible_boundary_candidate |
| r001 | subcritical_time_amplitude | 3/4 | -1/4 | 3/2 | true | true | false | false | incompatible_scaling_row |
| r002 | energy_defect_candidate | 3/2 | 1/2 | 1/4 | true | false | true | false | incompatible_scaling_row |
| r003 | bkm_subcritical_consistent | 4/5 | -1/5 | 2 | true | true | false | false | incompatible_scaling_row |
| r004 | nse_inconsistent_reference | 1 | 1/5 | 4/3 | false | true | true | false | incompatible_scaling_row |
| r005 | critical_energy_margin | 3/2 | 1/2 | 1 | true | true | true | true | compatible_boundary_candidate |
