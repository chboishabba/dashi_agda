# ns_sprint117_swirl_volume_scaling

Deterministic finite-energy swirl volume scaling ledger.

Formula surface:

- finite-energy rows use ratio = r_H ** (alpha + 1)
- alpha values: 0.25, 0.5, 1.0, 2.0
- r_H values: 0.5, 0.25, 0.125, 0.0625
- u_phi ~ 1/r is rejected because its L2 energy diverges at the axis

Obstruction ledger complete: true.
Swirl Option B route obstructed: true.
Concentration-based Option B closed: true.
Non-circular geometric correlation source remains open: true.
Clay promoted: false.

| profile | alpha | r_H | ratio | finite energy | decision |
| --- | --- | --- | --- | --- | --- |
| u_phi ~ r^0.25 | 0.25 | 0.5 | 0.420448207627 | true | accepted_finite_energy_swirl_profile |
| u_phi ~ r^0.25 | 0.25 | 0.25 | 0.176776695297 | true | accepted_finite_energy_swirl_profile |
| u_phi ~ r^0.25 | 0.25 | 0.125 | 0.0743254446877 | true | accepted_finite_energy_swirl_profile |
| u_phi ~ r^0.25 | 0.25 | 0.0625 | 0.03125 | true | accepted_finite_energy_swirl_profile |
| u_phi ~ r^0.5 | 0.5 | 0.5 | 0.353553390593 | true | accepted_finite_energy_swirl_profile |
| u_phi ~ r^0.5 | 0.5 | 0.25 | 0.125 | true | accepted_finite_energy_swirl_profile |
| u_phi ~ r^0.5 | 0.5 | 0.125 | 0.0441941738242 | true | accepted_finite_energy_swirl_profile |
| u_phi ~ r^0.5 | 0.5 | 0.0625 | 0.015625 | true | accepted_finite_energy_swirl_profile |
| u_phi ~ r^1 | 1 | 0.5 | 0.25 | true | accepted_finite_energy_swirl_profile |
| u_phi ~ r^1 | 1 | 0.25 | 0.0625 | true | accepted_finite_energy_swirl_profile |
| u_phi ~ r^1 | 1 | 0.125 | 0.015625 | true | accepted_finite_energy_swirl_profile |
| u_phi ~ r^1 | 1 | 0.0625 | 0.00390625 | true | accepted_finite_energy_swirl_profile |
| u_phi ~ r^2 | 2 | 0.5 | 0.125 | true | accepted_finite_energy_swirl_profile |
| u_phi ~ r^2 | 2 | 0.25 | 0.015625 | true | accepted_finite_energy_swirl_profile |
| u_phi ~ r^2 | 2 | 0.125 | 0.001953125 | true | accepted_finite_energy_swirl_profile |
| u_phi ~ r^2 | 2 | 0.0625 | 0.000244140625 | true | accepted_finite_energy_swirl_profile |
| u_phi ~ 1/r |  |  |  | false | rejected_infinite_l2_energy |
