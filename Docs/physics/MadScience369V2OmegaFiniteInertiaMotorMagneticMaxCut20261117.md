# V2 Ω finite-inertia magnetic-memory motor weld — 17 November 2026

**Physical objective.** Establish whether the magnetic-memory current-placement gain survives load-dependent shaft dynamics, without treating improved converter recovery as the explanation.

## Reused model

Existing two-winding rotor-angle coenergy, nonlinear reversible saturation and passive current-following memory from `v2_omega_coupled_magnetic_torque.py` and `v2_omega_nonlinear_memory_torque.py`. Magnetic geometry and nominal 95% signed net converter boundary are unchanged. Winding currents are imposed as smooth functions of rotor angle; no transistor-resolved tracking is established.

A finite-inertia rotor follows `J ω̇ = T_motor + T_magnetic − b ω`, with an ideal motor shaft-torque actuator constrained to `|T_motor| ≤ T_max`, speed-proportional feedback and fixed feedforward. The magnetic memory remains governed by `τ ż=i−z`. The actual mechanical-cycle storage endpoints, not assumed closed states, are included.

The integrated signed identity is:

```
W_motor_shaft =
  W_electrical_export_raw
+ W_copper + W_magnetic_memory + W_viscous
+ ΔE_rotor + ΔE_magnetic
```

It holds without assuming constant rotor speed or vanishing motor-side stored energy. Net bus output quoted below is calculated with a fixed ideal signed factor, *not* a physical bidirectional converter loss map.

## Illustrative result (not original V2)

Assume rotor inertia 0.02 kg·m², motor torque limit 0.65 N·m, viscous coefficient 0.00006 N·m/(rad/s), nominal 2354 RPM, 30 mechanical revolutions. Controllers are matched to 20 W net output in the earlier fixed-speed model.

| Last cycle | Memory-aware timing | Copper-only timing |
|---|---:|---:|
| Motor shaft mechanical supply | 30.427 W | 32.679 W |
| Modeled bus output | 20.00005 W | 19.99999 W |
| Rotor energy-rate correction | +0.000156 W | +0.000155 W |
| Speed ripple | 0.263 RPM | 0.267 RPM |
| Complete per-cycle ledger residual | −1.32 μJ | +0.32 μJ |

Thus the same-machine dynamic comparison retains approximately **2.252 W less motor shaft demand** at effectively matched export. That saving is completely accountable as magnetic-memory loss redistribution, not an anomalous output.

## Independent negative controls

- Motor torque cap 0.08 N·m causes persistent saturation and kinetic-energy depletion; **stationarity fails**.
- Inertia 0.0002 kg·m² creates more than 10 RPM speed ripple despite a closing energy ledger; mean power alone is insufficient.
- The voltage/current checks on the dynamic trajectory are **sampled**, not certified between samples or at transistor edges.
- The last-cycle rotor storage rate is small but nonzero; numerical approach to a periodic solution is **not a certified nonlinear periodic orbit**.

**Local acceptance:** 58/58 magnetic priority tests passed: 47 reused, 11 new. The complete tested source, tests, runner and machine-readable receipts are supplied in the conversation package `v2_omega_finite_inertia_magnetic_shaft_maxcut_20261117.zip`. **New executable files not yet committed to GitHub**; this report and canonical roadmap are the repository-backed results of this round.

## Roadmap boundaries

Open: source-selected original V2 coenergy and material hysteresis, physical winding current tracking and electrical-drive losses, real shaft inertia and motor electrical input, rigorous hybrid periodic orbit and thermal feasibility, original all-port load-intervention measurements, pinned Agda kernel and connected-head CI. All original **16 strict P0–P4 gates remain OPEN**.

Highest-alpha next step: true same-machine current-tracking and motor efficiency map, followed by calibrated torque/load intervention. Converter recovery remains a *fixed secondary boundary*, not the primary claimed mechanism.
