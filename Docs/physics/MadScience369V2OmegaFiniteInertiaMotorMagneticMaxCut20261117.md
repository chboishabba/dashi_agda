# Ω — finite-inertia motor and magnetic-memory weld (17 November 2026)

## Scope and reuse

Uses existing `v2_omega_coupled_magnetic_torque.Model` and `v2_omega_nonlinear_memory_torque.Memory`, `periodic_state`, and `match_output`. The magnetic geometry, current waveforms and converter boundary are unchanged. No source-selected V2 component values are available. This is a **numerical** finite-inertia dynamic extension, not an Agda kernel proof, physical measurement, PWM controller or thermal stability proof.

## Mathematical identity and sign discipline

Let `i(theta)` be the *commanded* two-winding current, `z` the magnetic-memory state, `tau z_dot = i-z`, `lambda = L(theta)i-beta*i³+k z`, and `Tmag = partial_theta W'`. Current enters the electrical winding, so positive signed terminal work is electrical *input*; `-i·v` is raw electrical export. Magnetic energy obeys

`dEmag/dt = i·lambda_dot - Tmag*omega - Dmem`.

The actual motor and rotor satisfy

`J*omega_dot = Tmotor + Tmag - b*omega`.

Therefore, for **any** complete integration interval,

`Wmotor = Wexport_raw + Wcopper + Wmemory + Wfriction + DeltaErotor + DeltaEmagnetic`,

where `Erotor=J*omega²/2`; there is **no** uncharged flywheel, auxiliary source or assumed zero magnetic storage. The raw signed conversion to nominal bus export is `eta*Wexport_raw` as a *deliberately idealised* fixed boundary; this is not a bidirectional power-electronics loss theorem. The motor input is shaft mechanical power from a **torque-limited ideal actuator**, not a metered mains motor electrical input.

## Added dynamics

`i(theta) = c + u sin(p theta) + v cos(p theta)` is prescribed as a current-tracking assumption, not derived from a feasible PWM regulator. Motor torque is limited by `|Tmotor|<=Tmax` and follows a proportional speed controller around nominal 2354 RPM with fixed average-reaction feedforward. Finite inertia, viscous loss, passive magnetic lag and both energy stores are integrated together with signed work integrators. The rotor is not artificially constrained to constant speed. Ordinary recovery efficiency is held fixed. Endpoints are evaluated at the same **rotor-angle cycles**, rather than equal wall-clock times.

## Results — invented design parameters

Baseline: `J=0.02 kg·m²`, `Tmax=0.65 N·m`, `b=0.00006 N·m/(rad/s)`; 30 mechanical rotor turns; model RPM 2354. The two controllers were previously calibrated to **20 W exported** at fixed RPM. With finite-inertia tracking, each produces approximately 20 W on the final cycle while the memory-aware controller requires approximately **2.25 W less motor shaft supply**. The reduction is explained by reduced magnetic-memory dissipation despite slightly higher copper loss; viscous friction is explicitly included. The final-cycle energy residual is on the order of microjoules and rotor storage-rate trends toward zero (last-cycle ~1e-4 W). Speed ripple remains finite (~0.26 RPM in this assumed inertia). Current and voltage are **sampled** under the prescribed tracking trajectory; no continuous switching voltage proof is claimed.

## Negative controls and acceptance

1. Capping motor torque at `0.08 N·m` produces persistent saturation and negative kinetic-energy rate; reject stationary operation.
2. Reducing inertia to `0.0002 kg·m²` yields >10 RPM ripple despite power-ledger closure; show that mean-power improvement alone does not certify speed quality.
3. Omitting `DeltaErotor` or `DeltaEmagnetic` breaks the full-state ledger whenever those stores drift.
4. Original V2 torque, real current-tracking, converter losses, winding parameters, rotor inertia and core-temperature data **not measured**.
5. Agda/Nix and full connected-head CI **not run**. This numerical model establishes neither an original-material hysteresis law nor a theorem of global periodic stability.

### Status against A–H / Ω

| Gate | Status |
|---|---|
| A×B coenergy and two-winding memory reused | Model established; no hardware identification |
| A×E×F finite rotor inertia + motor torque actuator + friction | Numerical source-independent producer, local tests passed |
| Same-machine, same-export current-timing saving under dynamic rotor | Conditional numerical result; storage rates explicitly accounted |
| Finite torque and speed ripple negative controls | Passed on illustrated parameter set |
| True bounded-voltage current controller with switching | OPEN |
| Certified nonlinear periodic orbit, uncertainty envelope | OPEN |
| Calibrated motor electrical input / shaft torque | OPEN |
| Original V2 material and load-response measurements | OPEN |
| Pinned Agda acceptance and original 16 P0–P4 strict gates | OPEN |

Prioritise actual magnetic maps, flux/torque identification, and current tracking before further recovery-converter sweeps. No physical excess energy claimed.
