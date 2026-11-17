# Ω — distinct motor/generator storage and factorial load/recovery identification

**Scope:** Exact signed-energy accounting for a proposed independent V2 measurement experiment, **not** calibration of @madscience369 V2. Extends `MadScience369V2OmegaFactorialMeasurementProtocolMaxCut20261117.md`; preserves the eight-arm-repeat palindrome schedule (four experimental arms, each twice per block). Previous source: `scripts/v2_omega_intervention_protocol.py`; new instrument contract: `scripts/v2_omega_split_storage_protocol.py`.

## Correct two-ledger system boundary

The previous testable split uses `motor_input - shaft - motor_loss = 0` and `shaft + auxiliary - load - other - generator_loss - dE_stored/dt = 0`. These split equalities are **too strong when the motor's internal storage varies**. A balanced whole-system energy equation may pass while the motor-side split fails. This is not merely a sensor preference: it changes the mathematical conclusion.

The corrected exact identities, for separately observed motor-side and generator-side states, are

\[
P_{\rm motor}=P_{\rm shaft}+P_{\rm motor\,loss}+\dot E_{\rm motor},
\qquad
P_{\rm shaft}+P_{\rm auxiliary}=P_{\rm load}+P_{\rm other}+P_{\rm generator\,loss}+\dot E_{\rm generator}.
\]

Adding cancels the internal shaft power precisely once and gives

\[
P_{\rm motor}+P_{\rm auxiliary}=P_{\rm load}+P_{\rm other}
 +P_{\rm motor\,loss}+P_{\rm generator\,loss}
 +\dot E_{\rm motor}+\dot E_{\rm generator}.
\]

These are rational identities applied to independent observations. A correct all-port ledger is **necessary, not sufficient**, for claiming a physical boundary is complete or causal mechanisms identified. All powers are **nonnegative magnitudes in a declared oriented direction**; reverse-flow at a port requires explicit instrument-orientation/schema extension, not silently taking an absolute value. Energy-store changes may be signed, computed from separately recorded nonnegative inventory endpoints.

## Factory-grade negative control

The constructed test has 286 W motor electrical input, 200 W transferred to the shaft, 86 W motor loss, and 200 W generator loss, with no load. Modify one run to 201 W shaft transfer, **99 J motor store from 100 J**, and 201 W generator loss. Then

- motor residual: `286 - 201 - 86 - (-1) = 0`;
- generator residual: `201 - 201 - 0 = 0`;
- whole residual: `286 - 86 - 201 - (-1) = 0`.

The original motor-side split (without motor storage) would have reported a 1 W discrepancy, or worse, attributed it to changing motor efficiency. The new stationary protocol rejects that run because `|ΔE_motor| = 1 J` exceeds the assumed zero energy-endpoint uncertainty. With the **explicit** nonstationary option, the same measured depletion is admitted without calling it sustained efficiency improvement. An analogous control tests charging the motor-side store.

## Experimental design and uncertainty

`block,sequence,arm,duration_s` identify the four arms (`00`, `01`, `10`, `11`) crossed for load and recovery. Each appears at positions whose indices sum to seven, cancelling a *common linear time drift* from the factorial estimate in that block. Run order must be preregistered; this schedule alone does not eliminate carryover, treatment-history dependence, nonlinear drift, unknown common-mode calibration errors, or omitted supply and heat paths.

Each run additionally requires motor input, auxiliary input, load output, other output, shaft transfer, measured motor and generator losses, independent motor/generator energy inventories before and after, and uncertainty bounds for all these. The source field `motor_loss_w` or `generator_loss_w` must be obtained **independently** (calorimetry, mechanical friction analysis, core/copper accounting, etc.); it cannot be defined by the balance residual and then used as an independent validation.

All values are exact decimal-to-rational observations. For a contrast \(I_X=X_{11}-X_{10}-X_{01}+X_{00}\), conservative worst-case error bounds sum each of the four arm-mean error bounds. The output reports *deterministic intervals*, **not** confidence intervals. Per-row endpoint error in this schema is an admitted absolute error bound on the **difference** `E_after-E_before` (not merely one endpoint reading); an actual instrument must propagate its endpoint errors into that value. Time-window errors and power calibration correlations must also be bounded externally before use.

A positive output interaction is accepted as a sign only if its worst-case interval excludes zero. Individual motor, generator and whole balances must independently close within reported uncertainties. The `--permit-nonstationary` option never discards measured energy changes.

## Admission rules / remaining full gates

**Closed at constructed protocol and finite algebra scope:** `v2OmegaMotorGeneratorTwoStorageExactPortCancellation`; `v2OmegaMotorStoreDepletionRejectsFalseStationarity`; `v2OmegaFactorialTwoStorageErrorEnvelope`; `v2OmegaPhysicalMeasurementTemplateUnfilled`. The test suite is not an actual experiment.

**Still open:** original V2 topology, independent shaft torque calibration, motor and generator energy-state measurement, measured motor/generator loss distributions, randomized/carryover-controlled physical intervention, full thermal closure, physical converter tracking and switching efficiency, P0 kernel acceptance, and the full 16 strict P0–P4 device gates. The stored-energy inventory also requires physical completeness: rotor kinetic, motor/generator magnetic, battery, capacitor, thermal and other significant reservoirs. Repeating an operating point does not prove complete storage closure.

Run `bash scripts/check_v2_omega_split_storage_protocol.sh`. The generated 32-row CSV remains **blank** by design. No original measurements are included or inferred. This tranche has no need for an invented V2 cable geometry.
