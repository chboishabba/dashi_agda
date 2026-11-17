# V2 A–H/Ω — pre-registered factorial energy-intervention protocol

**Status:** model-level mathematical and software contract CLOSED; physical original-V2 H and Ω gates OPEN. No source-selected coil schematic, torque map, all-port instrumentation or original measurement series has been supplied. This protocol **does not** manufacture V2 measurements.

## Highest-alpha question

Does increased electrical output under load/recovery interventions correspond to a physically observed change in (i) shaft demand, (ii) motor losses, (iii) generator/converter losses, (iv) auxiliary input, (v) other output, or (vi) stored energy? This distinguishes pulse/recovery benefits from a source/meter omission and avoids granting free shaft power to a claimed generator.

For a whole motor + drivetrain + generator boundary, each measured run must satisfy

\[
 P_{\mathrm{motor}}+P_{\mathrm{aux}}=P_{\mathrm{load}}+P_{\mathrm{other}}+P_{\mathrm{motor\ loss}}+P_{\mathrm{generator\ loss}}+\frac{E_{\mathrm{end}}-E_{\mathrm{start}}}{T}.
\]

Separately verify the two apparatus boundaries, if their shaft and loss meters actually cover those boundaries:

\[
 P_{\mathrm{motor}}=P_{\mathrm{shaft}}+P_{\mathrm{motor\ loss}},\qquad
 P_{\mathrm{shaft}}+P_{\mathrm{aux}}=P_{\mathrm{load}}+P_{\mathrm{other}}+P_{\mathrm{generator\ loss}}+\dot E_{\mathrm{storage}}.
\]

**Important restriction:** the current software allocates all change in measured stored energy to the generator/rotor side and no separate motor-storage term. If the actual motor has changing magnetic/capacitive/kinetic inventory, meter or resolve that separately before using this split. Whole-boundary conservation alone remains valid with complete total storage.

## Pre-registered 2×2 factorial

Four arms `00,01,10,11` use the first bit for electrical load off/on, second bit for the recovery-controller intervention off/on. No physical source/controller topology is inferred. Within each block, every arm is measured twice, in a **palindromic** eight-run sequence such as `00 01 10 11 11 10 01 00`. All arm-mean time indices equal 3.5, so the signed contrast

\[
I_y=(\bar y_{11}-\bar y_{10})-(\bar y_{01}-\bar y_{00})
\]

cancels any common affine clock-time drift. Run multiple blocks with rotated schedules chosen **before** observation. This is a restricted design symmetry, not randomization and not immunity to nonlinear drift, carryover, warmup, sensor aliasing or a load-dependent time trend. When randomized actual-run ordering is feasible, use precommitted randomized balanced schedules and preserve matched-time diagnostics.

The port contrast closes exactly:

\[
I_{\rm motor}+I_{\rm aux}-I_{\rm load}-I_{\rm other}-I_{\rm motor\ loss}-I_{\rm generator\ loss}-I_{\dot E}=0.
\]

For measured absolute error `e_{a,p}` in the two reads of arm `a` and port `p`, define arm-mean error as `(e_1+e_2)/2`; then the deterministic worst-case interaction error is `Σ_{a∈{00,01,10,11}}e_{a,p}`. The sign is accepted only when the entire interval excludes zero. No Gaussian, independence, cancellation or confidence-level claims are made. Calibration and correlated systematic errors **must be included** in each stated per-row bound.

## Acceptance and failure gates

1. Strict CSV schema: no missing values, no substituting absent meters by zero; signed power orientation specified by the instrumentation and reconcilable with the schema.
2. Positive observation durations; nonnegative absolute error bounds and nonnegative stored-energy inventory.
3. Each experimental block has eight unique clock positions, each factorial arm appearing exactly twice at time-symmetric positions.
4. With strict stationarity enabled, each *individual run* must match its storage endpoint within admitted measurement uncertainty; mean cancellation is insufficient.
5. Whole-system and independently identified motor and generator sub-boundaries close within the sum of their independently certified measurement bounds.
6. Interaction energy identity closes within propagated contrast bounds; unaccounted ports reject rather than becoming 'anomalous energy'.
7. Positive load×recovery interaction can be claimed only when its deterministic output interval excludes zero. **Attribution to reduced loss additionally requires independent calibrated loss / thermal and shaft evidence.**
8. Pre-declare observation window, settling, instrument calibration, treatment carryover, line-frequency/phase deskew, rotor/shaft sensor location and all energy reservoirs (rotor, bus capacitors, magnetic memory, thermal reservoir).

## Baseline formal and regression provenance

This source reuses `v2_omega_load_intervention_weld.py` for a deliberately **synthetic** exact 7 W load×recovery interaction. It checks the test protocol on a known-consistent mathematical counterworld; it does **not** turn that counterworld into a V2 observation. The instrument template remains unfilled.

Reproduce with `python -m pytest -q tests/test_v2_omega_intervention_protocol.py` and optionally with the combined runner `bash scripts/check_v2_omega_intervention_protocol.sh`. Generate an empty 4-block CSV using `python scripts/v2_omega_intervention_protocol.py --template measurements.csv --blocks 4`. To audit real data, fill every measurement and its calibrated absolute error, then run `python scripts/v2_omega_intervention_protocol.py --measurements measurements.csv`.

This proof is Python/Fraction exact for the asserted algebra, with no Agda 2.9 kernel execution. No empirical V2 readings have been imported. Strong original P0–P4 gates remain OPEN.

## Next strict dependencies

- `v2HOriginalSourceSelectedAllPortExperimentalReceipt`: original netlist, intervention clock, shaft and electrical metrology, storage/thermal coverage and calibrated full CSV
- `v2HCalibratedInstrumentErrorAndCarryoverCertificate`: traceable meter calibration, uncertainty covariance or conservative worst-case bounds; nonlinear drift and carryover controls
- `v2EFSeparatedMotorAndGeneratorStorageWeld`: independent motor-side and generator-side inventories, heat/shaft uncertainty
- `v2CDRealRecoveryTopologySwitchingLossReceipt`: original physical converter with measured switching loss and returning source port
- `v2GIdentifiedRobustPhysicalPareto`: a calibrated optimum conditional on the measured system, not the original finite toy candidate list
- `reluctancePermeancePulseAgda29KernelAcceptance`: Agda golden and source-connected kernel check

**Roadmap priority:** real intervention receipt and real electromechanical identification outrank further arbitrary cable geometry and new model-level periodicity constructions.
