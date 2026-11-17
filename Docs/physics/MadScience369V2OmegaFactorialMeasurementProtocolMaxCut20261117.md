# V2 A–H/Ω: factorial all-port intervention and measurement acceptance (17 November 2026)

**Research status:** A mathematically specified and locally tested *measurement protocol*, not evidence that the original @madscience369 V2 machine meets it. This source-qualified claim remains OPEN.

## Core intervention

Keep the steelman centred on load backaction, loss displacement and stored-energy release, not cable geometry. The intervention controls two binary factors: electrical load L=0/1 and recovery controller R=0/1. For any measured port y, define the factorial interaction

```
I_y = mean(y_11) − mean(y_10) − mean(y_01) + mean(y_00)
```

The whole-system boundary requires each experimental run to satisfy

```
P_motor + P_aux = P_load + P_other + P_motor_loss
                + P_generator_loss + (E_end − E_start)/T.
```

With independently metered shaft transfer, two further constraints are

```
P_motor = P_shaft + P_motor_loss,
P_shaft + P_aux = P_load + P_other
                + P_generator_loss + (E_end − E_start)/T.
```

The split explicitly assumes changing stored energy lies on the generator/rotor side. A real machine with independent motor-side capacitors, magnetic stores, flywheel or thermal accumulation must meter and allocate those inventories separately. The *whole-system* equation can include all stores without this split.

The interaction identity is exact:

```
I_motor + I_aux − I_load − I_other − I_motor_loss
        − I_generator_loss − I_storage_rate = 0.
```

## Measurement design

The provided local implementation constructs a blank eight-run block of arm labels:
`00,01,10,11,11,10,01,00`, with possible blockwise rotations. Each arm occurs at two clock positions summing to 7. Consequently the difference-in-differences annihilates **common linear clock drift**, but not nonlinear drift, calibration bias, hysteresis/warm-up carryover, switching aliasing or a load-dependent time trend. This schedule is deterministic and prebalanced, not independently randomized.

Every data row must include a duration, calibrated true power at the motor, auxiliaries, electrical output, other outputs, independent shaft transfer, motor and generator dissipation, initial/final stored energy and **absolute measurement-error bounds**. No blank is converted to zero. A strictly stationary run has to match its own storage endpoints within admitted uncertainty, not merely cancel inventory across arms.

The worst-case deterministic interaction error for port p is the sum of its four arm-mean absolute error bounds. A claimed sign requires the entire interval to exclude zero. This is not a statistical confidence interval; correlated bias must be included in the reported error limits.

## Concrete negative controls

The local test suite rejects incomplete port rows, absent arm, unbalanced clock schedule, unmeasured storage depletion, inconsistent motor/shaft/generator accounting and negative uncertainty. It does not infer anomalous power from an unclosed meter ledger. Synthetic exact 7 W load×recovery counterworlds from the existing model are used **only as test fixtures**, never identified with V2 data.

Local source: `scripts/v2_omega_intervention_protocol.py`, tests: `tests/test_v2_omega_intervention_protocol.py`, empty 32-run template: `Artifacts/v2_omega_original_v2_empty_measurement_template_20261117.csv`. The local ZIP was generated and integrity-checked. **The Python/CSV source remains outside this GitHub PR until an exact source import is available.** No connected-head CI, Agda kernel, original data or physical measurements were run.

**Acceptance:** 25 new regression tests and **267/267** across selected A–H/Ω modules passed in the local checkout.

## Exact remaining gates

- `v2HOriginalSourceSelectedAllPortExperimentalReceipt` — full original V2 port map, winding, controller, calibration and complete measured data.
- `v2HCalibratedInstrumentErrorAndCarryoverCertificate` — source-certified instrumental errors, timing/phase deskew, randomization, nonlinear drift and thermal carryover.
- `v2EFSeparatedMotorAndGeneratorStorageWeld` — shaft and separate motor/generator stored-energy inventories with signed physical work.
- `v2CDRealRecoveryTopologySwitchingLossReceipt` — physical converter topology and device-level measured losses.
- `v2GIdentifiedRobustPhysicalPareto` — globally certified physically calibrated efficiency trade-offs, rather than a synthetic finite candidate set.
- `reluctancePermeancePulseAgda29KernelAcceptance` — pinned golden Agda acceptance.

The original 16 strict P0–P4 endpoints remain OPEN. Do not promote a synthetic factorial interaction into evidence of the original machine.
