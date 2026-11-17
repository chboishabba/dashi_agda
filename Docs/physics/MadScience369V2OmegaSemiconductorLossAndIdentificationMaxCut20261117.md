# V2 Ω — conditional bidirectional-converter loss model (17 November 2026)

**Source admission.** This is an independent DASHI constructed-model comparison, not a reconstruction of @madscience369 V2 or Don Smith/Filsinger. All component, material and thermal parameters are illustrative. Reel-associated values are approximate 2,354 RPM and narrated motor/output displays; the 45 W *shaft extraction* here is **assumed**, not measured.

## C×D signed loss weld

The preceding A–H/Ω recovery controller used *assumed* reverse transfer efficiencies. The new locally tested `scripts/v2_omega_semiconductor_loss_and_identification.py` defines a nonnegative, averaged *reverse-path* loss class on the **same** manufactured smooth current and terminal-voltage waveform:

```text
Pconduction = Rpath × mean(i² × 1[vi<0])
Pswitch = fPWM × nDevices × (E0 × fraction[vi<0]
                             + EI × mean(|i| × 1[vi<0]))
Pgate = fPWM × nDevices × Qgate × Vdrive
Pdead = 2 × tdead × fPWM × Vdiode × mean(|i| × 1[vi<0])
Delta_P_bus = (1-eta_ordinary) × gross_reverse
              - Pconduction - Pswitch - Pgate - Pdead - Pcontroller_extra
```

The ordinary comparator already recovers 95%; it is **not** a zero-recovery strawman. Gate and controller supply powers are external inputs. Changing physical converter assumptions changes the result; no converter silicon is identified.

## Conditional numerical receipt

For q=0, lead=-0.15 rad and fixed hypothetical 45 W shaft extraction, gross reverse-flow power is ≈191.022 W. Optimistic model parameters: 20 kHz, two devices, 15 mΩ reverse path, E0=3 µJ/event, EI=0.3 µJ/A/event, Qgate=35 nC, Vdrive=12 V, deadtime=150 ns, diode drop=0.8 V, extra controller input 0.4 W.

| Cost | Modeled W |
|---|---:|
| Conduction | 0.08957 |
| Switch events | 0.04386 |
| Gate-drive input | 0.01680 |
| Deadtime diode | 0.00495 |
| Extra controller input | 0.40000 |
| **Total** | **0.55519** |

At these expressly optimistic values, the ordinary model outputs 20.706 W and the enhanced cost model 29.702 W, yielding a **conditional +8.996 W**, not a measured or guaranteed result. The implied ~99.919% reverse transfer is **not a hardware-efficiency claim** and must not be added to earlier alternative 7.34 W/12.23 W comparisons.

Holding all other assumptions fixed, the break-even switching base energy is ≈0.860 mJ per selected event; an adverse 1 mJ switching-energy case or 10 W extra controller demand reverses the benefit. Other negative controls include resistance, gate charge, PWM frequency, diode dead time, temperature and voltage bounds.

The conservative smooth winding headroom is ≈2.54 V after an assumed 2 V derating and 3 V additional demand; this **does not validate switching-edge voltage, gate timing or tracking**. The hypothetical one-node junction steady heat estimate is ≈35.97°C, **not** a semiconductor electrothermal trajectory. The DC-bus energy is periodic only for a *sampled constructed* constant-power sink; capacitor ESR, waveform ripple and thermal inventory remain open.

## Named leaf gates and next acceptance

| Leaf | Status |
|---|---|
| `v2CDSemiconductorReverseBranchSignedLossLedger` | **Closed at specified averaged-model scope** |
| `v2CDSwitchEnergyRecoveryBreakEvenSensitivity` | **Closed conditionally for explicit event-energy model** |
| `v2CDLumpedThermalAndConservativeVoltageAdmission` | **Sufficient model envelope only** |
| `v2OmegaSameWaveformBusInventoryAndMotorShaftBoundary` | Constructed sampled cycle; original system **OPEN** |
| `v2CDRealSwitchingEnergyMapAndThermalFlow` | **OPEN** — datasheets and measured Eon/Eoff(V,I,T), Rds(T), deadtime, controller/driver consumption |
| `v2HOriginal45WIdentifiabilityAndIntervention` | **OPEN** — independently calibrated shaft, aux, storage and all electric ports |

Original **16 P0–P4 strict gates remain OPEN**. In particular, no source-selected V2 part number, waveform, shaft torque, efficiency or full energy inventory has been acquired. Cable geometry remains conditional, not the primary efficiency cut.

**Local acceptance:** 33 new pytest tests and 201/201 across available seven A–H/Ω modules passed. The older historical PWM donor was excluded; no connected-head CI or Agda kernel was run. Source/tests/receipts are in the separately supplied 18-file ZIP; they are **not** in this GitHub commit.
