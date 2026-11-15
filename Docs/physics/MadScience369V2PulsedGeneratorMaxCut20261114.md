# MadScience369 V2 — pulsed/multi-channel generator maximum-cut audit

Date: 2026-11-14. Status: independently created finite Agda source, 4 Python tests passed. **No Agda kernel execution**, no access to the apparatus; **no repository changes/push**.

## 0. Source attribution and non-promotion

Original attributable record: Instagram reel `https://www.instagram.com/reel/DfUzm74S4Hs/` published by handle `madscience369`, user-supplied SRT and two display screenshots (captured/uploaded 2026-11-14). Transcript claims: V2 prime mover spins generator; 2353–2354 RPM; displayed input 285–287 W; ~45 W output with load; displayed input and RPM comparable unloaded; non-self-running but 'precursor'. The speaker's 'definitive proof' is a **claim** and is not independent replication. Screenshots show an oscilloscope `Prd[1]=16.66ms`, ~652 V channel readout and signed Math power ~−287 W, but no reliable assignment of those probes to the physical input/output boundaries.

**Not established by this supplied reel:** device identity or schematic, number of coils/magnets, actual pulse/control strategy, multi-port topology, storage values, measured shaft torque, long steady-state output, independent real-power calibration. User hypothesis: pulsed power and multiple electromagnetic components are likely central. Hypothesis is actively tested, not attributed to the narrator as verbatim claim.

**Separate attributed designs:** Historical Slobodian/Infinity SAV MG10; David Holmstrom/Resonate369 C07/Dodecatron/V1/EZ Spin/AtmoMotor; this @madscience369 V2. Similar names are not sufficient to establish shared identity, ancestry, or ownership. Public unrelated 'Madscientist' forum content does not establish an identity match to @madscience369 and is not a V2 primary source. DASHI finite model and experiment design are new audit work, not inventions of the claimant or proof of their device.

Sources of formal donor concepts:
- `Docs/physics/KSW668CrossProgrammeMaxCut.md`, `DASHI/Physics/Plasma/KSW668FiniteDiscriminatorsExact.agda`: conditional Poynting, signed transfers and provenance limitations.
- `Docs/Investigations/Resonate369ISAVDerivedGeometryMaxCut2026-11-09.md`, `DASHI/Physics/Motors/Resonate369SchematicAdmissionExact.agda`: topology and design-identity attribution firewall.
- `DASHI/Physics/Foundations/ResonantFlightHarmonicPowerPhaseExact.agda`: active vs reactive cycle power.
- `scripts/circuit36927_inductive_recovery.py` and `scripts/circuit36927_switched_capacitor_recovery.py`: independent storage/recovery models.
- `docs/supportive-skepticism-bidirectional-severe-inquiry-sprint-20261026.md`: steelman, source independence, no-go conditionality.

## 1. Physical energy boundary

Define same-cycle integrated signed energy flows for an *identified* whole-system boundary:

`W_motor_elec + W_other_external = W_load + Q_losses + ΔE_rotor + ΔE_coils + ΔE_caps + ΔE_mutual + ΔE_other`.

Motor terminal input is distinct from motor *shaft* input; do not double count both. Input from switching controllers, batteries, chassis/earth, electronics and other ports counts under `W_other_external`. Use time integral of sampled `v(t)*i(t)` for each electrical port, not standalone mean V × mean I. Include timing phase error, bandwidth, current probe sign and thermal state. For a linear constant-inductance network `E_L = 1/2 iᵀ L i` with a physical positive semidefinite inductance matrix; for nonlinear/hysteretic magnetics, use source-backed energy/coenergy/hysteresis integrals, not automatic `1/2 L I²`.

### Candidate hypotheses, none pre-adjudicated

- H1 phase-selective magnetic extraction reduces other drag or iron/copper/switch losses when load attached.
- H2 multi-coil signed reactive circulation and flyback recovery displace losses/time profiles.
- H3 flywheel, coil, capacitor or magnetic storage drains transiently under load.
- H4 additional source/port or unintended return path supplies some work.
- H5 sampling/phase/bandwidth/window mismatch hides true change; signed math display ambiguous.
- H6 sustained unexplained positive residual after metering, storage and calibration are closed.

Do not rule out H1/H2 merely because 'standard generator drag' is expected: compare selected machine's actual torque-angle-current map, counter-torque, thermal losses and switching controls. Do not infer H6 from equal **displayed** values alone.

## 2. Exact finite completed examples (not real measurements)

- Source-attributed nominal point: input = 286 W, output = 45 W, RPM = 2354; topology unverified.
- Nonnegative alternate loss budgets at unchanged input: unloaded `286 = 0 + 286`; loaded `286 = 45 + 241`. This establishes one accounting-compatible mechanism; does *not* identify actual 'other' as measured losses or claim feasibility of 45 W loss reduction in hardware.
- Storage consumption at constant 45 W for an explicitly hypothetical 10/30/60-second load window: 450/1350/2700 J. The SRT does **not** establish a 30 s continuous output measurement.
- Angular speed ~246.51 rad/s; 45 W shaft-power equivalent ~0.1826 N·m (ideal), higher with conversion inefficiency. Motor input at 286 W not shaft output.
- If *solely* an ideal flywheel with initial speed 2354 RPM supplies 45 W for 10/30/60 s, and its final speed is 99% of the initial speed, required minimum inertias are ~0.744/2.233/4.466 kg m²; these are **conditional** counterfactual numbers, not V2 rotor properties. This bound applies only to the selected 1% drop assumption and disregards replenishment.
- `coarseObservationCannotUniquelyIdentifyMechanism` shows two different mechanism labels can have the same coarse 286/45 display; no hardware mechanism has been singled out.

## 3. Exact lemma/phase/deliverable ledger

| Phase/gate | Theorem or physical producer | Status | Acceptance/evidence |
|---|---|---|---|
| P0.A | `pulseTopologyNotEstablished` | Source-written | Agda 2.9 isolated kernel check outstanding |
| P0.B | `sameDisplayedInput`, `outputChanges`, `otherBudgetChanges` | Source-written finite | Kernel check outstanding; arithmetic Python 4/4 pass |
| P0.C | `coarseObservationCannotUniquelyIdentifyMechanism` | Source-written finite | Kernel check outstanding; no device conclusion |
| P0.D | `tenSecondEnergyJ`, `thirtySecondEnergyJ`, `sixtySecondEnergyJ` | Source-written finite | Hypothetical windows only; kernel check outstanding |
| P1.A | `originalV2SourceSelectedNetlist` | OPEN | Original V2 wiring and coil/magnet/count/version evidence, non-identification with unrelated designers |
| P1.B | `originalV2PulseControllerStateTransition` | OPEN | Gate/switch timing, duty cycle, commutation, waveforms, coil terminal polarities |
| P1.C | `originalV2CoupledInductancePSDStorage` | OPEN | Selected coil L matrix vs rotor angle/current, material saturation/hysteresis |
| P1.D | `originalV2MultiPortKCLKVLPowerIdentity` | OPEN | Circuit netlist, KCL/KVL, component constitutive laws, switching energy and diode recovery |
| P2.A | `originalV2ShaftTorqueFromCoenergy` | OPEN | Source-calibrated torque-angle-current map and electromechanical work reciprocity |
| P2.B | `originalV2SameCycleFullEnergyBoundary` | OPEN | Original Maxwell/Poynting differential-integrated weld, full external-port inventory, mechanical/thermal storage |
| P2.C | `originalV2HarmonicRealPowerObserver` | OPEN | Probe calibration, simultaneous voltage/current samples, phase deskew, harmonics, signed conventions |
| P2.D | `originalV2SameWindowLoadVsUnloadResidual` | OPEN | Paired repeated settled runs, controlled load, speed/torque, matched state/endpoints and uncertainty |
| P3.A | `originalV2PersistentResidualAboveUncertainty` | OPEN | Sustained multi-cycle bounded residual that excludes H1–H5 at stated confidence/sensitivity |
| P3.B | `originalV2PulseTimingCausalMechanismSelection` | OPEN | Controlled variation of phases, duty cycle, storage initialization, output loading and independent replication |
| P4 | `selectedV2Agda29GoldenAcceptance` | OPEN | Pin actual PR head, compile Agda modules and imports; run tests/CI, save logs and toolchain hash |

## 4. Experiment design / maximum-information cut

1. **Source root**: link exact V2 build revision and wiring sketch. Request oscilloscope Math expression and probe settings (especially the negative ~−287 W display), output power meter source and method.
2. **All-port power**: synchronize isolated differential voltage probes and calibrated current probes for motor supply, control/gate drives, load, batteries and returns; integrate real signed `v*i`.
3. **Same-shaft physics**: independent torque transducer upstream of generator, high-rate phase-resolved tachometer; separately characterise motor electrical efficiency and unloaded drag.
4. **Storage endpoint**: measure capacitor voltages, coil currents, magnet temperature/field state, flywheel inertia and speed; choose start/end with equivalent controller state and rotor angle after full cycles. Compare long enough that bounded one-time storage depletion cannot explain sustained output.
5. **Interventions**: change load in randomized order, vary pulse timing and phase at fixed speed and similar temperatures, remove/enable recovery path, test dummy resistor vs inductive loading, independently replicate measurement.
6. **Model comparison**: fit H1–H5 to held-out transitions; quantify uncertainty and report residual sign plus confidence interval; only then entertain H6.

## 5. Ownership / merge discipline

Keep one rollup PR per repository. Strongest *physics* donor is `dashi_agda` PR #1504 KSW 668; strongest *pulsed motor design/attribution* donors are the in-repo Resonate369 modules, used only as general mathematical donors. No changes have been pushed to PR #1504 from this artifact: this is a local, unmerged review bundle. Do not claim GitHub branch updated or Agda kernel acceptance.

## 6. Artifact receipts

- `DASHI/Physics/Motors/MadScience369V2FinitePowerDiscriminatorsExact.agda`
- `scripts/check_v2_maxcut.py`
- `tests/test_v2_maxcut.py`
- `Artifacts/v2_finite_scenario_receipt.json`

To reproduce: `python scripts/check_v2_maxcut.py` and `python -m pytest -q tests/test_v2_maxcut.py`. These validate scenario arithmetic and attribution ceiling, *not hardware*.