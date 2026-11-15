# Canonical maximum-cut execution ledger — V2 reluctance × pulsed power × 3/6/9

**Owner:** `chboishabba/dashi_agda` PR #1511. **Revision:** 15 November 2026, second implementation round. **No physical V2 calibration has been obtained.** This ledger supersedes older *status tables*, not their mathematical working or original-source evidence.

## Selected original / ownership firewall

- **@madscience369 V2** owns the Instagram reel and reported approximate rotor speed 2353–2354 RPM, motor electrical-input display 285–287 W, narrated 45 W delivered load; the source does **not** establish winding count, switch timing, shaft torque, pulse circuit or full meter calibration. Output is not an independently certified shaft-work anomaly.
- **Slobodian / Infinity SAV** historical MG10, **David Holmstrom / Resonate369** C07/Dodecatron/V1, and **Donald Smith / Filsinger** are separate original-attribution branches. Borrow *conventional control, recovery and nonlinear mathematics* bidirectionally, without identifying hardware, designs or inventors. Tesla's actual polyphase engineering must not be used to attribute modern DASHI Base369 or a universal 369 efficiency doctrine to Tesla.
- Historical electromagnetics, switched-reluctance and co-energy theory retain their original scientific provenance. New conditional numerical/Agda work belongs to DASHI, not to original device inventors. Distinguish actual test results, model-dependent predictions, symbolic identities and proposed experiments.

## Substantive outputs of this round

1. **P1.1a implemented — finite-bus state dynamics:** `scripts/v2_coupled_pulse_machine_maxcut.py` integrates the *actual current ODE* rather than prescribing an instantaneous rectangular current. Each of m=3..12 phases is driven by a piecewise-constant, three-state full-bridge command `v_j∈{-V,0,+V}` with finite current rise/fall, resistance, mutual inductance, angle-dependent back EMF and finite bus voltage. The controller is a constructed example, not an identified V2 switch network.
2. **P1.1b implemented conditionally — continuous envelopes:** an explicit Gershgorin lower bound on differential inductance and stepwise Grönwall upper bound enclose **the continuous mathematical ODE's** current/lag state, *conditional on the assumed temperature interval and exact state at each step*. The upper thermal bound is independently checked; terminal voltage is bounded exactly by the assumed three-state command. Numerically integrated state endpoints are **not interval-certified**; a full rigorous ODE flow enclosure remains OPEN. Do not call sampled RK4 a certified original-current bound.
3. **P1.2a implemented — thermodynamically passive nonlinear coupled model.** The constructed magnetic co-energy

   \[
   W'(i,\theta,z)=\tfrac12 i^T L(\theta)i+bI_s^2\sum_j\log\cosh(i_j/I_s)
   +g i^Tz-\tfrac12h z^Tz
   \]

   has \(\lambda=\nabla_i W'\), \(\tau=\partial_\theta W'\), \(f_z=\nabla_z W'=g i-hz\), \(\dot z=\mu f_z\), \(\mu\ge0\), \(U=i\cdot\lambda-W'\). Therefore

   \[
   \boxed{i\cdot\dot\lambda=\dot U+\tau\omega+\mu\|f_z\|^2.}
   \]

   For \(L(\theta)\) symmetric strictly diagonally dominant and \(b,h\ge0\), the incremental current inductance is positive and stored magnetic energy nonnegative. The lag term is a **specific passive memory-loss surrogate**, not validated ferromagnetic hysteresis; measured B–H loops, laminated steel loss, eddy currents and thermal material coefficients remain OPEN. The exact two-coil identity was checked symbolically and the full ODE energy ledger independently integrated.
4. **P0.3 improved — independently partitioned clamp conservation** in `DASHI/Physics/Motors/MadScience369V2ClampReroutingExact.agda`. Rather than assuming two separately complete source ledgers, it derives unchanged available energy from a declared partition of **one original clamp dissipation** into returned useful work, incremental switching loss and remaining heat. One concrete quantified witness is proved. Agda compiler acceptance is still OPEN. An actual V2 clamp partition is not known.
5. **P2.1a implemented — finite enumerated Pareto.** Exhaustively compares the modeled candidate rows for m=3..12, multiple pulse-window thresholds and phase leads, including a fixed-copper-mass resistance surrogate. Feasible candidates use the specified conditional continuous bounds. Dominance uses **storage-adjusted** bus work, torque ripple, thermal stress and phase count. This is exact list dominance on *computed approximate values*, not an interval-verified global Pareto theorem or a universal phase optimum.
6. **P2.1b strong negative control — magnetic storage depletion.** A 5-phase model candidate at ~120 W instantaneous mechanical extraction gave ~60 W raw bus export while discharging magnetic storage by ~52 W over the measured revolution. Its storage-adjusted rate is only ~9 W. It must NOT be reported as a sustained advantage. Increasing warmup changes the result, proving the sample controller is not established periodic; the original V2 requires same-state cycle endpoints and a validated longer-run attractor.
7. **P0.2 strengthened analytical reading:** in the original ideal falling-inductance constant-current window, \(F(q)=\arccos(q)/\sqrt{1-q^2}\) decreases on \([0,1)\), because \(\tan x>x\) for \(x=\arccos q\in(0,\pi/2]\). \(F(0)=\pi/2\), \(\lim_{q\to1^-}F(q)=1\), hence ideal copper/shaft ratio may fall by up to \(1-2/\pi\approx36.34\%\), **only while peak current grows without bound**. Enforced current, finite bus, switching and thermal losses remove that singular ideal gain. Real-analysis Agda kernel proof is still OPEN.


8. **P2.2a analytically globally optimal restricted pulse window** in `scripts/v2_pulse_restricted_global_optimum.py`: at fixed shaft extraction, the q-dependent loss is \((K_c\arccos q+K_{sw})/\sqrt{1-q^2}\). Its derivative numerator \(N(q)=K_c[q\arccos q-\sqrt{1-q^2}]+K_{sw}q\) obeys **\(N'(q)=K_c\arccos q+K_{sw}>0\)** on \(0\le q<1\). Thus there is at most one stationary minimum, and the global constrained minimizer is \(q_* = \min(q_{\mathrm{root}},q_{\mathrm{current\ limit}})\). Original toy parameters give **q≈0.7597979451**, 33.86148 W at assumed 45 W *shaft extraction*. This is a rigorous calculus argument with exact SymPy derivative algebra and independently tested numeric root; it is **NOT** the general P2.2 multi-coil switching/global topology theorem, nor Agda real-analysis kernel acceptance.
9. **P1.1c/P2.1c positive near-periodic PWM-average control:** a separately labelled controller uses bounded piecewise-held *averaged PWM voltage*, with an explicit 20 kHz switch-work surcharge. After five warmup revolutions, m=3..12 candidates at approximately **42–43 W assumed shaft extraction** have current/lag end-state differences below 2%, minimal magnetic-storage drift and close integrated energy ledgers. For example m=3 outputs ~22.96 W bus with ~94.7% torque ripple; m=6 outputs ~10.80 W with ~21% ripple; m=9 outputs ~−2.06 W with ~0.4% ripple. This is an honest threefold-vs-other Pareto trade-off for **invented parameters**, and the positive control against the 40 nonperiodic relay candidates. Averaged PWM omits within-carrier current ripple and device-level commutation transients; it is *not* a mathematical exact physical transistor/diode implementation, proof of a true periodic orbit, or the original V2.

## Exact remaining theorem and original-physical lemma ledger

**Definitions:** `SYMBOLIC` = verified algebraically/SymPy, `NUMERIC` = tests on an assumed machine; `SOURCE-WRITTEN` = Agda file authored but no kernel receipt; `CONDITIONAL MODEL` = explanatory model-level component exists; `OPEN` = named gate not discharged at its original requested strength; `PHYSICAL` = original device evidence required. Do not collapse these into “all passed.”

| Gate | Exact lemma/producer | Status after round | Required acceptance / blocking fact |
|---|---|---|---|
| P0.1 | `v2PulsedNonlinearCoenergyIdentity` | **SYMBOLIC, OPEN Agda** | General differentiable multi-coil identity incl. independent actuator work, with source-correct sign convention in the pinned Agda analytic owner; no field calculus kernel proof yet |
| P0.2 | `v2PulseWindowClosedFormAndHighCurrentCounterexample` | **ANALYTIC + NUMERIC, OPEN Agda real bridge** | Actual finite trigonometric/supremum theorem at physically specified current/slew constraints; typed Agda real analysis proof |
| P0.3 | `v2ReversibleClampRecoveryImprovesUsefulWorkConditional` | **SOURCE-WRITTEN stronger constructive lemma** | Agda acceptance of `recoveredClampPreservesInput`, `usefulAfterNotLess`, source-selected clamp partition and switch-energy data |
| P0.4 | `reluctancePermeancePulseAgda29KernelAcceptance` | **OPEN** | Exact-head pinned Agda 2.9.0/Nix typecheck of four new V2 modules plus imported donors; no compiler in this environment |
| P1.1 | `v2PulseControllerFiniteSlewAndBusVoltageEnvelope` | **CONDITIONAL MODEL implemented; full OPEN** | Validated continuous ODE flow enclosure at physical parameters, electrical switching constitutive law, current and thermal limits, not just sampled RK4 |
| P1.2 | `v2NonlinearMutualSaturationHysteresisAndCoenergyWeld` | **CONDITIONAL MODEL implemented; physical OPEN** | Same-device measured coupled \(\lambda(\theta,i,T,z)\), proper material memory/core loss, calibration of all magnetic energy and torque coefficients |
| P1.3/P2.1 | `v2JointPhaseCountPulseConverterParetoCertified` | **Finite model rows + near-periodic PWM numeric; full OPEN** | Strictly periodic/no-storage-drift admissibility, equal input/shaft budgets and total copper mass, globally certified continuous waveforms, m=3..12 Pareto including nonmultiples |
| P1.4 | `originalV2ContinuousVoltageCurrentThermalBound` | **PHYSICAL OPEN** | Source-selected winding/pole parameters, driver topology, semiconductor ratings, thermal and hysteresis data; numerical model is NOT an original-machine bound |
| P2.2 | `generalPolyphaseConstrainedGlobalOptimality` | **ANALYTIC restricted-q global closure; general OPEN** | Certified global objective over explicitly compact physically credible admissible controls; SLSQP/grid and finite dominance are not this theorem |
| P3.1 | `originalV2SelectedWiringPulseReceipt` | **PHYSICAL OPEN** | Original winding/pole/coil count, schematic, switching, auxiliary ports, trace provenance |
| P3.2 | `originalV2PermeanceInductanceFEAWithLeakage` | **PHYSICAL OPEN** | Same-geometry magnetic flux-linkage map, saturation, mutual, leakage/fringe, B–H and FEA or direct measurement |
| P3.3 | `originalV2ActualTorqueFromNonlinearCoenergy` | **PHYSICAL OPEN** | Calibrated signed torque map versus current/angle/temperature on the actual original machine |
| P3.4 | `originalV2ScopeChannelToMechanicalPhaseWeld` | **PHYSICAL OPEN** | Explain the screenshot ~60 Hz channel relative to ~39.23 Hz mechanical rotation with physical channel and phase evidence |
| P4.1 | `originalV2RealPortPulsePoyntingBoundary` | **PHYSICAL OPEN** | Same-clock motor input, shaft torque, all coil/bus/load and auxiliary signed \(\int vi\,dt\) incl. converters, field boundary |
| P4.2 | `originalV2RepeatableCycleStationarityAndStorageEndpoints` | **PHYSICAL OPEN** | Match rotor speed/phase, current, capacitor voltage, magnetisation and temperature; bounded net storage drift, not just steady RPM display |
| P4.3 | `originalV2LoadInterventionIdentifiableResidual` | **PHYSICAL OPEN** | Randomised loaded/unloaded interventions, independent metrology, complete uncertainty and loss/storage rival-model elimination |

**Gate accounting:** sixteen distinct original requested gates (count P1.3/P2.1 once). **None of the actual original-device gates P3/P4 are discharged.** New *subgate* closures this round: conditional P1.1 circuit-ODE implementation, P1.2 passive nonlinear memory construction and exact symbolic identity, P0.3 finite clamp-partition theorem source, P2.2a analytically global optimum of the *restricted* ideal pulse window, and finite Pareto dominance with a nearly periodic PWM-average positive control. Full P0–P2 theorem/kernel gates remain accurately marked open at their stated strong acceptance levels.

## Full energy and measurement contract

For the constructed model, finite pulse/full-bridge input, magnetic memory and terminal energy are integrated independently:

\[
P_{terminal}=\sum_j v_ji_j,
\quad P_{shaft,brake}=-\tau\omega,
\quad P_{Cu}=\sum_jR_j(T)i_j^2,
\quad P_{memory}=\mu\|g i-hz\|^2\ge0.
\]

The corresponding **integrated** conservation identity is
\[
\boxed{W_{shaft,brake}-W_{bus}-W_{Cu}-W_{memory}-W_{converter}-\Delta U_m=0.}
\]

With thermal capacity and cooling, a second *independent* equation verifies \(\Delta E_{thermal}=W_{Cu}+W_{memory}+W_{switch}-W_{cool}\); no heat source is silently assigned back to mechanical work. For the original V2, one must measure actual ports before applying either equation as an observed fact. Beware counting motor electrical input and its delivered shaft power together as independent inputs.

**Controller fairness:** raw reported bus output is NOT a sustainable efficiency metric when \(\Delta U_m\ne0\). The diagnostic \(P_{bus}+\Delta U_m/\Delta t\) accounts for the magnetic inventory change but is not a realizable stationary output unless an actual periodic current/material state is constructed and verified. The relay controller is NOT certified to converge to such a periodic state. An independent averaged-PWM tracking controller has a numerically near-matched current/lag state after five warmup revolutions under selected assumptions; a true periodic-orbit proof and transistor-level PWM/ripple remain OPEN. The P4 storage gate remains an important negative control even for a toy simulation.

## Reproducible commands and deliverables

From PR #1511 exact branch:

```sh
bash scripts/check_madscience369_reluctance_maxcut.sh
# Only on machine with pinned Agda 2.9 and Nix:
RUN_AGDA=1 bash scripts/check_madscience369_reluctance_maxcut.sh
python scripts/v2_coupled_pulse_machine_maxcut.py 12 > /tmp/v2_coupled_pulse_full.json
python scripts/v2_pulse_restricted_global_optimum.py > Artifacts/v2_pulse_restricted_global_optimum_20261115.json
```

The runner must include four new Agda targets and new P1/P2 tests. Static commands, conditional Grönwall bounds and finite floating-point candidate Pareto DO NOT prove original physical hardware or globally certified non-convex optimal control. The full numerical receipt may be more expensive than quick regressions due to the 29-amplitude fair-shaft candidate search.

**Next highest-value mathematical cut:** kernel-check P0; formal validated ODE flow + a *periodic orbit/endpoint certificate* for one model machine; then exact full-waveform Pareto and global bound in a restricted rigorously specified class. Hardware P3 and P4 remain blocked on original V2 instrumentation. Do not open a separate PR for this round.