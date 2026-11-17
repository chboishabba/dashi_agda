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


## 15 November 2026 — P1.C finite propagation and Don Smith causal-flight transfer

**Original donor:** `DASHI/Physics/Motors/SmithFilsingerTimeIndexedTransferExact.agda` (`RetardedFlight`, `arrivalNoEarlier`, `twoHopSecondFlight`) and `scripts/check_smith_filsinger_causal_nonlinear_maxcut.py` (`delayed_wave`, signed timed-pump Hamiltonian). Those are original Smith/Filsinger *model contracts*, not evidence of shared V2 hardware. The physical principle comes from relativistic causal Maxwell propagation: **information/causal electromagnetic fronts propagate no faster than the vacuum c bound**, rather than every system variable propagating *at exactly c*. Material, cable, acoustic, mechanical, thermal and other transport channels may be slower. EM phase/group velocity in a dispersive environment is not in general a signal-front velocity.

**Important correction to P1.1/P1.2 claims:** a simultaneous `L(θ) @ i(t)` mutual-inductance matrix is a *spatially lumped quasistatic approximation*. It does not implement a retarded Maxwell field or physically simultaneous state change between distant coils. For longer transmission paths, fast switching edges, distributed capacitance and boundary coupling, a delay/field solver must be used; a small `ω τ` can justify testing a quasistatic limit, but is **not a rigorous model-reduction theorem by itself**.

**New conditional finite flight controls:**
- `DASHI/Physics/Motors/MadScience369V2CausalFlightBoundExact.agda` imports the original Smith/Filsinger `RetardedFlight`; `SpatialLightConeLeg` requires a source-supplied integer-grid lightcone witness `distance ≤ flightTicks × frontSpeed`; `SeparatedPhysicalLeg` additionally requires `frontSpeed ≤ vacuumMaxSpeed`. `positiveDistanceNoZeroFlight` and `noInstantRemoteLeg` exclude a positive-distance link crossing in zero time; two-hop arrival never precedes source launch. **Source written, Agda kernel NOT yet run**; a full spatial Maxwell theorem is not implied.
- `scripts/v2_retarded_causal_network_maxcut.py` and `tests/test_v2_retarded_causal_network_maxcut.py` give 24 new Python regression cases for finite-speed acceptance, invalid superluminal edges, sampled earliest arrival, two-hop causal composition, passive single-link attenuation and quasistatic frequency scale. Sampled `ceil(tau/dt)` arrival is **conservative**; it overdelays each hop by < one sample interval. It must not be grafted into the coarsely sampled motor integrator as one artificial 142 µs step.
- Under an **illustrative, not V2 measured** half-metre cable at `v_front=0.7c`, one-way latency is ≈2.3826 ns, 20 kHz synthetic PWM `ω τ ≈ 0.0002994`, 2354 RPM shaft period ≈25.49 ms, and 180-steps/revolution original integrator step ≈141.60 µs. Quasistatic approximation is plausible at the selected PWM fundamental, but actual switch-edge bandwidth and machine geometry remain unknown.

### Exact new causal obligations (within P1/P3, not new independent original-V2 gates)

| Gate | Exact lemma/producer | Current disposition | Required for stronger closure |
|---|---|---|---|
| P1.C1 | `v2CausalFiniteFlightAndNoEarlyArrival` | Finite conditional Agda source and 24 Python tests | Kernel check imported Smith donor, establish numerical clock units/geometry provenance |
| P1.C2 | `v2DistributedLineMaxwellPassivityAndWavefrontBound` | OPEN | Driven retarded transmission-line/Maxwell boundary model with `front ≤ c`, passive/active energy ports and no acausal advance |
| P1.C3 | `v2LumpedQuasistaticErrorAndControllerLatencyBound` | OPEN | Rigorous approximation error for instantaneous coupled L versus retarded field dynamics at the selected switching rise times, plus controller latency |
| P3.C4 | `v2ActualCableGeometryMaterialAndProbeDelayReceipt` | PHYSICAL OPEN | Device-specific cable/coil lengths, medium/material response, front-speed/dispersion calibration, probe skew and event timebase |

**Acceptance implications:** future P1.3/P2.1 Pareto ranking must enforce finite signal front, gate/sense latency and source-work accounting whenever distributed delays are relevant; do not use delayed observations to double-count stored work. Retarded propagation by itself neither recovers nor creates energy, and the V2 physical P3/P4 gates remain entirely open. The 16 original strict gates remain unchanged; these are four newly explicit causal subgates.
 

## 15 November 2026 — P1.C2/P1.C3 and constructive periodic motor maximum cut (third round)

**Ownership:** This continuation follows the *merged* PR #1511 (merge `512e62f88d91`); current master was checked separately. Changes belong in one dedicated continuation PR, not in closed #1511. Historical @madscience369, separate Don Smith/Filsinger, Slobodian and Holmstrom devices remain distinct. The numerical cable and motor parameters below are illustrative, NEVER source-calibrated.

### P1.C2a: exact passive 1D telegrapher energy and finite reflected-wave network

New `scripts/v2_distributed_causal_line_maxcut.py`, tests and `Artifacts/v2_distributed_causal_line_20261115.json`:

For the 1D, constant-parameter line with per-length L', C', R', G' >= 0,

\[
\partial_x V=-L'\partial_t I-R'I,\qquad
\partial_x I=-C'\partial_t V-G'V,
\quad
\partial_t\tfrac12(C'V^2+L'I^2)+\partial_x(VI)=-R'I^2-G'V^2.
\]

The last equation is **symbolically established as a local identity** for smooth solutions satisfying the equations. The characteristic speed in the **nondispersive** ideal line is `v=1/sqrt(L'C')`; `v<=c` is an **additional physical admission**, not an algebraic consequence of positive L',C' alone. Wave variables `W±=V±ZI`, `Z=sqrt(L'/C')`, carry `VI=(W+²-W-²)/(4Z)`. Finite amplitude packets propagate one cell per tick; both load and source may reflect with signed amplitudes `|Γ|<=1`; an attenuation amplitude `a∈[0,1]` introduces dissipation. The explicit step identity is

\[
 E_{n+1}-E_n=W_{\rm source,n}-W_{\rm load,n}-(1-a^2)E_n.
\]

The source term is **signed net** injection after reflection, not square of the externally prescribed drive. For the tested rational packets (two reflecting boundaries, loss and interference), this is *exact Fraction arithmetic* and the final residual is exactly zero; the continuum algebra also has a SymPy zero residual. This is a **specific passive 1D line**, not a complete 3D Maxwell/coil-field theorem or a physically measured V2 wiring diagram.

The companion **Agda source** `MadScience369V2DelayQueueEnergyExact.agda` implements an exact typed positive-length queue shift with a proposed inductive conservation proof and no-gain consequence. It is **not kernel-accepted**, because Agda/Nix is not installed. This source does **not** assert the rational reflection/telegrapher continuum proof inside Agda.

### P1.C3a: explicit quasistatic-error and causal controller timing bound

For a **matched** delay line and input with certified Lipschitz constant K and |u|<=M, at flight delay τ,

\[
 |u(t)-u(t-\tau)|\le K\tau,\qquad
 |P(t)-P(t-\tau)|\le \frac{2MK\tau}{4Z}.
\]

A reproducible piecewise-linear sampled-input certificate computes K from exactly the specified interpolant. It is **not** a bound for unknown between-sample switching edges, magnetic near-field radiation, nonlinear mutual coupling or a dispersive V2 line. For a frequency \(\omega\) the transfer multiplier is \(e^{-i\omega\tau}\), but *small* `omega*tau` alone does not license a switching-front quasistatic reduction.

For independent rotor observations, a measured remote rotor angle at `t-τ` may be **locally extrapolated** by ωτ without transmitting new data faster than c. Under constant mechanical speed, an uncompensated sinusoidal current-pattern lag `δ=h ω τ` yields averaged ideal reluctance generation multiplied by `cos δ`; a local predictor from previous measurements cancels that phase exactly **only in the exact constant-speed model**. If angular acceleration obeys `|θ¨|<=a`, predictor phase error obeys `|δ_pred|<=h a τ²/2`. A physical feedback-control stability/edge-PWM error theorem remains **OPEN**.

Illustration (not the V2): 0.5 m at 0.7c gives τ≈2.3826 ns; synthetic 20 kHz angular phase ≈0.0002994 rad, while a 2 ns edge has `τ/rise≈1.19` and cannot be dismissed by the fundamental comparison. Do not insert 142 μs of artificial delay into the motor's coarse ODE step.

### P2.1d/P2.2b: constructed *true* periodic generator state and phase cancellation

New `scripts/v2_periodic_causal_motor_certificate.py`, tests and `Artifacts/v2_periodic_causal_motor_certificate_20261115.json` construct a **different restricted linear, independent-winding** model:

\[
 L_j(\theta)=L_0+A\cos(h\theta-2\pi j/m),\qquad
 i_j(\theta)=\frac{I_0+I_1\sin(h\theta-2\pi j/m)}{\sqrt m},
 \quad I_0\ge I_1>0.
\]

The **explicit**, continuously bounded drive is `v_j=R i_j+L_j di_j/dt+(dL_j/dt)i_j`; therefore this exact wave shape **solves** the lumped continuous winding equation, rather than being an unattainable desired rectangular pulse. A conservative analytic voltage envelope bounds every time, not just samples. For R>0 and `L0>|A|`, the one-cycle homogeneous Poincaré factor is

\[
 \rho=\exp\left(-\frac{RT}{\sqrt{L_0^2-A^2}}\right)<1.
\]

The affine period map therefore has **one globally attractive periodic solution** for the specified periodic voltage; the explicitly constructed waveform is that solution. The storage endpoints agree **identically** after every full period. Average extraction/copper are

\[
 P_{\rm shaft}=\tfrac12 A h \omega I_0 I_1,\quad
 P_{\rm Cu}=R(I_0^2+I_1^2/2),\quad P_{\rm ideal,bus}=P_{\rm shaft}-P_{\rm Cu},
\]

which are independent of m under the fixed aggregate current normalization. For this **particular DC+single-sine family**, torque ripple is `I1/(4√2 I0)` at m=3, and **exactly zero at m=4..12** by phase Fourier cancellation. It is not a claim that any physical >=4 phase machine has zero ripple, nor that the nonlinear coupled PWM model has a proved periodic orbit.

Selected illustrative parameters (`2354 RPM` only is reel-derived; L0=40mH,A=12mH,h=4,R=1Ω,I0=1A,I1=.6A,Vmax=320V) yield ≈3.54975 W mechanical extraction, 1.18 W copper, 2.36975 W *ideal* bus, 0.51274 contraction factor. This is not the original V2 shaft or electrical output. A separate restricted unipolar fixed-RMS theorem shows product `I0 I1` maximized at `I0=I1=√(2S/3)` before voltage constraints; it is not the full physical global optimum. Average voltages are ideal **averaged PWM** targets; semiconductor switching ripple, retarded field coupling and converter losses remain open.

### Revised exact remaining obligations — preserve original 16 strict gates

| Gate | Current narrower closure | Exact remaining high-strength acceptance |
| --- | --- | --- |
| `v2DistributedLineMaxwellPassivityAndWavefrontBound` (P1.C2) | Symbolic 1D telegrapher Poynting law, explicit reflection/attenuation packets, rational exact balance | Kernel-accepted spatial PDE/retarded Green solution, realistic dispersion and V2 physical boundary/source coefficients |
| `v2LumpedQuasistaticErrorAndControllerLatencyBound` (P1.C3) | Rigorous Lipschitz delay bound for specified matched line, rotor predictor bounded | Derive nonlinear multi-coil Maxwell-to-lumped error including edge spectrum, near fields and controller stability |
| `v2CausalFiniteFlightAndNoEarlyArrival` (P1.C1) | Prior Agda source/24 tests; new finite-delay conserved packet source | Run Agda 2.9 pinned kernel, specify physical units and original wire geometry |
| `v2JointPhaseCountPulseConverterParetoCertified` (P1.3/P2.1) | Added exact, attractive, same-state **linear** periodic family with phase harmonic cancellation | Saturating mutually coupled nonlinear periodic-orbit/real switching certificate plus full cost/mass matched continuous Pareto |
| `generalPolyphaseConstrainedGlobalOptimality` (P2.2) | Restricted-q global optimum + constructive periodic current family fixed-RMS algebra | Real physical constraints and a certified general nonconvex optimisation bound |
| `v2PulseControllerFiniteSlewAndBusVoltageEnvelope` (P1.1) | Exact continuous input voltage envelope for restricted linear periodic class; previous constructed nonlinear ODE numeric | Validated nonlinear coupled ODE flow, source-device switching and thermal envelope with real components |
| `reluctancePermeancePulseAgda29KernelAcceptance` (P0.4) | Six source modules now targeted in runner | **OPEN** Agda 2.9 pinned typecheck; rectify any errors, exact-head receipt |
| `originalV2*` (P1.4/P3/P4) | **NONE PHYSICALLY CLOSED** | Original source-selected topology, source shaft power, electromagnetic fields, storage endpoints, metrology, repeatability |

Run `bash scripts/check_madscience369_reluctance_maxcut.sh`, and (on a host with pinned Agda/Nix) `RUN_AGDA=1 bash scripts/check_madscience369_reluctance_maxcut.sh`. Do not infer kernel acceptance from Python. **This closes P1.C2a, P1.C3a, and restricted P2 periodic subgates, not their parent full-source gates.**

## Fourth max-cut: nonlinear coupled periodic flux and retarded feedback (15 Nov 2026)

See [NonlinearCausalPeriodicProof](MadScience369V2NonlinearCausalPeriodicProof20261115.md). Under uniform positive incremental inductance ell I <= d(lambda)/di <= Lambda I, positive R and a reversible saturating symmetric mutual coenergy, the flux-state ODE contracts as exp(−Rt/Lambda). For periodic voltage and geometry this establishes a unique globally attracting periodic state, with explicitly constructed bounded-voltage current, exact same-cycle magnetic storage endpoints and signed power accounting. A smooth matched-delayed input has flux-error bound (Mv tau/k)(1−exp(−kt)), k=R/Lambda; a discontinuous 100 V switching edge is a negative control outside this Lipschitz assumption.

**New exact subgates closed analytically at restricted scope:** v2CoupledSaturatingFluxPeriodicPoincareContraction; v2CoupledSaturatingFluxPeriodVoltageEnvelopeAndEnergyClosure; v2DelayedNonlinearFluxResponseGronwallBound; v2UnexpectedSwitchEdgeRejectSmoothDelayBound; v2RetardedNonlinearFluxFeedbackSmallGainExponentialStability; v2RetardedActiveFeedbackPeriodicOrbitAndSignedWork; v2RetardedControllerHighGainUncertifiedCountercontrol. For an active delayed controller K*i(t−tau), b=|K|/ell<a=R/Lambda guarantees exponential history attraction with eta+b*exp(eta*tau)=a and uniqueness of periodic response by Banach's theorem. Feedback work is an **external signed input**, not passive gain. Violation of this sufficient gain margin means only that certification fails.

**Acceptance:** 53 new local Python tests and **216/216 total passed**, full existing local default test runner returned 0. Full new producer, all 53 regression tests, and the split test runner are now **committed to PR #1516 with Git blob parity to the tested local source**. The separate ZIP retains extended receipts and proof details. Exact connected checkout still requires its own independent replay. Full legacy SLSQP artifact producer deferred, Agda compiler unavailable. Original 16 P0–P4 strict gates remain OPEN. Next cut is rigorous hysteretic/lag model + spatial Maxwell/PWM-edge weld and original real hardware metrology.

## 2026-11-15 — fifth maximum cut: passive magnetic memory + genuinely delayed controller

**Canonical proof:** [MadScience369V2RetardedMagneticMemoryProof20261115.md](MadScience369V2RetardedMagneticMemoryProof20261115.md). The new producer `scripts/v2_retarded_memory_periodic_maxcut.py`, tests `tests/test_v2_retarded_memory_periodic_maxcut.py`, and JSON receipt establish a **restricted analytical theorem** beyond the reversible, memoryless predecessor:

| Newly closed *model-level subgate* | Acceptance | Full original gate still open |
|---|---|---|
| `v2RetardedSaturatingMemoryHalanayPeriodicContraction` | weighted flux+lag-state Dini derivative, Halanay positive exponent from explicit sufficient small gain, periodic-state uniqueness and attraction | P1.2 actual hysteresis; retarded continuum Maxwell + Agda real-analysis acceptance |
| `v2RetardedMemoryManufacturedPeriodicStateAndVoltageBound` | explicit time-periodic current and passive z, analytic continuous bus voltage, exact initial/final magnetic state | P1.1 switching edges/semiconductor/real thermal flow; P4.2 original storage observations |
| `v2RetardedMemoryCoenergySignedWorkIdentity` | two-winding exact SymPy residual 0, 3–12 phase numerical pointwise residual near 0, strictly positive memory loss | P0 nonlinear calculus in Agda; P4 all original physical power ports |
| `v2DistributedLineToMemoryMotorSameSignedPortConservation` | exact algebra and rational signed power-port cancellation conditional on same terminal | P1.C2 full coupled wave/Maxwell field + motor solution; P3.C4 physical cables/probe timing |
| `v2RetardedMemoryHistoryIntegrationAndHighGainNegativeControl` | delayed-history method of steps, high-gain rejected as uncertified, superluminal paths rejected | validated arbitrary switching-edge delay solver; general arbitrary material hysteresis |

**Interpretation:** a first-order relaxing magnetic memory is a special dissipative internal-state model, not all hysteretic materials. A pure delay from a guided electromagnetic wave (bound `<=c`) is a distinct model of *control signal arrival*, not a retarded **mutual magnetic field solution**; simultaneous `L(θ)` remains a quasistatic approximation. The constructed controller has a known feedforward periodic waveform plus an explicitly signed active delayed feedback port, not an experimentally observed V2 controller. The passive 1D line/motor signed-port composition is algebraic, not a complete nonlinear PDE boundary wellposedness result.

**Strict gate accounting is unchanged:** the 16 original P0–P4 declarations retain their stated strong acceptance, even though the one-rate magnetic-memory periodicity and conditional energy-port composition subgates have now closed. Next highest-value mathematical cut: rigorous waveform edge/finite slew plus delay under a *dynamically coupled* cable/motor boundary with verified Poincaré/energy contraction, and Agda kernel acceptance. P3/P4 cannot be discharged without original physical measurements.


## 2026-11-15 — sixth maximum cut: dynamically coupled waveguide / nonlinear-memory motor port

**New proof note:** [MadScience369V2WaveguideMotorDynamicPortProof20261115.md](MadScience369V2WaveguideMotorDynamicPortProof20261115.md). **Producer:** `scripts/v2_waveguide_motor_port_maxcut.py`. **Tests:** `tests/test_v2_waveguide_motor_port_maxcut.py`. **Receipt:** `Artifacts/v2_waveguide_motor_acceptance_20261115.json`.

This closes the **discrete dynamic bidirectional port-connection subgate** that was left conditional in the fifth cut. A finite, nonzero-flight waveguide delivers incident waves to the nonlinear reluctance winding; the winding's implicit solved current determines terminal voltage and the reflected wave at the *same signed port*. Feedback is based only on waves already returned to the source. A passive amplitude transmission factor gives explicit nonnegative distributed guide loss. For fixed θ at an electrical step, a nonlinear discrete-gradient solver enforces magnetic-memory/copper dissipation; advancing θ separately meters shaft work at constant magnetic flux and memory.

The exact defined-model identities are `ΔE_line = W_source − W_terminal − D_line` and `ΔU_motor = W_terminal + W_shaft − D_copper − D_memory`; therefore **`Δ(E_line+U_motor)=W_source+W_shaft−D_line−D_copper−D_memory`**. Signed generator and load direction are both supported. The wave identity, including dissipative reflection, is independently checked with exact rational Fractions; nonlinear implicit solves are numerical and conditional on root convergence. The default constructed test's max step ledger residual is ~1e−17 J; no apparatus measurement is implied.

**Causal acceptance:** changing a launch cannot change the remote terminal until after N finite flight steps, or the source's returned wave before 2N. Positive distance and `v_front<=c` are enforced. Unlike a fictitious one-step motor-delay approximation, a 0.5m cable at 0.7c needs 2.3826ns of flight; the default coarse-motor-step line is 12.59km **by construction**. A multi-rate, passive original-device cable/controller weld remains OPEN.

| Sixth-cut exact target | Status | Still-open strict parent |
|---|---|---|
| `v2DynamicBidirectionalWaveguideMemoryMotorSignedPort` | CLOSED restricted discrete model + root-residual tests | Maxwell field/motor wellposedness; original terminal geometry |
| `v2LossyWaveguideMotorDiscreteTotalEnergyBalance` | CLOSED exact finite algebra/Fraction and signed numeric coupled-port check | continuum full PDE/Agda calculus/original energy metrology |
| `v2CausalSourceMotorReturnRoundTripNonanticipation` | CLOSED constructed N/2N trace tests | actual original cable length/material/probe delay |
| `v2DiscreteGradientNonlinearMemoryHeatNonnegative` | CLOSED conditional positive dissipative model and numerical step tests | general rate-independent hysteresis, validated flow, switched semiconductor losses |
| `v2SubNanosecondCableMultiRatePassiveCouplingCertificate` | **OPEN** | passive cross-rate coupling over full mechanical cycle and PWM switching edge spectrum |
| `v2DynamicCoupledMotorLinePeriodicOrbitGlobalAttractor` | **OPEN** | full joint waveguide/magnetic memory/hybrid active controller periodicity |

**Acceptance:** 41/41 new Python tests and 68/68 combined (27 original V2 baseline + 41 new) tests independently completed. The full historical mega-suite was attempted but timed out; do NOT claim complete full-suite replay. Agda kernel remains **NOT RUN** (no compiler in active runtime). The **16 original P0–P4 strong gates remain OPEN**, including original V2 netlist, nonlinear material map, all-port power, shaft torque and metrology. No measured extra energy, universal 369 optimum or Don Smith hardware identity follows.

**Next maximum cut:** mathematical wellposedness and periodic contraction for a dynamically coupled lossy line/memory motor under *finite switched controller* plus passive multirate certification; pinned Agda 2.9 kernel; original V2 physical evidence where available.


## 2026-11-15 — seventh exact finite-flight multirate / periodic coupled-port cut

New source: `scripts/v2_exact_multirate_periodic_port.py` with `tests/test_v2_exact_multirate_periodic_port.py` and full proof `Docs/physics/MadScience369V2ExactMultiratePeriodicPortMaxCut20261115.md`. This is a restricted **linear lag-memory, locally clocked reluctance** model with passive discrete finite-flight packet line, not a nonlinear continuum Maxwell/V2 hardware reconstruction.

**Five new model-level subgates:** `v2FinitePacketMotorMemoryQuadraticEnergyAllStates` (exact rational coefficient-wise identity); `v2CausalBlockSemigroupAllSignedWorkExact` (exact affine/Gramian binary block composition preserving source/terminal/copper/memory/line work); `v2ClockedReluctanceCoupledLineMemoryPeriodicBanach` (exact rational period map, a strict `||P^16||∞<1` contraction, unique periodic state and zero exact energy residual); `v2LocalRotorParameterWorkNoFreeGain` (signed mechanical/modulation energy on local L changes); `v2ShortCableHeldParameterTenMillionTickReduction` (10,697,777-step numerical block reduction at illustrative 0.5m/0.7c with constant L/source, not a smooth rotating-machine certificate).

**Acceptance:** 85/85 new local tests PASS, 126/126 with old dynamic waveguide tests PASS, 139/139 with old retarded-memory tests PASS = 180 distinct targeted tests. Old *aggregate* legacy PWM warm-up suite timed out and is not represented as passing. Agda kernel NOT RUN (compiler unavailable).

**Still OPEN at full strength:** `v2SubNanosecondCableMultiRatePassiveCouplingCertificate` for validated nonlinear/hybrid multirate + interval flow, `v2DynamicCoupledMotorLinePeriodicOrbitGlobalAttractor` for a **smoothly rotating nonlinear coupled mutual/saturated/hysteretic machine**, spatial `v2DistributedLineMaxwellPassivityAndWavefrontBound` and `v2LumpedQuasistaticErrorAndControllerLatencyBound`, Agda 2.9 kernel and all 16 original strict P0–P4 endpoint definitions. Source-specific V2 wiring, field maps, shaft torque, timing and all-port calibrated work are still missing.

## 2026-11-15 — eighth maximum cut: nonlinear multiwinding generator + finite-flight causal port

**New canonical proof:** [MadScience369V2NonlinearExactCausalPeriodicGeneratorMaxCut20261115.md](MadScience369V2NonlinearExactCausalPeriodicGeneratorMaxCut20261115.md). **Source:** `scripts/v2_nonlinear_exact_causal_boundary.py`. **Tests:** `tests/test_v2_nonlinear_exact_causal_boundary.py`.

**Closed in explicitly restricted mathematical scope:**

| New leaf | Actual proof / acceptance | Parent full gate |
|---|---|---|
| `v2NonlinearMutualMemoryAVFAllStateSignedEnergyExact` | Exact polynomial AVF secant and signed finite-flight packet/motor boundary conservation for all admissible states | Full continuum Maxwell and source-selected V2 OPEN |
| `v2NonlinearMutualMemoryAVFImplicitExistenceUnique` | Uniformly SPD flux/memory energy Hessian; strict monotonicity and coercivity of the implicit endpoint map | Actual physical constitutive / nonlinear kernel calculus OPEN |
| `v2NonlinearCausalMultiwindingManufacturedGeneratorCycle` | Nonzero periodic source/line/multi-coil/memory state in exact Fraction arithmetic, mechanically paid electrical export and matched storage endpoints | Original V2 P4.2 OPEN |
| `v2NonlinearCoupledMotorLinePeriodicLocalAttractor` | Rational Jacobian norm `0.9572862540872351… < 1` for 3-winding periodic model (also synthetic 2/4/6/9/12), **local** contraction only | `v2DynamicCoupledMotorLinePeriodicOrbitGlobalAttractor` general rotating hybrid scope OPEN |
| `v2SmoothClockedRotorParameterWorkErrorBound` | Conditional `B D h TV(A)` bound for smooth flux and inverse-inductance motion; does not cover switching-edge discontinuities | Realistic continuous nonlinearity + multi-rate validated flow OPEN |

**Generator-polarity exact ledger (abstract units per period):** rotor/clock mechanical work +0.0275, electrical export 0.002756208295, passive line dissipation 0.006780434870, copper 0.017155664527, magnetic-memory loss 0.000807692308; exact storage difference zero. The source is electrically absorbing this exported work; no energy beyond accounted rotor work.

**Critical limitation:** the exact periodic witness uses `dt=1/4 s`, one flight cell at `v=2c/3`, implying ~49,965 km of cable. It is **not** a 0.5 m cable / real V2 mechanical period. An independent negative control confirms a hypothetical 0.5 m cable at 0.7c has ~2.38 ns front delay, requiring a truly validated nonlinear multirate treatment. No new original apparatus, FEA, torque, switching-waveform, or power meter evidence has been acquired.

**Acceptance:** 66/66 new tests and 192/192 targeted integrated Python tests passed in local standalone mirror. Full legacy aggregate NOT run this round; Agda 2.9 executable unavailable; no Agda kernel PASS. Command: `bash scripts/check_v2_nonlinear_exact_causal_boundary.sh`.

**Strict gate accounting:** all original 16 P0–P4 gates remain OPEN under their original full criteria, as do continuum Maxwell `v2DistributedLineMaxwellPassivityAndWavefrontBound`, validated short-cable `v2SubNanosecondCableMultiRatePassiveCouplingCertificate`, globally attracting arbitrary hybrid `v2DynamicCoupledMotorLinePeriodicOrbitGlobalAttractor`, and source-specific P3/P4 evidence.
## 2026-11-16 — Ninth maximum cut: source-bounded electromechanical efficiency (priority correction)

**Primary user goal:** explain potential efficiency changes from nonlinear reluctance, timed pulses, magnetic/capacitor flyback recovery and reduced copper/core/controller losses. Cable geometry / causal propagation remains conditional on measured edge/RF regimes, **not** a mandatory gate before analysing electromechanical work.

**Canonical new owner:** [MadScience369V2SourceBoundedEfficiencySteelmanMaxCut20261116.md](MadScience369V2SourceBoundedEfficiencySteelmanMaxCut20261116.md). Producer: \`scripts/v2_source_bounded_efficiency_maxcut.py\`; tests: \`tests/test_v2_source_bounded_efficiency_maxcut.py\`; runner: \`scripts/check_v2_source_bounded_efficiency_maxcut.sh\`; receipt: \`Artifacts/v2_source_bounded_efficiency_receipt.json\`.

**Controlled 2×2 factorial, all at the SAME hypothetical 45 W generator-shaft extraction** (not the narrator's 45 W electrical load), using a saturating positive-incremental-inductance co-energy, original reel's approximate 2354 RPM only, and invented R/L/material/controller parameters. Ordinary control already **recovers 80% of flyback**. Advanced recovery returns 95% with extra controller overhead and soft-switching expense. Analytic positive/negative coil-port integration and an independent bus/loss calculation agree:
- ordinary loaded rectification 10.933 W net bus;
- timed pulses only 11.728 W (+0.796 W);
- enhanced recovery only 21.592 W (+10.659 W);
- combined 23.161 W (+12.228 W).
Model timing×recovery factorial interaction +0.773 W. All four have 45 W shaft input and 0 **ideal winding** endpoint storage; DC bus/capacitor/thermal/hysteretic endpoints and finite slew are NOT certified. These are not physical operating points because instantaneous current edges demand unbounded voltage.

**Strong original-claim discriminator:** If the reel's ~286 W displayed motor electric input really remains constant with no change in auxiliary inputs, displaced outputs or stored energy, 45 W incremental electrical load requires **~45 W lower total dissipative loss** (≈43–47 W for a ±2 W input variation), or some equivalent whole-boundary work flow. The 12.228 W *different, loaded-control* toy comparison neither proves nor sufficiently explains that 45 W loaded/unloaded observation. Four exact conservation counterworlds with indistinguishable coarse displays illustrate non-identification: lower losses, storage depletion, auxiliary input or incomplete meter. Motor electrical input is NOT generator shaft power.

**Acceptance:** 57/57 local Python regressions PASS, direct donor linear-limit test, exact algebraic/symbolic co-energy identities, bidirectional port energy and excess recovery/logic cost negative controls. 18 of 45 sensitivity points make enhanced recovery harmful. The branch's exact GitHub checkout/complete historical suite and pinned Agda kernel were NOT executed; no physical V2 tests.

**New named leaves:**
- \`v2SameShaftSaturatingPulseCoenergySignedIdentity\`: restricted analytical + Python/SymPy PASS, Agda real-calculus and physical finite slew OPEN.
- \`v2FourArmCompetentRectifierRecoveryFactorial\`: restricted 2x2 fixed-shaft comparison PASS, actual source-controller and full storage closure OPEN.
- \`v2RecoveryCannotDoubleCountMagneticStoredEnergy\`: exact signed winding balance PASS at mathematical scope; actual switching diode/C/L gate OPEN.
- \`v2Original45WLoadedUnloadedLossDisplacement\`: whole-boundary conditional algebra and four counterworlds PASS; source measurement identification OPEN.
- \`v2FiniteSlewFixedShaftStorageMatchedEfficiencyFrontier\`: OPEN; next decisive mathematical cut to use available nonlinear multi-coil ODE + real switch/thermal energy and matched full state.
- \`v2OriginalV2ControllerSourceReceipt\`: OPEN; source-selected topology, gate trace, λ(θ,i,T), shaft torque, independent ports.
- \`v2V2ExperimentLossSuppression45WIdentifiability\`: OPEN; randomised loads + true motor electric and generator shaft and thermal/stored work.

**Strict original status is unchanged:** all 16 strong P0–P4 endpoints remain OPEN. The next high-alpha work is physically finite-slew, same-shaft and storage-closed efficiency optimisation **before** another standalone cable geometry lemma. No claim of free energy or 369 universal phase-count advantage.
### 2026-11-16 — Ninth cut finite-bus PWM adversarial extension

Independent model-level cross-check of the 2×2 efficiency steelman: [MadScience369V2FixedShaftPWMNegativeControl20261116.md](MadScience369V2FixedShaftPWMNegativeControl20261116.md), source \`scripts/v2_fixed_shaft_pwm_negative_control.py\`, tests \`tests/test_v2_fixed_shaft_pwm_negative_control.py\`. **Reuses** the already existing \`v2_coupled_pulse_machine_maxcut.py\` rather than creating another physical constitutive law. It retains saturating coupled inductance, passive lag memory, model PWM average with ±320 V, 20 kHz switching-energy cost, magnetic near-periodicity and same **hypothetical** ~45 W generator shaft extraction across 3-phase cases (not an identified V2 phase count).

This OTHER model charges reverse converter efficiency 0.95→0.99 (ALL reverse terminal power; not only off-clamp) and separate 0.4 W recovery + 0.2 W timed-control overhead. Result: ordinary 19.320 W bus; timed q=0.1 18.698 W; enhanced recovery 26.193 W; both 25.876 W; over-narrow q=0.45 25.097 W, with higher gross circulation/voltage. Copper loss falls as pulses narrow, but **net bus output can fall** because converter processing and controller overhead dominate. This is a fail-closed control against reading the ideal rectangular pulse's +12.23 W as a hardware guarantee. The two models have different loss/operation regimes; their watts must never be merged into one physical prediction.

**Acceptance:** 6/6 new local regressions PASS, 57/57 earlier tests PASS independently = **63 distinct** targeted local passes; exact tested source Git blob parity recorded on PR. Magnetic state closure is approximate (2% tolerance); capacitor/bus/thermal state not periodic; PWM command is averaged and does **not** resolve individual 20 kHz switching edges; a validated interval ODE/PWM transistor proof and original V2 experiment remain OPEN. No Agda kernel acceptance or full historical suite has been run.

New narrowed leaf \`v2FixedShaftFiniteBusPulseTimingCanHurtEvenIfCopperFalls\` CLOSED at synthetic averaged-PWM scope. \`v2EnhancedRecoveryGrossBidirectionalPortCostsPaid\` CLOSED at this specified reverse-efficiency model. \`v2TrueTransistorPWMAndMatchedWholeStateThermal\` and \`v2V2SourceSelectedPulseLossDisplacement45W\` remain OPEN. **The 16 original strict P0–P4 gates remain OPEN**. Finite causal cable details remain conditional, not a steelman priority.


## 2026-11-16 — A–H disjoint efficiency tranches and Ω integration (programme-scale maximum cut)

**Canonical report:** [MadScience369V2DisjointTranchesOmegaMaxCut20261116.md](MadScience369V2DisjointTranchesOmegaMaxCut20261116.md). This *reorders the next work by physical mechanism*, replacing the previous default priority for cable geometry or isolated causality lemmas. Existing finite-flight constraints remain cross-cutting acceptance conditions.

| Owner | Scope | Mathematical implementation / strict outstanding work |
|---|---|---|
| A×B | nonlinear coenergy and pulse/phase placement | Existing saturated winding pulse family at common shaft input; requires voltage/slew validated physical map and same-resource polyphase global bound |
| C×D | LC resonance, recoverable reactive flow and power electronics | Signed running and clamp recovery plus a separately constructed passive LC periodic-energy model; requires source-welded semiconductors, independent controller work and full switch transition losses |
| E×F | loss redistribution and full motor/shaft/generator response | Explicit motor input-to-shaft conversion and loss allocation; requires original input torque, motor efficiency and state-dependent load response |
| G | simultaneous constrained optimisation | 162 source-independent ideal-pulse candidates, 68 finite-grid non-dominated candidates, 18 cost/efficiency sensitivity cases (12 combined gains, 6 losses); no physical global optimality certified |
| H | 45-W observation discrimination | Same-display storage, auxiliary, meter and loss-shift counterworlds; original topology/metrology/interventions unavailable |
| Ω | one shared complete system | **OPEN** physical identity, fixed material and shaft resources, causal finite-slew controller, exact independent energy accounting, full cycle storage and independently measured loaded/unloaded boundary |

The illustrative **45-W generator shaft input** is an invented comparison condition, not an original V2 shaft measurement. Within this model, ordinary control gives approximately **10.933 W** bus and the best combined finite-grid candidate **23.160 W** (+12.228 W). Conventional rectification already recovers magnetic energy. Another PWM model demonstrates pulse narrowing can *hurt*. A standalone LC model accounts for **joules per cycle**, not additional watts to be silently added to the winding model without a physical shared timing/boundary.

For actual reported motor input near 286 W and added load near 45 W, at matched all-else conditions, an additional 45 W output requires a 45 W reduction in other loss/output, or an independently measured change in input/storage. This is a *discriminator*, not evidence such a loss shift happened. At constant true input, a hypothetical motor efficiency increase from 0.6000 to approximately 0.75734 increases shaft output by 45 W while reducing motor conversion loss by 45 W, demonstrating why the electrical motor meter alone does not identify generator reaction torque.

**New restricted-model target names:** `v2ABFiniteSlewNonlinearPulseOptimalityBound`, `v2CDResonantBidirectionalConverterPortWeld`, `v2EFWholeDrivetrainVariableEfficiencyLoadResponse`, `v2GCommonResourceRobustGlobalPareto`, `v2HOriginal45WIdentifiabilityAndIntervention`. All remain **OPEN at full physical scope**. Existing 16 original strict P0–P4 gates remain OPEN; pinned Agda and original V2 receipts OPEN. The 104/104 reconstructed local Python regression acceptance is not Agda verification or a connected-head CI result. Exact new source and machine-readable data remain in the accompanying local artifact, pending GitHub source upload.


## 2026-11-16 — tenth highest-alpha Ω efficiency cut: smooth finite-voltage winding, closed DC bus, kinetic-storage and observability

**New restricted model producer, 31 tests and runner are committed to PR #1519 with exact local Git blob parity**; the extended numerical trace remains in the conversation's seven-file archive \`v2_omega_smooth_storage_highalpha_maxcut_20261116.zip\`. No original V2 winding/material/shaft data were inferred. This is **not** the original V2 converter; the earlier 104 selected A–H regressions plus 31 new tests passed **135/135 locally** on the reconstructed source, not in connected-head CI. The original 16 strict P0–P4 gates remain OPEN.

**A×B (smooth rather than rectangular current):** the C¹ waveform \`i(x)=I max(sin(x+lead)-q,0)^2\`, reversible saturating coenergy, its exact constructed continuous terminal voltage and periodic magnetic storage endpoints yield a finite, source-independent magnetic generator model. Exact derivative majorants bound current, current slew and continuous voltage, using \`max_samples|v|+M*pi/n\` instead of an unverified sampled maximum. Under invented 45 W generator shaft, 2354 RPM, 40 mH/12 mH, 5 A saturation, 1Ω and ±320 V design limit, the selected constructed waveform has peak sampled terminal voltage 319.048 V and a **continuous mathematical upper bound 319.6242 V**. That is a model winding-voltage theorem, **not transistor/PWM/thermal acceptance**.

**C×D / Ω (shared DC storage):** an explicitly accounted 0.01 F capacitor on an approximately 340 V bus receives signed four-quadrant converter-port power and feeds a modeled constant-power load defined by the exact cycle mean. The bus/magnetic state can close each cycle by construction; the continuous capacitor-energy enclosure accounts for numerical quadrature and between-grid excursions, and the selected case remains in 330–360 V. A physical real-time voltage/current tracking controller, transistor losses, bus supply/charge constraints and thermal stationarity are **OPEN**.

**Same-winding recovery comparator:** q=0, lead=0; ordinary 95% reverse conversion gives approximately 20.670 W synthetic net export, enhanced 99% reverse conversion with **0.4 W extra controller work** gives approximately 28.014 W, an estimated gain **7.344 W**. An analytic Lipschitz integral-error bound on the *difference of the same signed waveform* puts its positive gain in **[7.136, 7.552] W**. This does **not** supersede or combine wattages with the earlier +12.23 W discontinuous-current and finite averaged-PWM comparisons; they use different circuits and assumptions. The 30 enumerated smooth candidates do not certify a full physical global Pareto optimum.

**E×F (kinetic storage):** the conditional finite-interval theorem \`J >= 2 ΔP T / (ω0² (1−(1−ε)²))\` requires rotor inertia **≥0.074425 kg m² for one second** and **≥0.744251 kg m² for ten seconds** if an otherwise unexplained 45 W were supplied solely by deceleration from 2354 RPM with ≤1% observed speed drop. Actual V2 inertia/time data are unavailable, so this is a discriminator, not a source claim.

**H (rank/identifiability):** with only measured motor-input difference and added load, the exact differential balance gives one linear equation for independent auxiliary-input, loss, storage-rate and other-output changes: observation row \`[1,-1,-1,-1]\`, **rank 1, nullity 3**. The original reel is underidentified. Only under equal auxiliary/stored/other ports and an independently verified input change within ±2 W is required loss suppression [43,47] W. Source-selected instrumentation, intervention and uncertainty budget remain open.

**Strongest remaining gates:** \`v2ABFiniteSlewNonlinearPulseOptimalityBound\` beyond constructed feedforward and sample-quadrature; \`v2CDResonantBidirectionalConverterPortWeld\` at actual switched transistor and real shared LC/winding dynamics; \`v2EFWholeDrivetrainVariableEfficiencyLoadResponse\` with real torque/efficiency; \`v2GCommonResourceRobustGlobalPareto\` and full-cycle thermal material budgets; \`v2HOriginal45WIdentifiabilityAndIntervention\`; \`reluctancePermeancePulseAgda29KernelAcceptance\`. Cable layout remains conditional. **No physical original V2 gate closed.**


## 2026-11-17 — Ω highest-alpha converter-admission and experiment-identifiability cut

**Priority correction:** do not promote the smooth-waveform +7.344 W model gain into an achievable converter gain without robust voltage and switching certification. This is a conventional source-bounded efficiency study, not original V2 device identification. Executable producer/tests and full numerical receipt were verified in a local ZIP and must be copied to the repo before connected-head acceptance.

- **C×D converter reverse throughput:** same invented smooth q=0 waveform has 193.596574 W gross reverse and 159.001621 W gross forward port processing. Changing reverse efficiency 0.95→0.99 while adding 0.4 W controller work yields +7.343863 W net gain, with model numerical quadrature interval [7.135639, 7.552087] W. At fixed waveform and overhead, recovery break-even eta is 0.952066. These are not extra input watts or V2 measurements.
- **A×B×G voltage fragility:** conservative winding upper envelope 319.624160 V against an invented 320 V limit leaves only 0.375840 V certified headroom (~0.12%). Adding a conservatively bounded 1 V requirement or +0.1 Ω resistance uncertainty makes this **sufficient voltage bound unable to certify** the waveform. An upper bound above the limit does NOT prove actual infeasibility; tighten and validate the bound or redesign the controller. Switch losses and hardware drive admissibility remain OPEN.
- **H exact observability:** measured differential load-minus-input gives matrix row [1,-1,-1,-1] on auxiliary input, dissipative loss, stored-energy-rate and other-output changes; rank 1, nullity 3. Independent auxiliary, storage-endpoint and other-output measurements give rank 4. A duplicate input-output meter adds no rank. Direct *complete calorimetry* can identify losses only if it also captures otherwise omitted heat/storage channels.
- **E×F experiment sensitivity:** under proposed (NOT observed) guaranteed absolute errors of 1 W load, 2 W motor input, 1 W auxiliary, 2 W stored-power and 1 W other-output, an observed extra 45 W load at zero observed changes in other terms would require dissipation suppression in [38,52] W. This is an interval guarantee, NOT a 95% CI. At 2354 RPM a 45 W shaft-power change is ~0.183 N·m; an illustrative ±0.01 N·m differential torque and ±1 RPM error imply <3 W conservative shaft-power error. Device-specific sensor selection and synchronized random load interventions still OPEN.
- **Local acceptance only:** 30/30 new tests and 159/159 tests across the available integrated subset PASS (17 Nov 2026). The legacy averaged-PWM test module, whose donor file was absent in this reconstructed local test tree, was NOT rerun; Agda/Nix absent; no connected-head CI. **All 16 original P0–P4 strong gates remain OPEN**. Causality/cable geometry remains conditional on actual switching bandwidth.

**Highest-alpha next acceptance:** source-selected V2 winding/controller/topology and independent synchronized real-power+torque+auxiliary+storage measurement. Separately, validate a robust *switching-realizable* recovery efficiency map under finite voltage/current and thermal constraints. Do not equate apparent ~286 W motor input with generator shaft power.


## 2026-11-17 — highest-alpha robust pulse/recovery interval-box cut (local implementation; not yet committed)

The preceding smooth q=0, lead=0 candidate has only 0.375840 V conservative voltage margin and fails when a realistic-*assumption* uncertainty budget is added. A new independent script `scripts/v2_omega_robust_pulse_recovery.py` (currently available in the attached ZIP, **not in GitHub**) compares 30 q/phase candidates at common invented 45 W generator shaft input, analytically closed winding state and constructed bus cycle.

**Assumed uncertainty box, not device specifications:** R increases 0 to 0.03 Ω; winding voltage availability derates up to 2 V; omitted terminal voltage demand up to 1 V; enhanced reverse η≥0.985, ordinary reverse η≤0.955; enhanced controller overhead ≤0.7 W. Four R×derating corners are checked at each candidate while the other bounds are already set at their conservative extremum. The conservative Lipschitz voltage envelope is used as a sufficient feasibility criterion; exceeding the bound does not prove physical infeasibility. No silicon device switching, material hysteresis, current-loop tracking or thermal estimate is claimed.

**Finite Pareto result:** Five of the 30 candidates meet these constructed winding, current, slew, bus-energy and correlated recovery-gain bounds. At q=0, lead=-0.05 rad the highest-outcome admissible candidate has 26.465 W lowest modeled sampled bus output, **only 0.243 V** headroom and a **correlated recovery-gain lower bound ~4.906 W**. Lead=-0.15 rad yields 26.376 W worst modeled output and **5.036 V** headroom; lead=-0.20 rad yields 26.251 W and **6.862 V** headroom. The nominal lead=0 case has **-2.709 V conservative margin**, so it is **uncertified** under the box. These bus output magnitudes are quadrature-model estimates, not statistically or analytically guaranteed lower bounds on real apparatus wattage; the correlated gain lower bound includes the declared Lipschitz quadrature allowance.

**Acceptance:** New `tests/test_v2_omega_robust_pulse_recovery.py` **9/9 PASS**. Available integrated A–H/Ω suite **168/168 PASS** in the local container (17 Nov 2026) excluding the historic averaged-PWM donor test module; no connected-head CI or Agda kernel. The complete 12-file ZIP contains both this cut and the previous converter/observability implementation; these 12 executable/proof files have not yet been committed in this update. The strict 16 original P0–P4 gates remain **OPEN**.

**Next disjoint maximum cuts:** (C×D) measured real converter efficiency/thermal/dead-time versus instantaneous signed current and bus voltage; (A×B×G) tracking-feasible robust waveform and proof of physically bounded sustained storage; (E×F×H) source-selected V2 shaft torque/motor electrical efficiency, loss/auxiliary/storage instrumentation and randomized load intervention; (Ω) same hardware and signed endpoints. Keep cable geometry conditional, not the chief efficiency dependency.
