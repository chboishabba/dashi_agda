# Reluctance / permeance × polyphase pulsed generator: steelman / bidirectional maximum cut

**Date:** 2026-11-15. **Provenance:** original @madscience369 V2 reel in user-supplied 90 s SRT and screenshots (14 November 2026); technical comparison to *independent* Slobodian/Infinity SAV and David Holmstrom/Resonate369 work; DASHI reuse and newly constructed test models. **Status:** symbolic SymPy identities and numerical tests reproducible locally; new Agda source written but not kernel-accepted; **no motor experiment performed**. Scope explicitly excludes attributing any pulse topology to the speaker and excludes attributing DASHI 369/MDL to Nikola Tesla.

## 1. Exact original claims and identification firewall

- @madscience369 V2: narrator reports a motor-driven generator at ~2353–2354 RPM, motor input display ~285–287 W with and without electrical output and ~45 W output when loaded; calls it a precursor rather than self-running. The provided reel **does not establish** phase count, rotor pole count, winding layout, pulse schedule, capacitor, inductor, battery, DC bus, independent shaft torque, output-load impedance, calibrated probe channels, temperature, or durable energy balance.
- Slobodian/Infinity SAV historical MG10: **different attributed hardware and claims**. David Holmstrom Resonate369 C07, Dodecatron, V1, EZ Spin and AtmoMotor: **independent attributed designs**. No identity of devices is inferred by similar terms or similar pulse techniques. Reuse physical mechanisms across designs as *comparative hypotheses* only.
- Tesla rotating-field/polyphase prior art: real electrical engineering. Modern `Base369` phase carriers, `3/6/9` MDL/cost formalism, finite quotient, triadic refinement and automorphic structures belong to DASHI's modern mathematics, not a historical Tesla `369` doctrine.
- Theoretical physics provenance: Maxwell/Faraday/Poynting and conventional reluctance/coenergy machine theory, not new discoveries of DASHI or the V2 inventor. All independent audit code/optimisation decisions are new methodological work and not attributed to the original device designers.

## 2. Found in the actual repository; what's missing

| Repository owner | Reusable, not conflated | Frontier |
| --- | --- | --- |
| `DASHI/Foundations/Base369PolyphaseCharacters.agda`; `DASHI/Foundations/Base369BinaryTernaryRefinement.agda`; `Docs/support/reference/Base369TeslaPolyphase.md` | 3 as coarse phases, 6 binary polarity refinement, 9 ternary resolution; C6/C9 not a divisibility chain, common C18 | Complex finite Fourier and physical harmonic/impedance calibration |
| `DASHI/Physics/Closure/TeslaPolyphaseHistoricalBoundary.agda` | Strong historical attribution firewall | No universal 369 machine optimum |
| `DASHI/Physics/Motors/Circuit36927TypedValuesExact.agda` | R/L/C typed values | Selected V2 netlist and material maps |
| `scripts/circuit36927_inductive_recovery.py`, `scripts/circuit36927_switched_capacitor_recovery.py` | Reference pulse-recovery and storage models | Actual switch routing, energy transfer and loss parameters |
| `scripts/circuit36927_joint_voltage_constrained_drive.py`; `Docs/Investigations/Resonate369ISAVDerivedGeometryMaxCut2026-11-09.md` | Numerically optimised existing fixed-L PM motor control, voltage/ripple lessons, many source-evidence gates | **Original V2** variable-reluctance geometry/FEA, saturation, coupled pulse timing; no transfer of PM results as measured V2 facts |
| `DASHI/Physics/Foundations/ResonantFlightHarmonicPowerPhaseExact.agda` | Active vs reversible reactive storage | Signed same-port cycle measurements |
| `DASHI/Physics/Plasma/KSW668FiniteDiscriminatorsExact.agda` | Conditional signed Poynting law and energy-transfer sign ambiguity | Maxwell current/surface physical weld |

Search of indexed repository found no dedicated `permeance`, `reluctor` or `switched reluctance` physical theorem; `reluctance` lexical matches were generally unrelated everyday-language uses. Therefore this investigation adds *a conditional* permeance/reluctance interface, rather than claiming existing full SRM mechanics.

## 3. Main mathematical weld

For an idealised linear single flux path with reluctance \(\mathcal R = \ell/(\mu A_{gap})\), permeance \(\mathcal P = 1/\mathcal R\) and winding turns \(N\):

\[
 L(\theta)=N^2\mathcal P(\theta),\qquad
 W_m(\theta,i)=\frac12L(\theta)i^2,
 \qquad \tau_e = \frac12 i^2\,\partial_\theta L.
\]

For a generator under this sign convention, \(\tau_e<0\) is braking (excitation during decreasing inductance). A motor uses the opposite phase window. Rotor motion at \(\omega\) and a single phase satisfy:

\[
 v=Ri+L\dot i+\omega L' i,\quad
 iv=Ri^2+\frac{d}{dt}(\tfrac12Li^2)+\omega\tau_e.
\]

The identity is **proved symbolically for this model**. Multi-coil linear coupling replaces \(L\) by symmetric PSD matrix \(\mathbf L(\theta)\) and gives \(W=\tfrac12\mathbf i^T\mathbf L\mathbf i\), \(\tau=\tfrac12\mathbf i^T\mathbf L'\mathbf i\); the corresponding exact SymPy identity was checked including variable mutual coupling.

When saturation is material, use \(\lambda(\theta,i)\), \(W'_m=\int_0^i\lambda(\theta,s)ds\), \(\tau=\partial_\theta W'_m\) and \(W_m=i\lambda-W'_m\). Symbolic checks include the toy \(\lambda=L(\theta)i-b(\theta)i^3\) and show that a naive \(\tfrac12 L(i,\theta)i^2\) can be wrong. A physically admissible saturation model additionally needs positive differential inductance and calibrated B–H/hysteresis data; this toy is not a full material model.

External electrical controller/gate/battery, motor electrical supply, shaft, thermal work, energy storage and any Earth/chassis ports must be measured without double counting. An **ideal inductor/regulator** may return stored energy with zero converter loss, but it cannot create net cyclic energy: the storage derivative vanishes after matched full cycles and exported electrical energy comes from mechanical work or some other accounted input.

## 4. Phase-count optimisation A: ideal best-slope current selection

Assume m independent equal, 2π/m-shifted sinusoidal inductance patterns and zero-time perfect single-phase commutation. Define \(g_m(x)=\max_j\sin(x-2\pi j/m)\). Then

\[
 \min g_m=\cos(\pi/m),\quad \overline{g_m}=\frac{\sin(\pi/m)}{\pi/m},\quad
 H_m=\overline{1/g_m}=\frac{m}{\pi}\log\bigl(\sec(\pi/m)+\tan(\pi/m)\bigr).
\]

For m=2, the best-slope envelope goes to zero at isolated positions, so the selected *single-coil*, unidirectional, constant-torque strategy demands unbounded current. For m≥3 it stays positive. These are **ideal selected-model** results; the geometric sine covering proof is a direct consequence of equal angular spacing, and dense 300,000-sample angular checks agreed to <1e-9 for integrated values (within the tested m=3..12).

| m | worst g | average g | H_m |
| --: | --: | --: | --: |
| 3 | .5000 | .8270 | 1.2576 |
| 4 | .7071 | .9003 | 1.1222 |
| 5 | .8090 | .9355 | 1.0731 |
| 6 | .8660 | .9549 | 1.0491 |
| 7 | .9010 | .9668 | 1.0354 |
| 9 | .9397 | .9798 | 1.0210 |

Adding dimensionless per-phase MDL/switch penalty \(C=H_m+\alpha m\) produces observed test optima (among m=3..12): \(\alpha=.150 \to m=3\), \(.015\to6\), \(.005\to9\), but \(.050\to4\), \(.030\to5\), \(.010\to7\). That is a **positive AND adversarial result**: the numbers 3/6/9 can each be preferred under explicit costs, but none universally dominates. This penalty is *not* an empirically calibrated physical switch-loss curve. Real m changes pole count, winding geometry, mutual fields, voltage and thermal management.

## 5. Phase-count optimisation B: smooth shaped pulsed generator with real-power metering

Independent additional synthetic control family (not actual V2):

\[
 L_j(\theta)=L_0+A\cos(h\theta-2\pi j/m),\qquad
 i_j(\theta)=I\,[\max(0,\sin(h\theta-2\pi j/m+\delta))]^p.
\]

Used constants, selected to give a 2354 RPM *engineering benchmark*, **not fitted to a physical machine**: h=4, L0=20 mH, A=4 mH, R=0.30 Ω/channel, summed mean current-square budget \(\overline{\sum_j i_j^2}=35\,A^2\), 250 V hypothetical terminal limit, 98% converter forward/recovery efficiencies and 0.15 W/phase converter overhead. Search m=3..12; choose pulse phase δ and exponent p in [1.5,3.5] via multistart SLSQP. Results apply only to this waveform family, not arbitrary optimal pulsed controls.

All per-phase instantaneous electrical powers are computed from signed \(v_j i_j\); gross regeneration and gross drive are metered separately. The nonideal bus balance is

\[
 P_{bus}=\eta_{rev}\overline{\sum_j(-v_ji_j)_+}
 -\frac{1}{\eta_{fwd}}\overline{\sum_j(v_ji_j)_+} - m P_{switch}.
\]

Sampled selected results:

| m | bus export W | shaft-to-EM braking W | RMS torque ripple/mean | terminal V peak |
|--:|--:|--:|--:|--:|
| 3 | 39.584 | 62.296 | 64.17% | 166.2 |
| 4 | 39.434 | 62.296 | 32.66% | 144.0 |
| 5 | 39.284 | 62.296 | 12.26% | 128.8 |
| 6 | 39.134 | 62.296 | 2.67% | 117.5 |
| 7 | 38.984 | 62.296 | 0.11% | 108.8 |
| 9 | 38.684 | 62.296 | 0.02% | 96.0 |

The 'best bus export' is **m=3 in this particular cost model**, but a torque-ripple-sensitive mechanical controller can prefer m=6–9 or even nonmultiples. Decreasing per-phase current and voltage peak with m are consequences of the stipulated *fixed aggregate current-squared* and otherwise identical fictitious coil maps; they are not automatic statements for physically fair fixed-copper-mass designs.

**The pulsed reactive-power insight:** the m=3 model has ~265.44 W mean gross positive coil-port flow and ~317.24 W gross negative coil-port flow. The difference is only ~51.80 W ideal export, followed by ~12.21 W converter/overhead loss, leaving ~39.58 W bus export. Thus gross bidirectional/internal pulse energy can be much larger than delivered useful output; correctly recovering that energy matters a lot for efficiency and tells us nothing about over-unity by itself.

**Numerical checks:** single-sample identity residual <4×10^-13 W across baseline models; mean storage-energy derivative near zero (<0.001 W); all selected optimised waveforms were checked at 8× the optimisation angular sample rate; all remained below the *hypothetical* 250 V bound. Selected resampled exported power differs by <0.001 W. **8× sampling is not a certified continuous supremum**: the existing DASHI continuous-voltage-guard work correctly warns that a continuous bound requires an analytic derivative/interval certificate. The source-shaped pulses may also require semiconductor-level slew/gating validation.

## 6. Cross-programme bidirectional and falsifiable controls

**Positive steelman:** (S1) moving reluctance pattern, (S2) recoverable magnetic/capacitor energy, (S3) phase-selective low-drag extraction, (S4) deliberately reduced pre-existing iron/copper/controller losses, (S5) optimal switching and per-channel recovery. Measure every benefit under unchanged apparatus and matched shaft/input power; acknowledge genuine efficiency gains even if no new source appears. For permanent magnet or hysteretic construction, add independent flux linkage, Maxwell stress, and temperature sources before extrapolating reluctance-only predictions.

**Adversarial tests:** (N1) same displayed 286 W and 45 W output can arise if other existing losses fall 45 W (algebraic *possibility*, not explanation proven); (N2) rotor, capacitor, inductor or magnetic storage depletes temporarily; (N3) converter/gate/source/earth supplies additional signed work; (N4) phase-deskew/power-factor aliasing makes high pulsed VA masquerade as net W; (N5) pulse input changes torque/phase despite fixed RPM; (N6) surplus survives same-run independent metering and matched storage endpoints. A baseline 286 W *motor electrical power* is not equivalent to 286 W *generator shaft mechanical power*.

**Cross-pollination against other independent motor designs:** map the Resonate369 V1 reed/bifilar timing and Dodecatron CW/CCW sign rules into *hypothesis families* for polarity and energy-return control, not into actual V2 topology. Import MG10 FET/choke recovery questions as possible *test interventions* only. Import Tesla polyphase characters as harmonic/phase indexing, not false inventorship. Import `ResonantFlightHarmonicPowerPhaseExact` to keep real/imaginary (active/reactive) energy separate. Import KSW `zeroFluxImpliesSignedWork` only as a *conditional* Maxwell budget, not a proven complete device field boundary.

## 7. Remaining exact lemmas and physical producers

| Gate | Named remaining producer | Closure |
|---|---|---|
| A | `originalV2SelectedWiringPulseReceipt` | Independent original V2 coil count, driver/switch timing, auxiliary ports, magnet topology, schematic revision |
| B | `originalV2PermeanceInductanceFEAWithLeakage` | Measured/FEA \(\mathcal P(\theta)\), \(\lambda(i,\theta)\), material B–H, fringe/leakage, PSD coupled L matrix |
| C | `originalV2ActualTorqueFromNonlinearCoenergy` | Same selected current/angle/hysteresis and bidirectional shaft torque map |
| D | `originalV2RealPortPulsePoyntingBoundary` | Full KCL/KVL, per-port synchronous sampled vi, motor efficiency, regulator forward/reverse recovery, Maxwell boundary |
| E | `originalV2ContinuousVoltageCurrentThermalBound` | Valid switch/controller model, physical bandwidth, interval/derivative supremum; don't confuse 8x samples with a proof |
| F | `originalV2RepeatableCycleStationarityAndStorageEndpoints` | Equal initial/final rotor speed, phase, winding/cap charge/temperature or explicit \(\Delta E\) with uncertainty |
| G | `originalV2LoadInterventionIdentifiableResidual` | Randomised loads vs pulse schedules, independent torque, uncertainty interval, competing loss/storage explanations |
| H | `reluctancePermeancePulseAgda29KernelAcceptance` | Pinned Agda 2.9 verification of new module; imported Tesla/V2 donor checks on same branch |
| I | `generalPolyphaseConstrainedGlobalOptimality` | Full controls, winding mass/material cost, saturation, thermal and topology constraints, certified optimisation (not established by finite scans) |

Separate ownership: Agda is golden for exact structural claims; Python is a transparent numerical/model receipt; real hardware claims only from original calibrated experimental evidence; Tesla's authentic rotating-field history is not DASHI's modern 369 mathematics. The present study does **not** show a physical anomaly or disprove every possible V2 implementation.

## 8. Reproduction

`python scripts/check_reluctance_permeance_phase_maxcut.py`

`python -m pytest -q tests/test_reluctance_permeance_phase_maxcut.py tests/test_v2_maxcut.py`

Numerical receipt `Artifacts/v2_reluctance_phase_maxcut_receipt.json`; finite reel countermodels `Artifacts/v2_finite_scenario_receipt.json`; new source `DASHI/Physics/Motors/ReluctancePermeancePulseBoundaryExact.agda`; earlier source `DASHI/Physics/Motors/MadScience369V2FinitePowerDiscriminatorsExact.agda`. No Agda compiler was available in the local model environment. The Agda records supply conditional physical law **interfaces**, not physical producers. The Nat energy no-surplus implication is independently source-written but needs kernel acceptance.