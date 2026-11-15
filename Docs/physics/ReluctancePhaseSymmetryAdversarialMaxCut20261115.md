# Reluctance/permeance × pulsed power × Base369: symmetry correction and experimental maximum cut

**2026-11-15 · new motor owner.** This builds on the independently authored `ReluctancePermeanceTesla369PulsedGeneratorMaxCut20261115.md` and its source files. The triggering attachments copy two previous cross-programme summaries; they supply **no original V2 schematic, field map, switch trace, machine dimensions or newly calibrated power reading**. Do not broaden this motor implementation into the Filsinger/brane lanes.

## Attribution and admission

- **Original V2 speaker/claim:** @madscience369, user-supplied Instagram reel, ~2353–2354 RPM, motor-input display ~285–287 W under narrated loaded/unloaded states, ~45 W narrated output while loaded. He calls the device a *precursor*, not a self-running machine. These are attributed statements and observed display values, not independently calibrated multi-port power measurements. The source does not prove his winding count or whether his controller is pulsed.
- **Separate hardware:** historical Slobodian/Infinity SAV MG10; David Holmstrom's Resonate369 C07, V1, Dodecatron and other variants. Investigate analogous commutation, flyback, phase/copper allocation and flux geometry **without attributing identical electrical designs or inventorship**.
- **Physics owners:** Faraday, Maxwell, Poynting, conventional SRM magnetic coenergy/virtual work. **Tesla** owns historically documented polyphase/rotating-field engineering, not the modern DASHI `Base369` 3/6/9 symbolic/MDL, 3-adic-style or modular mathematics. DASHI owns this comparative algebra and tests only.
- **Positive literature:** J. M. Stephenson and T. J. E. Miller *Optimal Design of Switched Reluctance Motors* (cf. primary SRM design work); Texas Instruments application report SPRA420A *Switched Reluctance Motor Control* derives `tau=(1/2)i^2 dL/dtheta` under linear magnetics; Mašić, Čorda, Smaka *Computation of Static, Steady-state and Dynamic Characteristics of the Switched Reluctance Motor*, finite-element flux-linkage/coenergy/torque; modern saturation/permeance modelling DOI `10.1049/iet-epa.2019.0987`. Bibliographic source refers to physical prior art, not to the V2.

## A. Existing donors (already merged or owned)

1. `DASHI/Foundations/Base369PolyphaseCharacters.agda`; `Base369BinaryTernaryRefinement.agda`; `Docs/support/reference/Base369TeslaPolyphase.md`: C3, C6, C9 **distinct** finite phase carriers. C6 and C9 are **incomparable refinements**, with common C18. Do not call C3→C6→C9 a nested divisibility chain.
2. `DASHI/Physics/Closure/TeslaPolyphaseHistoricalBoundary.agda`: source attribution gate.
3. `DASHI/Physics/Motors/Circuit36927TypedValuesExact.agda` and `scripts/circuit36927_joint_voltage_constrained_drive.py`: RLC types, voltage/slew constrained optimisers; previous denser-sampling false positives and continuous guard.
4. `DASHI/Physics/Motors/Resonate369SchematicAdmissionExact.agda`: source-selected netlist/polarity interfaces, **not** original V2 wiring.
5. `DASHI/Physics/Plasma/KSW668FiniteDiscriminatorsExact.agda`: signed physical work conditional on field boundary.
6. New `MadScience369V2FinitePowerDiscriminatorsExact.agda` and `ReluctancePermeancePulseBoundaryExact.agda`: V2 coarse display non-identifiability and conditional reluctance/closed energy-budget interfaces; *kernel acceptance outstanding*.

## B. Most important new exact conditional result: no universal mean-power gain from phase duplication

For **identical** coils with the same periodic waveform shape and per-phase reluctance law,

\[
L_j(\theta)=L_0+a\cos(h\theta-2\pi j/m),\quad
 i_j=I f(h\theta-2\pi j/m),\qquad j=0,\ldots,m-1.
\]

Define `A=⟨f²⟩>0`, `B=⟨f² sin x⟩` as *complete-cycle* averages. Fix **aggregate** current squared `S=⟨Σ i_j²⟩=m I² A`. Periodic-translation invariance gives:

\[
\boxed{\overline{\tau}=-\frac{a h S B}{2A}},\qquad
\boxed{\overline{P}_{\rm Cu}=RS},\qquad
\boxed{\overline{P}_{\rm ideal,export}=\frac{\omega a h S B}{2A}-RS}.
\]

**There is no `m` in these expressions.** This proves a *normalisation-controlled comparison*, not a universal physical machine equality. Because the original pulse model holds `S`, `R`, `a`, and `h` fixed and imposes `m × P_switch`, the familiar ~39.58 W (m=3) vs ~38.68 W (m=9) difference is almost exactly the extra imposed 0.9 W overhead. The **mechanically extracted 62.296 W, 10.5 W copper loss and 51.796 W ideal electrical export are effectively identical** over m=3..12.

**Strong counterpoint:** the pointwise sum of time-shifted phase currents, peak voltage and torque harmonics *do* depend on m. Low ripple can improve usable mechanical operation even when mean power is invariant. It is not generally monotone in m for shaped waveforms: one tested p=1.5, delta=0 control gives near-zero synthetic ripple for m=6 and a small but nonzero ripple for m=9. Don't turn an idealized ripple improvement into proof of more usable V2 energy.

**Fair-comparison frontier:** physically different m usually changes conductor mass/length, pole/slot count, torque density, interphase mutual inductance, saturation, peak winding voltage, control semiconductors, core losses, magnetic noise and cooling. A fixed `Σ mean(i²)` is not a fixed-copper-mass constraint. Re-run calibrated optimisation with these quantities held on actual comparable budgets before recommending a winning topology.

## C. Threefold 'sine math' exactly framed

In the *different* ideal best-positive-slope, single-active-phase, instantaneous-switching model,

\[
 g_m(x)=\max_j \sin(x-2\pi j/m),\quad
 H_m=\langle1/g_m\rangle=\frac{m}{\pi}\log\!\left(\sec\frac\pi m+\tan\frac\pi m\right).
\]

For m≥3, minimum g_m is `cos(pi/m)>0`; for m=2 it reaches zero. Three phases are the smallest everywhere-positive case under these strong assumptions, a genuine engineering/combinatorial reason for a threefold baseline. The selected score `C_m=H_m+α m` has **exact adjacent crossings**

\[
\alpha_m=H_m-H_{m+1}.
\]

Within candidate m=3..12, the specific α winning regions are approximately:

| m | α region (dimensionless) | Interpretation |
|--:|:--|:--|
| 3 | α≥0.13540245 | per-phase complexity costly |
| 6 | 0.01373131≤α≤0.02404530 | intermediate ripple/complexity choice |
| 9 | 0.00408199≤α≤0.00579044 | cheap extra angular resolution |

m=4,5,7,8,10,11 and 12 likewise win on nonempty intervals. At adjacent crossing values two counts tie. This is a **conditional optimisation theorem**, not empirical proof of Tesla's supposed universal 369 numbers.

## D. Strongest pulse/regulator steelman and exact energy identity

For a conservative nonlinear coupled magnetic machine define a coenergy `W'(θ,i)` with the integrable constitutive law `λ=∇_i W'`. Define field energy `W=i·λ-W'` and torque `τ=∂θ W'|i`. For the same current, angle and time,

\[
\boxed{\mathbf i\cdot\dot{\boldsymbol\lambda}=\dot W+\omega\tau}. 
\]

Adding resistive loss and the controller, converter, bus and any source ports gives a complete signed physical ledger. This *does not* assume a constant L, nor prohibit mutual inductance or permanent magnet bias. Hysteresis, irreversible magnetisation and temperature dependence require an additional state and dissipative work; a chosen state function without those terms is not a realistic hysteresis model.

In the synthetic m=3 pulse case, gross positive coil-port flow ≈265.44 W and gross negative coil-port flow ≈317.24 W, ideal export ≈51.80 W. Finite converter η and switching overhead reduce actual model bus export to ≈39.58 W. In the mathematically ideal η=1 and zero switching overhead limit, the same waveform yields ≈51.80 W bus export, **not** power beyond ≈62.30 W shaft extraction. This is the direct strongest-form test of a near-perfect inductor/regulator: recovery prevents dissipation, it does not erase reaction torque or make a second unmeasured source appear.

## E. Named maximum-cut leaves (A/B/C)

| Priority | Producer/lemma | Status | Necessary original evidence / acceptance |
| --- | --- | --- | --- |
| A0 | `reluctancePermeancePulseAgda29KernelAcceptance` | OPEN | pinned repo Agda 2.9 typecheck, exact imports; no Agda compiler in test environment |
| A1 | `originalV2SelectedWiringPulseReceipt` | OPEN | source-selected V2 original wiring, switch drive, coil count/polarity, physical source ports |
| A2 | `originalV2PermeanceInductanceFEAWithLeakage` | OPEN | same-machine λ(θ,i,T), B–H, airgap, fringing, leakage, mutual terms; not inferred from video |
| A3 | `originalV2ActualTorqueFromNonlinearCoenergy` | OPEN | physical torque/angle/current and controller load, source-consistent material energy |
| B1 | `originalV2RealPortPulsePoyntingBoundary` | OPEN | time-synchronous motor input, shaft, all coil port VI, DC bus, load, thermal/radiative losses |
| B2 | `originalV2RepeatableCycleStationarityAndStorageEndpoints` | OPEN | same rotor angular phase, speed, capacitor voltages, currents, temps before/after |
| B3 | `originalV2ScopeChannelToMechanicalPhaseWeld` | OPEN | oscilloscope channel topology; distinguish 16.66 ms apparent scope 60 Hz from 39.23 Hz shaft rotation |
| C1 | `originalV2ContinuousVoltageCurrentThermalBound` | OPEN | certified supremum of current, voltage, switching transition + material temp across physical bandwidth |
| C2 | `generalPolyphaseConstrainedGlobalOptimality` | OPEN | comparable material/mass/pole counts, harmonic/saturation models; validated global optimum |
| C3 | `originalV2LoadInterventionIdentifiableResidual` | OPEN | random load order, calibrated independent metrology, same-window storage and confidence bounds |

The 45 W narrated output with approximately unchanged input **only** forces a loss difference or signed stored-energy/other-port difference under an assumed complete energy boundary. In a steady matched cycle with all additional inputs equal, 45 W more output means 45 W less elsewhere (other load or losses); transient storage can temporarily supply it. The coarse reel doesn't distinguish these possibilities.

## F. Acceptance and commands

`python -m pytest -q tests/test_v2_maxcut.py tests/test_reluctance_permeance_phase_maxcut.py tests/test_reluctance_phase_symmetry_maxcut.py`

`python scripts/check_v2_maxcut.py`

`python scripts/check_reluctance_permeance_phase_maxcut.py`

`python scripts/check_reluctance_phase_symmetry_maxcut.py`

Python runs are model receipts, not Agda proofs or physical experiment. The symbolic `m` cancellation assumes a continuous full-cycle integral with shifted identical periodic functions; a grid check estimates quadrature only. Repo branch and Python test acceptance must be recorded against exact commit heads. New Agda modules are **source-written and kernel-UNVERIFIED** until locally checked.