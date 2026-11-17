# V2 electromechanical efficiency steelman — disjoint A–H tranches and Ω integration

**Scope:** DASHI constructed model, 16 November 2026. Continuation of PR #1519 and the merged motor/Smith–Filsinger work. No measured @madscience369 winding, converter, flux map, generator shaft torque, auxiliary source or full-cycle storage state is available. All published V2 figures here remain *reported*, not independently instrumented.

## Canonical steelman / priority correction

A nonlinear, pulsed, multiphase motor-generator may improve useful electrical output by placing current where magnetic conversion is favourable, retrieving otherwise dumped magnetic/capacitive energy, reducing converter/material losses and altering drivetrain backaction. No energy source beyond signed electrical/mechanical/auxiliary input and initial stored energy is admitted. **Do not prioritise cable geometry unless actual edge speeds, physical lengths or RF behaviour require it.** The Don Smith/Filsinger connection supplies *mathematical analogies* for timed modulation, nonlinear response and recovery, not original V2 circuit topology.

## Tranche owners and actual producers

| Owner | Independent deliverable in this round | Acceptance scope / unresolved issue |
|---|---|---|
| **A×B** nonlinear magnetics × pulse timing | `tranche_ab` in `scripts/v2_tranche_maxcut.py` uses the prior positive-differential-inductance saturating coenergy, checks current cap and common 45 W illustrative shaft input, and searches 81 ideal pulse windows | Finite-grid **ideal rectangular waveform**, not a finite voltage/slew magnetic design theorem; no original winding |
| **C×D** resonance/recovery × converter | `tranche_cd` separately tracks positive running work, recovered running work, conventional vs enhanced clamp work, converter/switch/controller dissipation. `scripts/v2_lc_recovery_tranche.py` additionally constructs a passive two-state normalized LC rotation with independent source kick, loss, extraction and stable storage periodicity | No source-selected resonance/circuit, transistor waveforms, capacitor ESR or thermal certification. LC output is J/cycle, NOT combined with magnetic winding W without a common period or physical interface |
| **E×F** losses × drivetrain | `tranche_ef` composes a generator loss budget into full motor-input, motor-shaft and other-mechanical-work accounts at illustrative 286 W motor input, varying motor conversion efficiency | No observed motor efficiency/shaft torque/heat, and **motor electrical power is not generator shaft power** |
| **G** cross-tranche constrained comparison | `tranche_g` ranks 162 finite current-feasible pulse/recovery combinations with separate bus/copper/converter/controller objectives, 68 nondominated candidates in the current finite grid | **NOT** a global physical optimum: magnetic and current states have ideal initial/final match but DC-bus, thermal, memory and full-system storage stationarity, finite-slew and material mass are NOT certified |
| **H** reel hypothesis discriminator | `tranche_h` provides four distinct whole-boundary conservation counterworlds, ±2 W display sensitivity, and motor-efficiency counterworld | Original V2 source evidence cannot distinguish them; all physical gates remain OPEN |

## Shared comparison and quantitative conclusions

All reported **winding-model four-arm** results hold a hypothetical 45 W mechanical generator shaft extraction fixed, and use 2,354 RPM as a reel-derived setting only. The nonlinear/material/converter numerical coefficients are independently invented. Baseline ordinary rectification already recovers part of the turn-off magnetic energy.

| Fixed-shaft arm | Bus output (illustrative W) |
|---|---:|
| Ordinary | 10.9328 |
| Pulse-only | ≈11.73 |
| Recovery-only | ≈21.59 |
| Joint pulse and recovery | **23.1605** |

The finite 81-window × 2-recovery-setting grid best uses threshold `q≈0.39926`, peak winding current `≈5.558 A`, winding copper loss `≈11.408 W`, converter-related loss `≈9.332 W` and controller work `0.6 W` for this hypothetical fixed-shaft machine. Its improvement over ordinary is `12.2276 W` for this model only. The 18-model scenario stress test changes resistance, assumed converter efficiencies and controller overhead: **12 positive, 6 negative** combined gains. This is *parameter sensitivity*, not a calibrated uncertainty distribution.

**Independent LC energy control:** The passive discrete LC oscillator has `L=40mH`, `C=10μF` (natural f≈251.65Hz), an exactly metered 0.1 J/cycle source kick, energy-preserving rotations, dissipative ring loss, a recovery extraction fraction and charged controller work. At each phase its energy balance closes; for survival × retained fraction below one it has a unique energy-periodic state. Compared with a conventional recovery assumption, higher recovery improves useful J/cycle but excessive controller power makes it worse. These J/cycle results **cannot be added** to the winding's W results without an actual physical coupling and matched timescale.

## H: the 45-W real-world discriminator

For the *complete* motor-generator boundary, with correctly signed losses and changes in stored power,

\[
\Delta P_{\rm load}=\Delta P_{\rm motor,electric}
+\Delta P_{\rm auxiliary}-\Delta P_{\rm losses}
-\Delta\dot E_{\rm stored}-\Delta P_{\rm other\,outputs}.
\]

If the ~286 W motor meter does measure true simultaneous total input, if auxiliaries and other outputs do not change, and the whole system is stationary, an added 45 W load requires an approximately 45 W reduction in losses. A ±2 W changed motor display yields an illustrative required loss reduction of **43–47 W**. That requirement is *not* a consequence of the generator's 45 W hypothetical shaft test: its shaft input was assumed independently.

An explicit alternative: at fixed true input 286 W, a motor whose conversion efficiency rises from 0.6000 to ≈0.75734 would deliver 45 W more mechanical shaft power while reducing motor internal loss by 45 W. The efficiency change is an abstract counterexample, not an inferred real effect. Other energy-closed counterworlds use storage depletion, auxiliary input or incomplete metering. The reel alone cannot identify which world applies.

## Ω: final integration contract

`Ω` requires a single versioned apparatus model with: (1) physical constitutive magnetics and torque; (2) measured/runnable finite voltage/current/dI/dt controller; (3) waveguide or lumped approximation within demonstrated validity; (4) measured independent active/auxiliary/converter work; (5) full thermal/magnetic/electrical/kinetic storage boundary; (6) equal input-shaft/resource budgets for efficiency comparisons; (7) a validated periodic or storage-adjusted observation window; (8) source-identical loaded/unloaded power/torque/probe experiment. When the corresponding evidence does not exist, no theorem or synthetic parameter study can fill that gap.

## Exact next lemma targets (not yet closed)

- `v2ABFiniteSlewNonlinearPulseOptimalityBound` — validated waveform and differential-inductance envelope; real material, current and voltage bounds.
- `v2CDResonantBidirectionalConverterPortWeld` — terminal-current/capacitor state, semiconductor losses and controller work at same clock, no duplicate source.
- `v2EFWholeDrivetrainVariableEfficiencyLoadResponse` — two-state motor/shaft/generator model with measured loss and torque response.
- `v2GCommonResourceRobustGlobalPareto` — global certified frontier under common copper/iron/material budgets and stationary storage.
- `v2HOriginal45WIdentifiabilityAndIntervention` — true signed motor and generator power, shaft torque, independent auxiliary, states and randomised load experiment.
- `reluctancePermeancePulseAgda29KernelAcceptance` — pinned Agda golden kernel; source-only formal constructions are not acceptance.

**Acceptance:** current round 104/104 selected tests pass on reconstructed sources in one local invocation, covering the earlier source-bounded model, PWM negative control, new A–H integration and new LC model; exact original repo checkout/CI/Agda not thereby proven. New 41 regression tests and 18 scenario sensitivity evaluations. Original 16 strict gates remain open.