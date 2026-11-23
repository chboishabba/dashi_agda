# J21 — source-only receiving-wave-to-HF-load Pareto and strict loss floor

23 November 2026 | PR #1537 | native source branch targets J12/J18/J19/J20. **Synthetic dimensionless nine-state candidate, NOT observed Filsinger hardware or a measured natural incident wave.** Retain original Smith/Filsinger attribution and the separate Duga/HAARP/SURA and Maxwell F10/F13 source owners.

## Source and execution truth

The J18 switched nine-state differential equations were independently reimplemented locally and compared numerically with **three** reported J20 source configurations: driver-OFF/wave-ON, driver+wave high-output, and high-capture/ideal-HF. They reproduced their HF-load work, incident/outgoing energy, field loss, switching count, and cycle closure to the displayed numerical precision. The local reimplementation itself was executed under Python, NumPy and SciPy; local SymPy 1.14 checked the strict loss algebra.

A NEW source-typed J21 consumer, scripts/check_smith_filsinger_j21_source_only_throughput_20261123.py, imports the original J20/J19/J18 implementation and pins the original Git blob hashes. **That newly committed J21 file has not yet had a byte-identical native-source execution in the local runtime**; its source assertions are proposed regression gates, not a reported acceptance pass. Do not confuse independent-equation replay with full committed-byte acceptance. No GitHub Actions, CI, or Agda kernel runs.

Pinned upstream file blobs: J12 f5f66e343a979dfe2bc70f68e1e98fce75817653; J18 f4270a475f010874056cfe3cdeff5ee8e43c44eb; J19 cc5cec2d4f881b38b4c01ef79dd93f36e9ef1439; J20 ed09b82287ec1ca0318b4f8e9d355f614d00d894.

## Objective / denominator

Only driver-OFF / independently prescribed wave-ON, on a restored energy boundary, supports the direct **model accounting** fraction eta=HF-load-work/incident-wave-work. With the controller ON this same ratio is **not** a causal environmental attribution. Wave capture =1-outgoing/incident and HF internal delivery =HF-load/(HF-load+gap+coil+freewheel) are distinct objectives.

Keep the existing capacitive OFF return, matched wave handedness -1, zero freewheel resistor, original nonzero HF coil and gap resistances, original positive copper/diode/bleed losses, and 9 dynamical states. Optimize gamma_internal, gamma_rad, k, k_h, Gload; keep driver OFF. Restore the same total stored state and alternating switch event chronology.

## Local numerical results

Baseline J20 driver OFF, wave ON: load 0.1425959 of 90.4778684 incident, 0.15760% model load/incident, 22 spark events.

Selected J21 point: gamma_internal=0.0002, gamma_rad=0.015, k=0.35, k_h=2, Gload=0.52, wave amplitude=1.2, phase=0.3, drive_amp=0.

| Signed energy channel | Work per restored cycle |
| --- | ---: |
| Incident wave | 90.4778684234 |
| Outgoing wave | 31.0579370287 |
| HF useful model load | 46.5616600780 |
| Field damping | 1.6460778386 |
| HF spark gap heat | 2.7936127978 |
| HF coil heat | 1.5524691875 |
| Copper1 + copper2 | 2.9145895837 |
| Diode heat | 0.4031750203 |
| Bank bleed | 3.5483485719 |
| Controller input | 0 |
| Storage drift | -2.1909e-6 |
| Signed energy residual | +5.0784e-7 |

**Load / incident = 51.4619330554%; wave capture = 65.6734430531%.** 22 alternating off/on events, state closure 1.38945e-6, adjacent-cycle event shift 2.0013e-5. The drift and residual are below existing J19 per-cycle gates; this is a numerical restored orbit, not global uniqueness or physical transfer efficiency. Numerical values from separately executed J18-equation reproduction.

At the same selected parameters with gamma_internal=0: driver OFF, field loss 0, HF load 47.1151987, 52.0737% model input-to-load; field damping alone is not the remaining bottleneck. With both incident wave and driver OFF: zero load. With wave OFF but driver ON: HF load 0.5865299, driver work 22.0650385, incident energy zero; its energy cannot be called environmental. Different event branches are expected.

## Exact strict-loss ceiling, not a proposed perpetual-power mechanism

For the existing nonlinear HF capacitor with charge Q(x)=Ch(x+alpha*x^3), stored energy Uc=Ch(x^2/2+3 alpha*x^4/4), the native capacitive-return equation gives

dUc/dt = x i_h - Gload*x^2.

On a restored HF capacitor cycle, integral(x i_h)=Gload integral(x^2). Cauchy-Schwarz implies integral(i_h^2)>=Gload^2 integral(x^2). Hence **Wcoil >= Rcoil*Gload*Wload**. On a driver-OFF restored full boundary, Wincident = Woutgoing + Wload + Wcoil + Wgap + Wfield + Wcopper + Wdiode + Wbleed. All right-hand sinks are nonnegative. Therefore, for positive load:

eta_environment_to_load <= 1/(1+Rcoil*Gload) < 1

when Rcoil and Gload are positive. At the selected model resistances, the ceiling from this ONE floor alone is 97.4659%, observed coil work is 1.552469 and its exact lower bound is 1.210603. Other dissipation and outgoing waves make the actual ratio much smaller. 100% source-to-load transfer is **mathematically excluded in the present finite-loss topology**. A zero-coil-resistance idealisation does not validate a physical zero-loss device.

## Event-chronology and negative controls

Four independent local symmetric perturbation pairs around the selected orbit, with matched 22 event labels:

| Parameter pair | Maximum corresponding event-time shift |
| --- | ---: |
| source_amp 1.1995 / 1.2005 | 0.00042639 |
| phase 0.299 / 0.301 | 0.00183011 |
| k 0.3495 / 0.3505 | 0.00176618 |
| Gload 0.518 / 0.522 | 0.01958139 |

The load pair is perilously close to the J20 strict 0.02 event-alignment cutoff. A nearby k_h=2.005 candidate failed restoration / changed switch count to 32 (versus 22). Elsewhere, gamma_rad=0.02, k=0.3, k_h=2 and Gload=0.56 produced a restored but NO-SPARK 0-event cycle despite positive HF-load work. A no-switch solution is not admissible as the same spark-powered Filsinger candidate. Do not infer differentiability, a unique optimum, or robustness from matching event counts.

## Next Pareto/max-cut weld

Continue exact native-byte J21 replay from the committed branch. Then optimise a **nonzero transversality/chronology margin**, rather than just final Wload; jointly rematch the loaded radiative port using its effective additional external damping and test larger finite neighbourhoods. Report actual externally measurable incident, reflected, dissipative and load energy at a single calibrated physical boundary before promoting any environmental performance or 100% hardware claim. Original Filsinger physical pin edges remain unverified 0/4, and original empirical energy-role samples remain 0/24.
