# Smith/Filsinger / Sun–Earth: exact phases, deliverables and remaining lemmas
**16 November 2026 — programme continuation / user-origin steelman.**
**Scope and verification:** source-audited on PR #1524 at `ba5269f4b043836eeaec8f898d9a91932b933c5c`, PR #1521 at `88b53fcb24b68bc37e0834a00a55279306f87018`, and PR #1519 at `792646c73d7d05f4a38cf32afc3261aa3a08f23b`. This roadmap is not a new kernel result or physical device receipt. Prefer Agda golden, local pinned check; no ESD writes, no forced TOE promotion.

## Steelman / source-owner boundary
A relatively small, timed, nonlinear electromagnetic controller may sustain two coupled, phase-offset source/receiver branches with **propagation, causal delay, material memory and source backaction**. By altering physical impedance/mode overlap and environmental response it may increase useful energy transferred from a *separately replenished* source. Controller work, initial donor charge, outgoing energy, loss, material-modulation work and real useful output remain explicit. Filsinger's recorded Earth-ground apparatus, *proposed* common-midpoint/golden plate and Don Smith's independently sourced figures are NOT established as one hardware identity. User's source/sink+solar+rain interpretation is a new conditional extension.

Distinct source regimes:
- **W (coherent wave):** two-port TCMT with natural incident wave, driver wave, spatial modes, reflection `s_-=-s_+ + K†a`; external wave/controller phase may matter if coherence is physical. Random independent natural phases erase mean quadratic cross terms in the specified linear regime. Actual external coherence and power not measured.
- **B (biased DC/slow source):** independent DC/low-frequency natural Thevenin source, with *internally* anti-phased controlled load/conductance branches; no externally supplied RF phase reference is required. For matched ideal fixed-R source anti-phase can stabilize total conductance and reach its fixed-source maximum but cannot exceed it or prove environmental source origin.
- **N (nonlinear history-dependent):** open, dispersive Maxwell–plasma–soil/cloud state where source response may depend on delayed controller action, memory, field coupling and natural replenishment. This is the main physical target. Neither W nor B alone establishes N.

## Headline acceptance status
- Merged producers: PR #1507 causal nonlinear source-port BIDI, #1514 hybrid/regime/source-identity, #1515 two-kernel acoustic spectral observation; each remains scope-specific. #1519 multirate motors is a *methods donor*, not Smith's original device.
- Draft #1521: nonlinear dispersive material port, Hall/Pedersen work separation, 1D line+finite donor+recharge and source admittance. Its M1–M7 have source-equivalent local numerical/symbolic receipts; M8/M9 abstract repeatable-cycle bounds, no Agda exact-head receipt and no original physics admission. Replenishment deficit persists in example.
- Draft #1524: `SmithFilsingerSunEarthCoupledSourceExact.agda`, `SmithFilsingerMidpointPhaseWorkExact.agda`, coherent source-controlled 2-mode/2-port (17 local tests), complementary DC Thevenin branch (12 local tests), **29/29 local source-equivalent tests reported**; no pinned kernel nor independently run current-head verification. Newest PR head should always be read before executing.
- No original-world same-unit source work, port geometry, calibrated phase, climatic-control gain or physical atmospheric bridge demonstrated.

**Important naming:** programme delivery phases Q0–Q6 below are separate from the canonical *physical gate* identifiers S0/P1/P2/R1/R2/R3/D1/D2 already used in #1521.

## Dependency-ordered delivery phases
| Delivery phase | Status | Concrete deliverable | Promotion test |
|---|---|---|---|
| Q0: original source + source identity | Documentation completed; physical S0 open | Typed reel/patent/claimed-plate graph with source IDs and separate ground/portable candidate configurations | Every claim traceable to source; not inferred pin continuity |
| Q1: exact finite mathematics | Models source-authored; kernels open | Agda checked source-separated signed port bounds, anti-phase matching theorem, incoherence negative controls, two-world non-identifiability | Pinned Agda 2.9 exact-head + source-equivalent tests; explicit hypotheses |
| Q2: full time-domain physical operator | Open, with #1519/#1521 method donors | One causal spatial field/material memory/receiver transfer operator and passive energy identity | Strict causal propagation, memory, Hall/Pedersen, Maxwell/Poynting, passivity, retarded phase at receiver |
| Q3: physically bounded source access | Open | Site/source-specific measured terminal `Voc, Rs` or nonlinear loaded `v(t),i(t)` kernel and uncertainty; real plate/electrode geometry | Independent natural real power, calibrated same-object return and two-load / time-varying counterfactual |
| Q4: one selected actual apparatus | Open | Driver+shunt+coils+cap banks+switch+diodes+ground/plate+acoustic source model with one parameter set | Reproduce start/hot/null/shutdown and *actual* power, no cross-reel conflation |
| Q5: sustainable matched extraction | Open | Repeated steady/cyclic tuned/control source–receiver, natural source backaction and no storage drawdown | Positive net independently replenished natural work at actual receiver, controller/drive/loss all metered |
| Q6: environmental/atmospheric extensions | Open and conditional | Sun-wind/ionospheric, plasma THz/IR, cloud rain/local cold-pool kernels and independent measured gain; TOE intake only after acceptance | All mechanism arrows sourced and quantified; local rain cooling distinct from global TOA effect |

## Exact remaining MATHEMATICAL lemmas: unclosed / unpromoted
| ID | Exact target | Reuse owner / proof strategy | Current cut |
|---|---|---|---|
| F01 `phaseCommonDriverRatioInvariant` | for energy-normalised linear `a_j=H_j s` with fixed nonzero common `s`, positive amplitude rescaling leaves `arg(a_2/a_1)` unchanged | #1524 `SmithFilsingerMidpointPhaseWorkExact`, two-mode Python | local numeric, no general Agda proof |
| F02 `receiverPhaseIncludesRetardedPath` | `Δφ(x,ω)=arg(s2H2/s1H1)`; pure delays give `−ω(τ2−τ1)` modulo 2π, but not a universal dispersive-group-delay law | `SmithFilsingerTimeIndexedTransferExact`, #1519, #1524 | pure-delay numeric, no physical-operator weld |
| F03 `detunedFreePhaseCannotRemainFixed` | two undriven uncoupled modes with distinct real frequencies cannot have constant relative phase on any nontrivial interval; distinguish common-drive lock | #1524 two-mode tests | not Agda general math |
| F04 `independentUniformPhaseCancelsQuadraticCrossTerm` | phase average of linear coherent cross term vanishes when external phase is independent uniform; no such claim for nonlinear/hysteretic response | #1524 `incoherent_phase_average` | 128-sample numeric, analytic/Agda generalisation open |
| F05 `fixedSourceMatchGapSquare` | `Voc²/(4Rs) − Voc² G/(1+RsG)² = Voc²(RsG−1)²/[4Rs(1+RsG)²]`, `Rs>0,G≥0` | #1524 DC matching SymPy, #1521 SP2 | symbolic local, Agda theorem over rationals/ordered field open |
| F06 `complementaryConductanceFlatAtPi` | `G1=g+a sin(t),G2=g+a sin(t+π)` gives `Gtotal=2g` at all t; with `2g=1/Rs` output attains fixed-source match bound | #1524 DC script | symbolic local; exact Agda/closed model theorem open |
| F07 `phaseOptimumDependsOnSourceImpedance` | counterexample that anti-phase is universal optimum, when `Rs`, load, delays or coefficient change | #1524 DC source-mismatch comparison | model counterexample local; portable finite exact witness unpromoted |
| F08 `naturalPortWorkMustBeSigned` | incident minus outgoing; if natural incoming=0 then naturally *net supplied* power cannot be positive in passive model; controller may radiate outward | `MidpointTwoPortWorkExact` + #1521 TCMT | Nat counterexample authored, physical port weld open |
| F09 `phaseReadoutCannotIdentifyNaturalSource` | two physical-source classifications with identical coherent-phase observation reject unique inference of source from phase alone | `MidpointTwoPortWorkExact.phaseReadoutAloneCannotIdentifyNaturalWork` | source-authored Agda, kernel open |
| F10 `retardedNonlinearMaterialEnergyIdentity` | Poynting + time-varying polarization/relaxation/modulator work with causal constitutive memory; no unaccounted material-work term | #1521 M1–M4 + existing Maxwell adapters | symbolic 1D/constitutive model only, 3D coupled theorem open |
| F11 `wholeSystemMatchedTrajectoryDifference` | same initial state/exogenous forcing: `δW_load−δW_drive−δW_mod = δW_nat−δW_loss−δU_final` for same well-defined boundary, including outgoing radiation in loss term | #1521 M4/M9, #1524 two-port | proof/physical source backaction weld open |
| F12 `replenishedCycleVsTransientDiscriminator` | full-state cyclic return implies useful work must be paid by ongoing source+driver+controller, not initial donor; positive net after costs requires independently positive replenishment | #1521 M8/M9 `RepeatableSourceReceiverCycle`, `TerminalCapRepeatableCycle` | abstract bounds source-authored, kernel/real-world open |
| F13 `fullColumnSoilIonosphereAccessWeld` | physical collection estimate using calibrated `J,E,σ,ε,Σ_{Hall/Pedersen}`, geometry and retarded boundary response | #1521 P2-PHYS and `AdmittedNaturalAccessCap` | simplified slab/column only |
| F14 `allRegimesOnePhysicalParameters` | one selected apparatus model explains startup, hunting, phase nulls, dual acoustic shutdown peaks, simultaneous electrical power | merged #1515 source audio + #1521 | original A1/A2/A3/B1/B2/B3-PHYS all open |
| F15 `sourceEnvironmentLoadSameCycle` | real signed natural work positive after drive/controller and losses over repeatable matched cycle with source replenishment and terminal access | original C3/R3; #1521 + #1524 | decisive physical endpoint open |
| F16 `electricControlRainColdPoolCausalGain` | independently attributable controller→cloud field→drop size/rate→evaporation/cold pool→surface anomaly, with energy/heat and counterfactual uncertainty | #1524 S4a/S6a/S6b/S6c/S7a, original Tinsley etc | end-to-end physical link open |

## NON-MATHEMATICAL hard receipts, not derivable from re-labelling Agda Set fields
- **S0/A1** original Smith vs Filsinger plate/netlist pin continuity; precise source claim and selected real circuit.
- **P1/A2** simultaneous V/I/switching clock, capacitor initial/final state, shunts and microphone; do not map 7.8 kHz acoustic to 7.8 Hz Schumann.
- **P2-sourceOperatorSameFilsingerCircuit** independent source voltage/current/admittance under actual load/phase, not chosen "Earth current" parameter.
- **R1/A3/B1–B3-PHYS** same-device nonlinear joint physical inverse explanation of on/hot/null/off.
- **R2/C1–C2** actual 3D Maxwell–ground–ionosphere with causal plasma and Hall/Pedersen/soil/material response, not finite discrete flight alone.
- **R3/C3** environmental positive signed net natural *replenished* work on matched complete cycles; controller/loss accounting and natural driver.
- **D1** pinned Agda 2.9 kernel receipts at exact PR heads (including #1521 and #1524, imports and finite gates).
- **D2** original measurement, source attribution and evidence-tier BIDI, user/Smith/Filsinger/Waker/Tinsley/HAARP correctly distinguished.

## Recommended MAX-CUT order and immediate deliverables
1. **First mathematical cut F05/F06/F07**: promote fixed-source matching square, anti-phase constant aggregate conductance and source-impedance counterexample into exact ordered rational/finite functions in the inherited Agda owners; prove field invariants, test negative controls; no new electrical theory required. Separately F01/F03/F04 phase coherence.
2. **Then F08/F09/F11/F12**: pinned Agda source-work and two-world proof plus matched trajectory repeatability; no false physical claim. Run pinned acceptance for #1521 then #1524, instead of merging source-only modules as kernel complete.
3. **Next F02/F10/F13**: bridge selected full causal distributed Maxwell/memory, natural source admitted parameters, and actual mid-point boundary response. Reuse multirate #1519 only as techniques, do not transplant motor parameters.
4. **Then F14/F15**: source-specific same-original source-to-receiver mechanical/acoustic/electrical and repeatable environmental-work observations. Without these, no physical over-input, solar or atmosphere work promotion.
5. **Last F16**: cloud/rain/cold-pool application only once small control actually perturbs a measured atmospheric field and cloud state in a verified causal model. Keep local cooling real even if global energy budget doesn't change.

## Research references and lineage
- Don Smith original Kelly/Darrer source and Filsinger reel provenance: `Docs/research/DonSmithFilsingerReelsOriginalClaimBidi20261111.md`; `Docs/research/FilsingerDonSmithGoldenRectangleLissajousMaxCut20261111.md`; `Docs/research/SmithFilsingerGoldenFibonacciSingleWaveMaxCut20261112.md`.
- Temporal coupled-mode theory and energy conservation: Zhao/Guo/Fan (2019) https://cguo.org/pdf/zhao2019a.pdf; Wu/Lalanne (2024) https://doi.org/10.1364/OE.517237.
- Source-dependent Earth/ionosphere work and storms: Lukianova et al. (2025) https://doi.org/10.1007/s10712-025-09914-7; Lin et al. (2026) https://doi.org/10.1029/2025GL118532; Tinsley (2023) https://doi.org/10.1175/BAMS-D-23-0065.1.
- HAARP nonlinear retarded current/echo: https://doi.org/10.1029/2011GL049263 and https://doi.org/10.1029/2009JA014610.
- Electric fields and rainfall / natural cold pools: https://doi.org/10.1029/2021GL093577; Kirsch et al. (2021) https://doi.org/10.1175/MWR-D-20-0197.1.
- Infoton source/thermodynamic crosswalk: `docs/research/InfotonP30WalkerMaxCut20261115.md`; no physical Infoton proof used in energy ledger.


## 16 November next max-cut execution: exact finite mathematics committed (NOT Agda kernel checked)
**New owner** `DASHI/Physics/Motors/SmithFilsingerFinitePhaseMatchingExact.agda` reuses existing Nat solver examples (`HydrogenEfficiencyCrossMultiplyExact`) and the existing midpoint signed-port work. No new competing Maxwell/circuit ontology and no changes to ESD or accepted TOE.

| ID | New source-owned concrete certificate | Independent acceptance / limit |
|---|---|---|
| F01 | `commonDriverCrossRatioInvariant`, polynomial equality for a common positive scalar multiplying two Nat channel responses | Algebraic cross-ratio proxy only; full complex phase remains open |
| F04 | `fourPhaseQuadraticCrossCancellation`, exact signed four-phase finite cancellation | Finite 0/90/180/270 phase ensemble, not arbitrary nonlinear or random atmosphere |
| F05 | `sourceMatchSquareGapAbove/Below`, `sourceMatchRationalAbove/Below` | General Nat polynomial square-gap certificate after rational cross multiplication. Positive denominator/physical Thevenin values remain separate |
| F06 | `complementaryConstantTotal`, arbitrary nonnegative finite two-slot conductance complement | Exact discrete version of phase opposition; no physical switch-loss/timing claim |
| F07 | `resistanceOneAntiStrictlyBetter`, `resistanceThreeInphaseStrictlyBetter` | Strict exact rational witness: best phase depends on source impedance |
| F08 | `naturalOffCannotSupplyPositiveNet` | Abstract signed-port source-off impossibility; not independently measured environmental port |
| F09 | Reuse `Midpoint.phaseReadoutAloneCannotIdentifyNaturalWork` | Existing source-authored witness; no duplicate |
| F11 | `matchedWorldsCrossBalance`, additive two-trajectory work equality at shared initial storage | Formal paired-world bookkeeping, not dynamic Maxwell/exogenous-forcing identity |
| F12 | Reuse #1521 `RepeatableSourceReceiverCycle`, `TerminalCapRepeatableCycle` | Do not duplicate on this unmerged branch; same-original replenishment open |

**Exact resistor-phase discriminator** (normalized `V_oc=1`, instantaneous `P(G)=G/(1+R_s G)^2`, two-slot in-phase `G=1/2,3/2`, anti-phase `G=1`):
- `R_s=1`: anti `1/4` versus in-phase `52/225`; exact anti advantage `17/900`.
- `R_s=3`: anti `1/16` versus in-phase `196/3025`; exact **in-phase** advantage `111/48400`.
- For `R>0`, `P_anti-P_in=-R*(3R^3-12R-8)/[(R+1)^2(R+2)^2(3R+2)^2]`. This expression has a single positive crossover in the interval `(9/4,23/10)` (~2.2743). The preferred phase is **source-dependent**, not dictated by 1:1.618 geometry.

**Validation evidence:** independent local exact `Fraction`/SymPy replay **9,112 arithmetic assertions PASS** and receipt at `Artifacts/smith-filsinger/finite_phase_maxcut_exact_receipt_20261116.json`. Code/test entrypoint: `scripts/check_smith_filsinger_phase_maxcut_exact.py`, `scripts/test_smith_filsinger_phase_maxcut_exact.py`. Exact-head Agda 2.9 target: `scripts/check_smith_filsinger_finite_phase_agda29.sh`. The pinned Agda compiler was unavailable in the analysis runtime: **D1 remains OPEN**; do not claim the committed scripts or new Agda were executed at their GitHub head. The independent replay is a separate arithmetic check, not a kernel certificate.

**Updated mathematical-status cut:** F01/F04/F05/F06/F07/F08/F11 have substantially stronger source-authored exact witnesses; F09 reused. They are **not yet pinned Agda accepted**. F02/F03/F10/F12 physical weld/F13/F14/F15/F16 remain as originally scoped. No original-world physical S0/P1/P2/R1/R2/R3/D1/D2 gate is newly closed.


### Latest cross-PR reuse: retarded phases and dynamically replenished source
The finite-Agda proof owner now imports `SmithFilsingerTimeIndexedTransferExact` for two explicitly scheduled paths that arrive at the same clock time after *different launches*. `twoPathsReachSameTime`, `arrivalDoesNotIdentifyLaunchPhase`, `freeRunningDifferentClocksStartAligned`, and `freeRunningDifferentClocksCanSeparate` are finite causal-clock counterexamples for F02/F03. They do **not** establish a physical Maxwell dispersion relation or continuous phase entrainment. This prevents the old error of identifying identical drive-terminal phase with interaction-region phase.

The newly added **#1524** owners `SmithFilsingerReplenishedCycleCapExact.agda` and `scripts/check_smith_filsinger_dynamic_replenishment.py` are independent but directly relevant F12 producers. They were added concurrently; do NOT duplicate their derivation. The continuous model is:
\[
C\dot v = g(V_{\rm up}-v)-G(t)v,\quad U=Cv^2/2.
\]
For *any selected nonnegative time-dependent G(t)* under a fixed positive linear upstream source and a capacitive state,
\[
\underbrace{\int_0^T G(t)v(t)^2\,dt}_{W_{\rm load}}
+\underbrace{U(T)-U(0)}_{\Delta U}
+g\int_0^T(v(t)-V_{\rm up}/2)^2dt
=\frac{gV_{\rm up}^2T}{4}.
\]
The square term is nonnegative; if every store is restored after a periodic cycle, useful load work cannot exceed the fixed linear source's matched terminal cap, and controller costs reduce *net useful* work further. This generalizes the earlier quasi-static source matching bound to the selected finite-memory ODE, **not** to a nonlinear solar/magnetospheric source operator. The new Python method analytically integrates each **piecewise-constant** segment; sampling its sinusoidal branch pattern at segment midpoints is not an exact continuous-sine integration. The `RepeatableSourceCycle` Agda record is a finite Nat conditional source cap, not a proof that the environmental input is naturally replenished. As of this addendum no independent pinned kernel or exact-head Python rerun was obtained.

The physically important remaining contrast: `W_nat` measured at a real terminal must be positive net of reflection and initial donor drawdown, whereas atmospheric solar forcing may change in response to loading. A fixed-voltage Thevenin cap does **not** limit all nonlinear upstream solar source adaptation; it is a falsifiable null model. Full Maxwell/plasma/solar boundary-weld F10/F13/F15 remains OPEN.


## Maximum-cut continuation 2026-11-16: F11/F12 finite replenishment accepted locally

**Current PR provenance:** #1524 adds the tested dynamic-source producer and finite Nat proof consumer to the pre-existing coherent-wave/phase and fixed-DC source interpretation. #1521 remains the owner of the physically distinct Earth/atmospheric/soil source-access estimates and nonlinear constitutive-port work. #1519 (head observed 41fd0c37f8a8b70b73616f1fb75ee3c2c1d9e625) is an independent multirate exact-energy **method donor only**, not original Smith/Filsinger hardware. Existing source owner, finite reservoir owner, signed reflection owner and retarded flight owner are reused.

### Exact outputs and acceptance hierarchy

| Formal item | Strongest completion supported now | What is NOT closed |
|---|---|---|
| F05 fixedSourceMatchGapSquare | Full real algebra identity by square completion; 2026-11-16 passive time integral extends it when the source is fixed | Unrestricted nonlinear/plasma source ceiling; ordered real field Agda theorem |
| F06 complementaryConductanceFlatAtPi | Exact sine anti-phase identity and a constant matched-load stationary solution; the finite-capacitance program demonstrates it again | Original capacitor/switch transistor implementation |
| F07 phaseOptimumDependsOnSourceImpedance | Existing counterexample with other Rs and separately chosen optimum; fixed-parameter periodic source benchmark | Same-original physical optimum |
| F08/F09 signed work/phase nonidentifiability | Earlier Agda source owner, 29/29 locally tested source-equivalent numerical comparisons | Pinned Agda, physical source classification |
| **F11** wholeSystemMatchedTrajectoryDifference | New exact capacitor ODE energy identity and integrated signed natural source/terminal/driver loss; 37 additional Python tests, same-branch phase controls | Actual nonlinear retarded two-world Green/Maxwell; same-device synchronized work |
| **F12** replenishedCycleVsTransientDiscriminator | A new finite-Nat source-authored cancellation proof, cyclic natural+controller bound and independently admitted cap; exact segment-integrated finite source/donor negative controls | Kernel acceptance; physically admitted cap/independent replenishment |
| F13 fullColumnSoilIonosphereAccessWeld | Ideal 1 m² full-column static fixed-source Pmax = 0.1475 µW, 60-s Emax=8.85 µJ | Real plate/earth source operator and geometry/field weld |
| F10 / F14 / F15 / F16 | Producer interfaces plus conditional source-separated research gates | Actual retarded 3D system, original joint hardware, natural repeatable work, weather effects |

New GitHub files:
- DASHI/Physics/Motors/SmithFilsingerReplenishedCycleCapExact.agda
- scripts/check_smith_filsinger_dynamic_replenishment.py
- scripts/test_smith_filsinger_dynamic_replenishment.py
- scripts/check_smith_filsinger_dynamic_replenishment.sh

The **3/3 Git blob SHA comparisons** of producer, 37-case test and Agda module match locally tested source files exactly. Source-equivalent local Python acceptance: **37/37 new; 66/66 targeted aggregate** including the earlier coherent-wave and fixed-DC phase controls. No pinned Agda/Nix executable here. Source-authored finite lemmas are not yet kernel checked.

### Mathematical cut theorem: no depletion means no hidden source

Source access is a selected physical port, not an adjustable parameter. For the **passive fixed linear** upstream voltage source V_s with feed conductance g, controlled load G(t) and finite storage C v²/2:

\[
W_{\rm terminal}=W_{\rm load}+\Delta U,\qquad
\frac{gV_s^2T}{4}-W_{\rm terminal}
=g\int_0^T(v-V_s/2)^2dt\ge 0.
\]

The time integral is independent of how the two internal branch phases are scheduled; **timing can improve matching, not expand the assumed source**. Source-off long-pulse model: Wload ~0.5 and DeltaU ~-0.5, zero natural work. At a genuine periodic full-store return DeltaU=0, useful load <= natural fixed-source matching ceiling. Real device source backaction and changed natural source law (N regime) require a separate physical boundary PDE with correctly attributed external work.

The abstract Nat theorem derives Wload <= admitted Wnat + Wcontroller on repeatable cycles. Its cap receipt is **assumed and explicit**, not inferred from atmospheric fair-weather J or global voltage. The actual Wnat measured for Filsinger remains UNKNOWN.

### Remaining endpoints, ranked by actual original goal (not toy theorem count)

1. **S0/P1 - pinned configuration and simultaneous ports:** original Filsinger Earth circuit vs proposed portable common-midpoint/plate vs Smith patent/editor diagrams remain non-identical. Record source, shunt/rectifier/return pins, real controller current and voltage, capacitor stored-state before/after, acoustic/electrical clocks, load and Earth terminals on ONE selected configuration.
2. **P2 - the decisive physical source operator:** obtain actual under-load port v(t),i(t), two or more external load conditions, signed incoming/outgoing RF or earth conduction, measured driver-controlled phase and matched natural forcing. The global full-column ideal E/J figures are explicitly NOT this receiver's available watts.
3. **R2 - replace fixed g/Vs with 3D physical response:** one causal spatial Maxwell/material/plasma/soil boundary; Poynting, Hall/Pedersen, nonlinear memory, return path, finite propagation and source backaction. Reuse PR #1521 constitutive source, #1519 multirate method if applicable; no speed-of-light or acoustic interpretation inferred from a temporal phasor.
4. **R3 - renewable real work, not depletion:** solve/test matched tuned/control trajectories under same external forcing, with all initial/final local AND source storage, pump, controller, loss, outgoing radiative flux, electrode and chemical potential. A physical same-cycle positive environmental work receipt is mandatory, not merely mathematical source work.
5. **R1 - original startup/hunting/null/pump-off:** one hardware-selected model explains actual acoustic plus synchronous electrical observables; no cross-reel evidence substitution or chosen normalization.
6. **D1/D2 - kernel + actual admission:** run shell wrapper with --agda on pinned Agda host, check exact heads and create authentic same-original source-to-proof weld; do not auto-merge/TOE-promote. No ESD editing.
7. **Q6 - conditional Sun/cloud/rain/local-cooling extension:** requires controller-to-local-electric-field evidence, causal charge-to-droplet-to-rain experiment, local enthalpy/cold pool and separately climate TOA controls. Different goal from positive electrical harvesting and still wholly OPEN as an end-to-end intervention.

**Programme status:** Q1 mathematically advanced and locally tested, pinned kernel still OPEN; Q2 linear finite RC submodel advanced, physical Maxwell remains OPEN; Q3/Q4/Q5 physical apparatus admission remain OPEN; Q6 environmental effects OPEN. The strict original physical gate count remains **0/8**. Reports of conditional models do not change that count.


## 17 November continuation: F10/F13 source/reference/solve (selected-model result)
Read [the new F10/F13 dedicated report](https://github.com/chboishabba/dashi_agda/blob/research/sun-earth-coupled-source-20261116/Docs/research/SmithFilsingerF10F13FieldToPortMaxCut20261117.md). Consumer of the *unmerged* PR #1521 material/Hall/Pedersen and source-admittance owners; no shadow circuit or Maxwell ownership.

* **F10 selected-model symbolic PASS:** passive Debye ADE with time-varying chi, explicit signed controller modulation work and positive tau*Pdot²/(eps*chi) relaxation; time-varying instantaneous epsilon negative-control; Hall zero Joule heating in NEUTRAL frame only; lab-frame neutral-wind energy; Poynting partition with no doubled terminal loss. **F10 full 3D nonlinear retarded source/material solution OPEN.**
* **F13 selected exact Laplace benchmark PASS:** Phi(r)=V*a/r for hemispherical equipotential contact in isotropic homogeneous half-space, G=2*pi*sigma*a; geometry-distinct ideal disk boundary G=4*sigma*a; independent 1D stratified tube R=H*(1-exp(-h/H))/(A*sigma0). No claim these are an exact generic 3D atmosphere/soil/ionosphere solution. **F13 real source impedance/effective aperture/ionospheric operator OPEN.**
* Prior citation correction: A. Tip (1998) is **Phys Rev A 57, 4818**, `10.1103/PhysRevA.57.4818` (“Linear absorptive dielectrics”); Wu & Lalanne (2024) title is *Exact Maxwell evolution equation of resonator dynamics: temporal coupled-mode theory revisited*.
* Local independent selected-model verifier **14/14 pytest PASS**; committed checker added to `scripts/check_smith_filsinger_dynamic_replenishment.sh`. No exact-head Agda compiler run, no calibrated Filsinger measurements. F15/R3 and rain-cooling F16 OPEN.
* Crucially, the environmental-power steelman is a **dynamic Sun/Earth source**, possibly ample enough to pay MW pump expenditure if physically transferred. The passive half-space Thevenin matched-load example is a **null** not a bound on solar-wind Poynting flow or nonlinear, source-responsive, spatially distributed power.


## 2026-11-17 source-first Maxwell value-of-information cut (F10/F13-F16)

**Full detailed source/verification record:** [SmithFilsingerMaxwellValueAndSourceFirstCut20261117.md](SmithFilsingerMaxwellValueAndSourceFirstCut20261117.md). New exact-head code, tests, original missing-evidence schema and conditional acceptance runner are on PR #1524.

**Highest alpha decision:** calibrated source-to-terminal work precedes a large 3D Earth/ionosphere Maxwell model. Spatial Maxwell/plasma is worth implementing after one selected apparatus has authentic geometry/materials, loaded natural-source response and a physical anomaly which a reduced DC/1D/port law cannot explain. It cannot produce a measured natural generator by choosing a boundary amplitude. Acoustic 7.8kHz is not an electrical phase measurement.

| Target | New restricted result | Strict remaining original-world wall |
|---|---|---|
| F10 / R2 | Exact symbolic local vector Poynting + nonlinear time-varying polarization + Hall/Pedersen/neutral-wind + generator signed work; 8/8 tests | Full calibrated causal Maxwell/plasma/soil/material source operator |
| F13 / P2 | Crowley 2011 Eq.25,28–37 isolated spherical fair-weather collector physics; 2m/0.1m conditional example ~0.1483 nW, 2.97 pA and 6.74e13 Ω; unit/model negative controls | Actual Filsinger electrodes/plate source identity and voltage/current geometry; no global 250kV assigned locally |
| F14 / R1 | Original-load-only energy balance rank 1/nullity 3; drive, natural supply and donor depletion counterworlds indistinguishable at load | Original actual pin graph, simultaneous driving/source/shunt/load/switch, acoustic waveforms and one parameter set |
| F15 / R3 | Conservative signed v*i interval receiver; requires independent source identity and full stored-state return; passing external flags is not an empirical receipt | Positive independently replenished natural work at selected original port over whole cycles |
| F16 / Q6 | Two causal models give identical natural electric-field/rain observations but differing controlled effect; 2021 paper establishes observational relation only | Actual controller→cloud electric-field transfer, causal rain/drizzle response and local cooling with controls |
| D1/D2 | 4/4 Git blobs parity; 33/33 new tests, 99/99 combined local source-equivalent tests | Pinned Agda kernel, original-world evidence admission and same-head CI |

**Source correction:** Crowley calls pi*d² a sphere's geometric cross section while defining d as diameter; physical projected disk is pi*d²/4 (fourfold convention discrepancy). Eq.28 Isc, Eq.35 R and Eq.37 Pmax do not change. Neither Crowley sphere nor earlier 1D slab are measurements of Filsinger's actual grounded/portable collector. Source: https://electrostatic.com/research/c11theatmos/c11atmo.html, 2026 Borok https://doi.org/10.1016/j.asr.2026.01.090, 2021 cloud raindrops https://doi.org/10.1029/2021GL093577, Tinsley https://doi.org/10.1029/2021JD035954.

**Execution:** scripts/check_smith_filsinger_source_first_maxcut.sh; 99 local targeted model tests **PASS**, all four new code/test blobs byte-identical to branch, no exact-branch CI nor Agda proof checker. No original same-unit physical gate is closed. All S0/P1/P2/R1/R2/R3/D1/D2 remain **OPEN (0/8)**. Retain W/B/N source regime distinctions and source-qualification; no ESD edits and no premature TOE promotion. F16 does not authorize weather intervention or indicate local/global cooling gain.


## 17 November correction: genuine Agda F10/F13/F14/F15/F16 welds

**Previous work was numerical/pytest modelling, not the requested formalisation.** The new proof-based analysis and actual Agda source signatures are in [SmithFilsingerFormalWeldMaxCut20261117.md](SmithFilsingerFormalWeldMaxCut20261117.md). This update supersedes the previous simulation-focused emphasis for formal gate tracking.

**New Agda consumer** DASHI/Physics/Motors/SmithFilsingerSourceMaxwellBoundaryWeldExact.agda imports and explicitly connects the existing MaxwellExteriorCalculusAdapter, TimeIndexedTransfer MemberState/RetardedFlight, ReflectedPortBidi original-source config, SunEarthCoupledSource port/regime, MidpointPhaseWork signed incident/outgoing real-work port, FinitePhaseMatching source-off and complementary-phase theorems, and ReplenishedCycleCap original stored-state cycle. Dependent SourceOwner prohibits swapping Smith compiled, filmed Filsinger Earth and proposed Filsinger portable hardware. FormalFieldToPort connects the original member and symbolic curvature carrier to one source-qualified boundary without claiming that the Maxwell source/Hodge PDE is solved.

**Genuine derived F15 lemma:** signedPortBalanceAfterFullStoreReturn, by exact Agda Nat semiring normalization plus cancellation, deduces natural net incoming + controller net incoming = useful load + loss from TWO original signed incident/outgoing laws, original MidpointTwoPortWorkWindow conservation, and full store return. The equality is NOT assumed as a second independent cycle law. signedNaturalAndControllerWorkPaysSamePortLoad instantiates this result; signedPortLoadBoundAfterStoreReturn bounds the very same load; sourceCapTransfersToSameOriginalPort transports an independently admitted natural-access cap through an exact port-identity witness. Source-free natural input cannot yield positive net natural work; finite flight does not arrive before launch.

**New Agda consumer** DASHI/Physics/Motors/SmithFilsingerCloudCausalWeldExact.agda explicitly preserves observed-natural-association evidence tiers for the electric field/raindrops and cold-pool papers; composes same-source controller-to-cloud, cloud-to-droplet, droplet-to-rain and rain-to-local-cold-pool arrows as conditional typed evidence; proves observationalCloudRainAssociationDoesNotWeld via observationally identical worlds with distinct intervention effects. Global climate promotion is separately conditioned, and original source-specific F14 acoustic/electric regime demands its own evidence.

**Acceptance boundary:** Agda proof source committed, but no Agda/Nix compiler is available in this session and NO kernel acceptance is claimed. scripts/check_smith_filsinger_formal_weld_agda29.sh is the pinned type-check target. Earlier 99/99 Python tests are irrelevant to kernel acceptance. The symbolic Maxwell adapter remains explicitly unpromoted: complete physically sourced 3D R2/F10, calibrated original source F13/P2, original combined F14/R1, sustained original-work F15/R3 and actual cloud causation F16 are PHYSICAL OPEN. No ESD edits and no premature TOE import.


## 17 November: nonlinear carrier / causal admittance / finite-source max-cut continuation
**Implementation:** [SmithFilsingerNonlinearRetardedSourcePortMaxCut20261117.md](https://github.com/chboishabba/dashi_agda/blob/research/sun-earth-coupled-source-20261116/Docs/research/SmithFilsingerNonlinearRetardedSourcePortMaxCut20261117.md), `scripts/check_smith_filsinger_nonlinear_retarded_source_port.py`, `scripts/test_smith_filsinger_nonlinear_retarded_source_port.py`. Existing original-world `source_first_original_evidence_contract_20261117.json` is not modified; separate *model-only* schema receipt added.

**F10-PLASMA conditional:** Electron continuity with independent pair-creation, attachment and recombination rates; `U_ion=Vch Epair n`, explicit paid ion-pair creation, ionisation loss, controller auxiliary input, and finite electronic channel resistance. Exact algebraic power/storage cancellations are model identities, and symbolically checked. This does not prove a complete air-plasma chemical/thermal/ion inventory (F10-3D OPEN).

**F13-RET selected:** Positive-real Foster trial port with signed Debye and Lorentz state energies and dissipations. This is a *surrogate* for an unknown waveguide impedance, not a fitted 3D Maxwell/soil/ionosphere Green operator; positive real excludes *passive* negative dissipation for state-returning cycles, not externally energized nonlinear source response.

**F13-NL selected:** `G_series=Gch Gext/(Gch+Gext)`. Channel `Gch∝n` may change substantially without raising the composite series limit beyond `Gext`. Cubic toy `I(V)=G0 V+γ V³` gives `Gdiff=G0+3γV²` versus `Gpower=G0+γV²`; different quantities.

**Finite source backaction:** Added finite upstream capacitor state `Cs Vs'=g_recharge*(Vexo(t-delay)-Vs)-I`. Natural signed replenishment, receiver load, exterior/channel heat, ion creation/loss, controller auxiliary input and all final storage tracked. The static external source is now an explicit *causal exogenous forcing of a finite reservoir*, not a fictitious fixed infinite battery. It remains a conditional 0D/1D nonlinear analogue and does NOT incorporate ionospheric Hall/Pedersen geometry or upstream Sun–Earth magnetospheric power.

**100× gain metric:** model reports `Wload/(Wcontroller+Wion_pair_creation)` and threshold; **neither sufficient nor a source validation** without actual source power, *every* pump cost (plasma thermal, chemistry, bridge), complete return cycle, error bars and physical source admittance.

**R2/R3/F15 physical frontier remains OPEN:** exact 3D soil/air/ionosphere Maxwell, fitted electron/ion kinetics, independently measured real source work under source backaction, controller+bridge losses and fully restored repeatable cycles. No original-world gate passed. The full committed test suite has no exact-head replay/kernel receipt in this runtime; selected SymPy identities were independently verified.

**Caution:** Externally sourced solar power could be orders of magnitude above fair-weather local-collector power, but only a causal interface with a source-supported phase/current/aperture and measured reservoir replenishment can establish that for the actual device.


## 17 November second Agda cut: internal Maxwell/material work-port cancellation

The current formal maximum cut is **not a simulation**. New owner DASHI/Physics/Motors/SmithFilsingerMaxwellMaterialEnergyCutExact.agda proves a generic shared-interface cancellation and composes two independently witnessed, same-original field-source and material-receiver work laws. It explicitly retains net natural-source input (not gross incoming waves), net driver work, paid material modulation, recovered modulation, electromagnetic/radiative loss, dissipative material loss, field storage and material storage.

The Agda source provides cancelSharedInterface, fieldMaterialCombinedWork, fieldMaterialRepeatableWork, fieldMaterialLoadBoundOnRepeatableCycle, netNaturalUnderExistingAdmittedCap, and sameOriginalMaterialCapWithControllerAndModulator. The resulting *conditional* selected-load inequality is: useful original load <= independently admitted net natural cap + net powered controller work + explicitly paid material modulation. This cannot hide material work in a purported external source or count field/material interface flux twice.

Original physical Poynting/current and nonlinear material conservation identities are still uninhabited physical hypotheses. The separate #1521 DispersiveMaterialPortExact donor is not present on #1524's branch; avoid a fake import and perform exact cross-branch join after the source trees converge. Full F10/R2 Maxwell, F13/P2 source operator, F14/R1 original history, F15/R3 replenished natural work, F16 actual cloud intervention remain OPEN.

Pinned Agda acceptance script scripts/check_smith_filsinger_formal_weld_agda29.sh now targets **three** formal modules; **Agda/Nix unavailable here**, so none of the new source-authored proofs is claimed kernel-checked. Full detailed signature/proof dependency in SmithFilsingerFormalWeldMaxCut20261117.md.


## 17 Nov Agda direct donor-to-field/material typed weld

The original #1521 canonical DispersiveMaterialPortExact.agda source has been *reused byte-for-byte unchanged* on #1524: same Git blob fb4039927678b370f359b3151c1fc2a2286c33ab on both branches. All extensions are in new DASHI/Physics/Motors/SmithFilsingerDispersiveMaterialWeldExact.agda, which imports the actual donor, not an abstract surrogate or numerical simulation.

The new Agda proofs derive originalDispersiveRepeatableWork from the existing MemoryMaterialPortLedger.fullBalance with **environment and material storage individually restored**, then prove originalDispersiveLoadBound. CanonicalDispersiveSameObject ties the donor's natural recharge to **net** natural work, driver work, paid modulation, returned modulation, real load, field+material loss, and all four initial/final source and material storage identities on one selected original configuration. donorOriginalLoadBelowAdmittedNaturalCap proves the donor's same-original load cap. Crucially, donorStorageReturnTransfersToSplit derives the split full-store return from donor receipts and matched storage states; canonicalDispersiveFieldLoadBelowNaturalCap instantiates the F10 field/material shared-work cancellation and resulting F15 bound **without re-assuming storage restoration**.

**Formal acceptance:** pinned script check_smith_filsinger_formal_weld_agda29.sh now includes FOUR new proof consumers and the original material donor; no Agda/Nix executable is available here, so source-authored theorems are NOT yet kernel checked. Physical F10/F13/F14/F15/F16 original-world gates remain OPEN and no empirical natural source is fabricated.


## 17 November maximum-cut — distributed finite-source / plasma topology (latest)

**New executable owner:** `scripts/check_smith_filsinger_distributed_causal_energy.py`; regression `scripts/test_smith_filsinger_distributed_causal_energy.py`; source/acceptance evidence `Docs/research/SmithFilsingerDistributedEnergyMaxCut20261117.md` and `Artifacts/smith-filsinger/distributed_source_plasma_maxcut_20261117.json`. Integrated into existing `scripts/check_smith_filsinger_dynamic_replenishment.sh`. No ESD changes or new parallel theorem graph.

**Completed selected-model mathematical cut:** N-node finite LC/telegrapher analogue, N−1 link-current energy, finite rechargeable source storage, causal delayed stipulated exogenous source waveform, carrier number/ion pair energy, source feed/line/bridge/load resistive loss, signed recharge work and paid ionization/controller energy. All interior link powers cancel by exact discrete telescoping; SymPy identity checked for N=3,5,8 and local **16/16 tests PASS**. The continuous semidiscrete ODE is NOT a strict light-cone Maxwell PDE.

**Adversarial source-connected control:** For the same carrier amplification ~4.29×, a plasma *shunt* reduced delivered load by ~2.25%; a plasma *series link* increased load by ~110.31% under its own stated parameters. This establishes **topology matters**. Neither configuration produced net useful work after assumed ion creation + controller cost, and source/storage failed full return. No sustainable natural harvest or original Filsinger netlist identity is claimed.

**F10 remaining:** Formal all-N induction, real Maxwell 3D space/matter/Hall/Pedersen/neutral-wind and complete plasma chemistry, plus physical effective moving channel interface. **F13 remaining:** measured conductor/collector topology and effective source-connected input admittance; actual causal soil/atmosphere/ionosphere Green operator (not fitted from our synthetic source); nonlinear return path and replenishment. **F15/R3 remaining:** independently verified net natural source work over source-restored matched repeated cycles after all bridge/ion/thermal/controller costs; 100× benchmark assessed only then. F14 original integrated regime and F16 cloud/cold-pool causal link remain distinct OPEN.
 
**Next high-alpha tranche:** (1) promote finite spatial telescoping energy and source ownership into the pre-existing Agda Maxwell/source port graph, with pinned kernel check; (2) construct selected field-to-port operator subject to actual source/geometry data, nonlinear series-vs-shunt interpretation and causal time-phase transfer; (3) source-backed same-original sustained-cycle acceptance; (4) conditional atmospheric branch. No amount of symbolic algebra can supply missing original P1/P2 measurement.


## 17 November — all-N spatial work plus retarded-time Agda weld (latest)

**Source and exact proof surface:** [SmithFilsingerSpatialRetardedAllNFormalMaxCut20261117.md](SmithFilsingerSpatialRetardedAllNFormalMaxCut20261117.md). New canonical consumers:

- `SmithFilsingerSpatialPortChainExact.agda`: `SpatialCell`, dependent `SpatialChain`, `spliceSharedWork`, `spatialChainWorkBalance` **for all finite N**, `spatialLoadBoundedByAdmittedInputs`, `sourceFreeSpatialChainHasZeroLoad`; concrete two-cell witness. No duplicate Maxwell source.
- `SmithFilsingerTimedSpatialPortChainExact.agda`: reuse canonical `RetardedFlight`, all-N `allTimedPathsArriveAfterLaunch`, `timedSpatialEnergyConservation`, two-flight 1→3→7 witness. Finite causal clock ≠ Maxwell light-cone proof.
- `SmithFilsingerSpatialSourceBoundaryWeldExact.agda`: SOURCE-INDEXED `SpatialToOriginalSourcePort` uses original `SelectedBoundary` / `FormalFieldToPort`, requires original physical field-to-port input AND output work identifications; derives matching selected original-port law from all-N cells. Missing measurements remain explicit, not silently constructed.

**Execution:** local **900/900 independent exact integer finite-chain checks PASS** (N up to 64); earlier local **16/16 distributed LC/plasma tests PASS**. Added `scripts/test_smith_filsinger_spatial_chain_exact.py` to existing `check_smith_filsinger_dynamic_replenishment.sh`, and the three new Agda owners to existing `check_smith_filsinger_formal_weld_agda29.sh`. **No exact-head GitHub combined run or pinned Agda 2.9 verification**; D1 OPEN. The reported 900 checks are an independent arithmetic replay, not compiler-proven.

**Gate movement:**
- F10 *finite spatial algebra*: all-N Agda proof candidate source authored, no pinned kernel. **F10 actual nonlinear 3D Maxwell/material/Hall–Pedersen R2 OPEN.**
- F02 finite causal time: source-authored all-N ordered flight. **Physical phase at interaction region and retarded Green operator OPEN.**
- F13 original source: stricter same-source indexed boundary work interface; **actual solar/soil/ionospheric impedance, geometry, full wave Maxwell solution P2 OPEN.**
- F15/R3: existing finite-source matching/replenishment gating intact; **independently measured source work over fully restored cycles OPEN**.
- User's steelman retains arbitrary source size and possibility of large pump expense where independently measured source work dominates; the source-free and finite-donor counterexamples stay in acceptance.

**Next highest-alpha physical route:** pinned kernel first, then selected actual source/geometry/terminal waveform identification, causal Maxwell material port with independent natural-source boundary and full return. Avoid using random finite-chain receipts to stand in for original astrophysical power access. No ESD edit or unverified TOE promotion.


## 17 November proof-only continuation: KSW full-vector Poynting and all-N timed spatial cap

**Source-first Agda REUSE and exact formal welds; NO simulation.** The programme now consumes KSW668FullVectorMaxwellJetExact.fullVectorMaxwellPoyntingIdentity: a three-vector, full-curl **pointwise** source theorem. SmithFilsingerFullVectorPoyntingPortWeldExact.agda requires an **independently certified physical spacetime/surface integration and source/terminal identification** before transporting pointwise conservation into an original natural/driver/source cap. The function selectedSourceFullVectorMaxwellCap is indexed by the existing original SignedSourceCycleWeld natural NET work and independently admitted source cap; no arbitrary gross incident wave or 250kV global column is substituted for the measured source.

SmithFilsingerSpatialSourceCapWeldExact.agda additionally imports original SpatialPortChainExact and TimedSpatialPortChainExact: spatialChainNetSourceWork proves that all internal directed transfer terms cancel for arbitrary many cells if full-chain storage returns; selectedOriginalAllSpatialCellsBelowNaturalCap transports the net natural source and controlled work to the original useful load; allTimedSelectedOriginalCellsBelowNaturalCap and allTimedSelectedOriginalArrivalIsCausal preserve the energy cap and launch<=arrival on timed paths. Discrete causal clocks are NOT physical Maxwell fronts.

**New signed material audit** materialModulationReconcilesOriginalCycleLoss derives old same-port internal loss + paid material modulation = field outgoing loss + material dissipation + recovered modulator work by equating the TWO independent restored-cycle laws and cancelling identical useful load. This prevents silent reclassification or double-counting of internal material work as independent environmental gain.

**Status:** source-authored mathematical proof candidates; no pinned Agda compiler or GitHub exact-head CI receipts in the current environment, so D1 kernel OPEN. Full F10 physical Maxwell existence/constitutive integration, F13 original source access/geometry, F14 original waveforms, F15 physically replenished real-work and F16 causal cloud evidence remain OPEN. The existing Maxwell 3-vector theorem closes its narrower pointwise abstract domain only. Further highest-value work is physical integrated Poynting → original calibrated terminal identification or pinned kernel elaboration; not a duplicate Maxwell PDE or synthetic power simulation. Existing originals preserve attribution and all ESD surfaces are unchanged.


## 17 Nov integrated full-vector Maxwell to timed all-N source-bound Agda weld

New mathematical, NON-simulation owner DASHI/Physics/Motors/SmithFilsingerMaxwellTimedSpatialWeldExact.agda composes original KSW 668 three-component Maxwell curl-jet Poynting theorem with the *existing* discrete causal flight and all-N spatial energy chain. Each dependent MaxwellTimedPath cell is required to supply its own physically justified Poynting-to-CausalSpatialCell integration map; eraseMaxwellToTimedSpatial applies the actual original vector identity cell-by-cell, preserving the selected original source b, its field/receiver f, and signed replenished-work cycle s. All links share the same boundary identity and correctly cancel interior work; no unmeasured source energy is inserted.

Proof endpoints: allIntegratedMaxwellCellsConserveWork, allIntegratedMaxwellCellsRespectFlight, allIntegratedMaxwellCellsBelowSelectedNaturalCap. The final theorem applies the original-source natural NET input cap to an arbitrary-length timed source/receiver path with fully restored energy stores and source/driver/load identity. The finite-flight proof is not a continuous relativistic light-cone or a physical device timing measurement.

Also tightened the full-vector independent admission: SameOriginalPhysicalFieldBoundary now carries actual typed equations for Maxwell pointwise→physical terminal work, material constitutive work, complete storage return and same-original load rather than freely chosen evidence Set labels. selectedFullVectorPhysicalAdmissionCap consumes those equations. Cross-ledger materialModulationReconcilesOriginalCycleLoss prevents hiding separately paid modulator power inside natural source inflow.

**Open wall:** actual continuum/piecewise-integrable Maxwell/plasma/soil current solution for selected original electrode and source geometry, valid surface/time Poynting→work per-cell witnesses, independent source/replenishment and original time-synchronous work evidence, and pinned Agda/Nix kernel acceptance D1. Source-authored theorem candidates and exact Git commits do NOT imply Agda proof acceptance. No simulation, ESD edit or false TOE promotion.

Full source and verification levels: [SmithFilsingerFormalWeldMaxCut20261117.md](SmithFilsingerFormalWeldMaxCut20261117.md).


## 17 November next maximum-cut: arbitrary finite-volume mesh / Yee CFL / source-indexed Maxwell boundary

**New source/reference/solve:** [SmithFilsingerFiniteVolumeYeeGreenMaxCut20261117.md](SmithFilsingerFiniteVolumeYeeGreenMaxCut20261117.md).

**New Agda source owners:**
- `DASHI/Physics/Motors/SmithFilsingerFiniteVolumeFaceIncidenceExact.agda`: any finite list of cells with independently supplied local work equations; `sumPairDistributes`, `foldLocalConservation`, all-cells conservation; one shared face-work list with aggregate incoming/outgoing incidence receipts; derive `finiteVolumeExteriorEnergyBalance`, load upper bound, source-off zero-load, and branching examples. Unlike the earlier `SpatialChain`, these cells can form cycles/branches. This is an exact finite mesh work theorem candidate, not a PDE or a fully face-ID indexed Stokes proof. **Per-face/per-cell ID incidence and real signed flux quadrature remain OPEN.**
- `SmithFilsingerFiniteVolumeMaxwellBoundaryWeldExact.agda`: `meshAsCanonicalSpatialCell` and `meshAsCanonicalSpatialChain` consume face theorem, normalize singleton chain sums and use existing `SpatialToOriginalSourcePort` to derive selected historical source-boundary equality. The original physical input/output work mapping is explicitly still demanded, not generated from pointwise Maxwell algebra.
- `SmithFilsingerYeeCFLConeGuardExact.agda`: exact 1D-Courant counterexample demonstrates CFL stability does NOT entail physical `distance <= c*time` support. A separate physical-cone admission record remains obligatory. 3D Yee `c dt <= dx/sqrt(3)` is a stability constraint, not `c dt >= dx` or a proof of front velocity.

**Acceptance:** independent exact integer replay **512/512 arbitrary directed finite meshes PASS**, N up to 32; script `scripts/test_smith_filsinger_finite_volume_face_incidence_exact.py` added to existing consolidated `check_smith_filsinger_dynamic_replenishment.sh`. The three new Agda owners were added to the existing `check_smith_filsinger_formal_weld_agda29.sh`. **Not executed:** pinned Agda kernel, full latest-head combined pytest, original physical field measurements.

**Next lemmas (honest technical gaps):**
1. F10-INC `eachInternalFaceUniqueOppositeOrientation`: per-cell face-ID assignments and exact 1-to-1 outgoing/incoming face pairing, not just aggregate equality; then signed vector-flux additive cancellation in the existing C3 carrier.
2. F10-STOKES `fullVectorJetIntegratedCellBalance`: pointwise real-field Maxwell jet + verified spatial/time Stokes discretization + matching field/material/ion loss and controller work yields each local real-valued energy law. No fake Nat-quantization of physical work.
3. F02-CONE `physicalRetardedGreenSupport`: prove/support kernel vanishes outside actual light cone using chosen Maxwell/material constitutive assumptions; numerical Yee CFL alone insufficient, cross-time magnetic energy positivity separately tested.
4. F13-PORT `selectedTerminalPoyntingEqualsMeasuredVI`: actual field contour, Ampere with displacement current, return topology, field cross-section and synchronized VI identification; do not infer current from H circulation alone.
5. F13-GREEN `soilAirIonosphereDyadicResponse`: source-backed causal background Green/operator with anisotropic Hall/Pedersen, nonlinear plasma active-region response and source backaction.
6. F15-SOLAR `independentSolarWorkPaysFullCycle`: original independent source net work with restored material/source/receiver states, modulation/ionization/bridge costs and positive useful net. 100x requires measured gain/cost lower bounds, not a symbolic label.
7. D1 exact-head pinned Agda 2.9 module acceptance and full source regression.

**Max-cut prioritization:** the pure mathematical next closure is **F10-INC** on explicit face IDs, then C3 signed-flux cancellation; the physical blocker is **F13-PORT/GREEN** calibration, without which field power can be misidentified. The steelman permits a very large independently powered solar reservoir; no passive fair-weather local-R calculation or uncalibrated simulation fixes access to that reservoir. No ESD edits.


## 17 November F10b finite open-boundary Poynting Gauss max-cut

**Formalisation/weld continuation; not simulations.** A cross-programme search found an exact, already authored rational forward-flux telescoping theorem in DASHI/Physics/YangMills/YangMillsLatticeStressWardSliceConservationExact.agda. It is now imported by the new DASHI/Physics/Motors/SmithFilsingerOpenBoundaryPoyntingGaussExact.agda, which proves finiteOpenBoundaryPoyntingGauss for x/y/z **cross-section-aggregated** rational face fluxes. Signed exterior right-minus-left flux is retained rather than incorrectly canceled as for periodic faces. This algebra is not a claim of continuous 3D Maxwell divergence or original current.

The new originalFullVectorJetOpenBoundaryFlux composes the canonical KSW668FullVectorMaxwellJetExact pointwise Poynting theorem and the canonical YM finite Gauss proof, with **independently required** field/time integration into rational face flux and physical face/source terminal trace. The latter two are precisely the still-open physical Maxwell/source current witnesses, not arbitrary simulated sources.

The N-cell MaxwellTimedPath producer was tightened: it no longer requires a function giving an already-constructed CausalSpatialCell. Its IntegratedFieldCell requires the signed local work equality, and buildCausalCellFromMaxwell **constructs** the actual timed energy cell from the KSW proof plus the admitted integration. A second IntegratedOpenGaussCell / throughOpenGauss construction uses the stronger KSW→YM open face flux result and requires explicit signed rational-flux-to-Nat original port calibration. All existing all-N spatial source-cap and causal arrival proofs apply to either constructor.

**D1 source integrity repair:** a structural scan found and fixed a missing closing parenthesis at SmithFilsingerMaxwellMaterialEnergyCutExact.fieldMaterialRepeatableWork. The prior ineffective regex hole checker was fixed; actual local bash fixture results clean ACCEPT, Agda hole REJECT, postulate REJECT, unsafe pragma REJECT (4/4 source-guard fixtures). Source delimiters rechecked in all three edited formal modules. These are NOT Agda kernel checks; no Agda/Nix executable is accessible here. Pinned check_smith_filsinger_formal_weld_agda29.sh now targets the open-Gauss module and its YM donor explicitly.

**Strict remaining gates:** F10 actual Maxwell/plasma field PDE, domain orientation and physically justified spatiotemporal face integration; F13 signed source terminal and environmental replenishment; F14 original electrical/acoustic matched waveform; F15 real full-state return and independent natural work; F16 causally measured cloud/rain/cooling; D1 actual pinned Agda compiler acceptance. No ESD edit, attribution preserved, no TOE promotion.


## 17 November next max-cut — F10-INC signed indexed face theorem and full-vector sample

[Full source/reference/solve record](SmithFilsingerIndexedSignedFiniteStokesMaxCut20261117.md).

**New Agda sources** (source-authored; pinned kernel OPEN):
- `SmithFilsingerIndexedFaceIncidenceExact.agda`: strict unique cell IDs, unique face IDs, distinct per-face source/target, exactly-once incidence even with zero-work faces, per-cell physically directed work. Crucially **derives** weighted source/target work receipts from incidence counts with `sumMarkedWeight`/`sumMarkedOnce`, proves finite Fubini swap, then feeds the original `FiniteVolumeFaceIncidenceExact` owner without duplicating its energy theorem. This closes the mathematical **aggregate face spoof** from the previous round at source level. Source-off and load upper bounds reused.
- `SmithFilsingerIndexedFaceSourceWeldExact.agda`: consumes the existing original source-indexed `OriginalFiniteVolumeAdmission` and requires the historic physical mesh to equal the strict indexed mesh. Physical port-current integration still OPEN.
- `SmithFilsingerSignedIndexedFaceFluxExact.agda`: all-N signed `C3.RealField` source/target face-pair cancellation with true additive inverses.
- `SmithFilsingerIndexedSignedCellStokesExact.agda`: derived all-N **per-cell signed** oriented-face sum zero, using precisely indexed endpoint counts, signed field-valued finite Fubini, and existing ring structure; no assumed aggregate signed equality.
- `SmithFilsingerFullVectorIndexedFaceSampleExact.agda`: actual KSW668 3-vector Maxwell jet and explicit cross-product `n·(E×B)` sampled flux, formal normal sign reversal and source/target face-pair cancellation. A sampled face is not a calibrated space-time Poynting integral.

**Independent local mathematical replay:** 512/512 strict indexed finite graphs; 512/512 rational per-cell signed face cancellations; 1,000/1,000 exact rational vector normal reversals PASS. New three Python regression owners added to the existing consolidated runner. Five new Agda owners added to existing pinned checker. **No exact-head combined pytest, no Agda 2.9 kernel execution, no measured physical same-original port.**

**Updated open gate sequence:** F10-INC *conditional finite graph and signed ring proof authored*, D1 pinned kernel OPEN; F10-STOKES real field-to-volume+time integrals and physical material/conductivity response OPEN; F02 physical retarded Green light cone OPEN; F13 original environmental admittance and electrode/return `V,I` OPEN; F15 independent replenishment positive net after full bridge/controller/ion thermal losses OPEN; F14/F16 original electrical/acoustic and rain/cooling causal chains OPEN. Strict source-first evidence remains untouched, no ESD edits or unjustified TOE promotion.

**Cross-lane reuse:** concurrent `SmithFilsingerOpenBoundaryPoyntingGaussExact.agda` already imports the Yang–Mills finite difference telescope and closes a finite rational rectangular exterior boundary identity. The new indexed finite-mesh theorem handles the complementary internal face-ID/signed source-target cancellation; connect them via a licensed continuous field/quadrature map rather than identifying their carriers by name.


## 17 November F15 signed reverse-port formal cut

The prior Nat source-cap proof assumes **nonnegative** environmental NET work (incident = outgoing + admitted natural work). The original physical source can instead be a SINK (outgoing > incident), so that assumption cannot be used universally.

New source-authored Agda owner DASHI/Physics/Motors/SmithFilsingerSignedBoundaryGroupCompletionExact.agda imports the EXISTING MidpointTwoPortWorkExact complete incident/outgoing ledger. It defines signed work via cross-sum equivalence of incoming/outgoing Nat pairs, proves reflexivity, symmetry, transitivity, additive inverse cancellation and addition congruence, and derives originalTwoPortSignedWorkConservation after full store return WITHOUT presuming naturally positive net input.

Most importantly, reverseEnvironmentalFlowConsumesControllerWork establishes that when naturalOutgoing = naturalIncident + environmentalReturn and controllerIncident = controllerOutgoing + controllerNet, then controllerNet = usefulLoad + internalLoss + environmentalReturn. reverseEnvironmentalLoadPlusSinkBelowController and originalReverseEnvironmentalPortFundedByController give the same-original bound usefulLoad + environmentalReturn <= controllerNet. The canonical earlier driverOnlyCanRadiateIntoEnvironment record supplies an exact proof witness (driver net 2, useful load 1, environmental output 1). This is a formal negative control, NOT a simulation or the original Filsinger apparatus.

Source-first dedup audit: newer concurrent #1524 SignedIndexedFaceFluxExact / IndexedSignedCellStokesExact already provide actual C3.RealField signed face cancellation; SpaceTimePoyntingTelescopeExact provides rational four-direction signed finite conservation. Reuse them as mathematical field owners. Nat signed-pair is only the work-meter/completion interface; do not pretend a quotient, natural source, or real physical SI calibration has been built. Cross-carrier field-to-meter calibration remains a separate physical F10/F13 gate.

Pinned Agda checker includes the new source and rejects any Agda goal-hole opener; four local guard fixtures passed. Agda/Nix executable remains unavailable; no kernel PASS. The physical F10 continuum source/current/integration, F13 source admission, F14 original electrical/time waveform, F15 replenished real work, and F16 causally controlled weather remain OPEN.


## 17 Nov continuation — F10-STOKES rational four-direction space–time weld (latest)

**Source/reference/solve:** [SmithFilsingerSpaceTimePoyntingStokesMaxCut20261117.md](SmithFilsingerSpaceTimePoyntingStokesMaxCut20261117.md).

**New proof sources:**
- `SmithFilsingerSpaceTimePoyntingTelescopeExact.agda` reuses the original `YangMillsLatticeStressWardSliceConservationExact.differencePartialTelescopes` time identity and `SmithFilsingerOpenBoundaryPoyntingGaussExact.finiteOpenBoundaryPoyntingGauss` spatial identity. Under an **explicitly supplied** finite local energy-work law, it derives the exact rational `ΔU + net signed exterior Poynting + material/ion loss + useful work = separately provided volume natural/control work` for four finite axes, without periodic exterior assumptions or Nat energy rounding. `DisjointExteriorPowerPartition` prevents double counting environmental energy simultaneously as exterior input and as natural volume source; `DecomposedSpaceTimeWork` retains individual Ohmic, ADE, ion chemical, modulation, ion pump, electrical driver and neutral-wind work. `SameOriginalSpaceTimeMaxwellAdmission` consumes the existing `OriginalMaxwellOpenFaceTrace` and KSW668 jet while demanding the still-unproved field integration/terminal identification.
- `SmithFilsingerSelectedSpaceTimePortWeldExact.agda` indexes the rational trace by the **same** historical `SelectedBoundary b` and `FormalFieldToPort b`, requires an additive quantized Nat→rational work calibration and contentful equalities for original natural incident/outgoing, controller incident/outgoing, receiver load and initial/final stored energy. It does NOT construct real source data or identify Smith suitcase vs Filsinger original vs proposed portable geometry.

**New regression:** `scripts/test_smith_filsinger_space_time_poynting_telescope_exact.py` integrated into existing combined Python acceptance; two new Agda owners added to `scripts/check_smith_filsinger_formal_weld_agda29.sh`. **800/800 independent exact Fraction four-direction windows PASS**, with source-off depletion, omitted-cost and wrong-face-sign negative controls. This is independent arithmetic replay, **not** exact GitHub-head pytest nor Agda kernel. D1 OPEN.

**Priority:** (1) pinned kernel acceptance; (2) actual Maxwell global field + surface/time quadrature and ADE/ion medium law yielding the finite local work equation (not just admitting it); (3) licensed indexed arbitrary-face-ID → rectangular rational exterior Gauss mesh equivalence; (4) physical retarded causal Green (not CFL); (5) original calibrated source/collector/return `V,I` plus natural source backaction; (6) restored-cycle F15/R3 energy and F14/F16 regime/atmosphere tests. All physical original-world gates remain OPEN, and large controlled solar transfer remains a conditional steelman rather than an observation.


## 17 November F10/F13 terminal quantisation obstruction and signed sink cut

Continuing exact formalisation rather than simulation, the new SmithFilsingerSignedBoundaryGroupCompletionExact.agda now proves signed-work cross-sum equivalence, additive inverse cancellation and addition congruence for the original incident/outgoing terminal carrier. Its reverseEnvironmentalFlowConsumesControllerWork proves controllerNet = usefulLoad + loss + reverseEnvironmentalWork when the environment is a NET sink; originalReverseEnvironmentalPortFundedByController gives usefulLoad + reverseEnvironmentalWork <= controllerNet on the selected original port. The canonical owner driverOnlyCanRadiateIntoEnvironment supplies exact nonvacuous driver-only negative controls (2 controller work, 1 load, 1 environmental return).

The broader C3.RealField signed indexed-face owner, indexed-cell Stokes theorem and rational SpaceTimePoyntingTelescopeExact were found already present in the branch. Do NOT duplicate them with a new signed field algebra. Instead, the Nat pair is a **pre-quotient terminal work-count representation**, and a calibrated signed real-field-to-terminal observation remains the missing F10/F13 physical bridge.

Formal **quantisation negative control** oneWorkQuantumHasNoExactSignedHalf proves by Nat induction that no integer signed pair doubled can equal one unit of signed work. Therefore an EXACT globally additive, nonzero mapping from arbitrary divisible rational/real field energy into integer Nat work quanta cannot be assumed. Physical integration must either retain native signed field/rational work until a justified discrete lattice is specified or carry measured/rounding uncertainty as certified intervals through the all-N source conservation weld.

The pinned formal Agda checker includes the signed module; local exact source guard tests passed clean/hole/postulate/unsafe (4/4), but this is not type-checking. No Agda/Nix kernel receipt or real original source admission has been obtained. F10 physical Maxwell field/trace/integration, F13 original source admittance, F14 electrical-acoustic same-object observations, F15 measured replenishment and F16 causal atmosphere remain OPEN. No ESD edits or TOE golden promotion.


## Exact additive meter no-go under a half-divisible source carrier

**New source-authored formal consumer:** DASHI/Physics/Motors/SmithFilsingerSignedMeterQuantisationNoGoExact.agda. It imports the canonical SignedBoundaryGroupCompletionExact signed Nat-pair pre-quotient, the original oneWorkQuantumHasNoExactSignedHalf theorem and the existing MidpointTwoPortWorkExact contradiction owner. It does NOT create a new real-field or sign-flux algebra.

Theorem additiveExactMeterCannotSendHalvedUnitToOneQuantum is universe-polymorphic in any source carrier A with an operation plus, a half element h, a full element u and exact h plus h = u. If an integer signed-pair meter respects the source operation via cross-sum equivalence AND maps the full element to one integer quantum, its value at half would have to be half an odd integer, contradicting the original exact Nat-pair parity theorem. This is a formal argument against an unrestricted EXACT nonzero additive C3.RealField/rational -> integer-quanta bridge; it is NOT a theorem against approximate meters or discrete finite-lattice models.

The actual physics lane should use the existing C3.RealField indexed signed face algebra and rational SpaceTimePoyntingTelescopeExact source carriers, preserving the field metric, source-current and integrated Poynting identity. For comparison with Nat terminal energy, a future *independently calibrated* metering map must either have a declared discrete domain/quantum lattice or bounded interval/rounding uncertainty with summed error. Such a map has not yet been constructed and may fail to exist for the original device.

A GitHub update race was resolved by creating a **separate proof consumer**, avoiding overwrites in the signed boundary owner. The pinned script now lists the consumer. Agda/Nix remain unavailable locally, so all new proof bodies remain pending kernel type-check; no physical F10/F13/F14/F15/F16 source/weather claims are promoted.


## 17 November F10-STOKES next cut: explicit travelling Maxwell field / energy face proof

The latest proof/negative controls are in [SmithFilsingerSpaceTimePoyntingStokesMaxCut20261117.md](SmithFilsingerSpaceTimePoyntingStokesMaxCut20261117.md).

**New original-field consumer:** `SmithFilsingerPlaneWaveSpaceTimeWitnessExact.agda` uses the EXISTING canonical rational C3.RealField and the KSW668 3D Maxwell derivative jet. For `E_y=B_z=a+b(x−t)`, `J=0`, it authors the Faraday and Ampere equalities, delegates pointwise Poynting to KSW668, proves `n_x·(E×B)=U=A²`, the characteristic `A(x,t+h)=A(x−h,t)`, and exact sampled cell work `ΔU+S_right−S_left=0`. Its explicit `FiniteSpaceTimeWindow` consumer applies `SpaceTime.spaceTimeExteriorEnergyBalance` rather than assuming that global work identity separately. This gives a NONCONSTANT, algebraically exact travelling-wave *bounded-domain sample* witness. A globally affine plane wave is not finite energy; actual physical Maxwell spacetime quadrature and atmospheric materials remain OPEN.

**Independent equivalent Fraction replay:** 1,200/1,200 travelling-wave rational characteristic/energy-cell checks PASS; earlier 800/800 four-direction rational work-window checks PASS. Wrong travel stride, omitted ion-creation/controller cost, false double counting of natural boundary inflow as a volume source, source-free donor depletion and wrong exterior-face orientation are adversarial controls. New test owners included in the existing Python acceptance. Three new Agda targets (4-direction, selected-original port calibration and concrete plane wave) included in the pinned formal checker. No actual Agda 2.9 kernel or latest-head combined Python suite execution here. No original P1/P2/R2/R3 experimental gate is closed.

**Next high-alpha:** (1) D1 actual pinned proof checker, (2) a locally finite-energy/compact-support Maxwell field and mathematically licensed SI space-time integral/constitutive law (ADE, plasma and neutral-wind energy), (3) per-face-indexed 3D signed real work / rational rectangular open exterior correspondence, (4) F02 causal retarded Maxwell–Hall/Pedersen source Green operator, (5) same-original electrode/ground V,I and independent replenished solar work F13/F15, (6) F14 physical original phase/instrument and F16 causal atmosphere/cooling. Treat local linear fair-weather high resistance only as a passive negative control, not a universal constraint on a dynamically driven external source.


## 17 Nov signed rational terminal meter error: certified upper and lower Agda consumers

**Exact source-first cross-programme reuse:** DASHI/Core/ProofCarryingFiniteSumEnclosureExact.agda, already used by the RH programme, provides the canonical proof-carrying finite-sum error and upper-bound eliminator. The Filsinger programme now imports it directly. It does not reimplement interval algebra or simulate a circuit.

New source-authored DASHI/Physics/Motors/SmithFilsingerCertifiedSignedMeterResidualExact.agda: certified rational residuals and original meter readings share identical finite term identities; signedResidualsTelescope proves aggregate physical work = measured work + aggregate signed rational error by the original ring normaliser, not by quantisation to Nat. SelectedOriginalCertifiedMeter requires physical matching to the SAME original finite SpaceTimePoyntingTelescopeExact receiver window and actual observed meter reading. originalUsefulReceiverEqualsMeterPlusResidual and originalSignedResidualBelowCertifiedUpper derive the selected receiver identity and the canonical certificate's upper error bound. SignedMeterUpperMonotonicity / originalReceiverBelowObservedPlusCertifiedResidual transport to actual original work <= measured + certified error upper.

New DASHI/Physics/Motors/SmithFilsingerCertifiedSignedMeterTwoSidedExact.agda: consumes an independent canonical proof-carrying certificate for the NEGATIVE residual and a contentful exactOppositeErrorSum identification linking both sides to the SAME original aggregate error value (not necessarily a termwise sample match). Under verified rational order monotonicity/sign inversion laws, twoSidedOriginalReceiverLower/Upper derive: observedWork - negativeErrorUpper <= originalUsefulReceiverWork <= observedWork + positiveErrorUpper. This is the valid answer to the earlier exact-integer half-quantum obstruction: keep rational signed energy until the explicitly bounded residual is accounted for, then optionally quantise with a separate justified metering lattice.

Strict F10/F13 physical field-to-actual-original-terminal calibration, error certificates, actual source admission, F14 electrical/acoustic original clock, F15 sustained independently replenished source, F16 weather causality remain OPEN. Both files are in the pinned Agda checker; no local Agda/Nix compiler or kernel receipt is available (D1 OPEN). Local source-level delimiter/no-hole scans are NOT equivalent to compiler acceptance. No ESD edits or TOE golden promotion.


## 17 November F02/F13 Green reuse — source-first answer to “repo has Green”

See [SmithFilsingerGreenOwnerReuseMaxCut20261117.md](SmithFilsingerGreenOwnerReuseMaxCut20261117.md). Repo search confirms **actual existing exact mathematical Green** in `BalabanFiniteCoerciveGreen` (general inverse and coercive norm), `BalabanSide4ScalarGreenConvolutionExact` (literal exact 4D periodic scalar inverse with mean correction), plus broader finite gauge Green-decay owners. **These are static elliptic/gauge Green kernels, not the material layered *retarded dyadic Maxwell* Green operator needed to establish solar-energy access.**

**New reuse-only formal consumers:**
- `SmithFilsingerCoerciveGreenRetardedWeldExact.agda`: original finite coercive inverse and reciprocal norm certificate; source-author `retardedGreen` with exact pre-delay zero and at-delay inverse/source0. Stamped absolute-clock version reuses `RetardedFlight.launch + flight = arrival`, with strict no-pre-arrival result even for nonzero launch. The same-original physical admission is strengthened from empty evidence tokens to concrete measured launch source identity, full physical-operator = chosen Green equality, calibrated signed original terminal useful work and natural incident/outgoing net-work equality, with explicit measured distance/front bound. The arrival field and original work equalities follow by *transport of these admitted facts*, not measurement inference.
- `SmithFilsingerPeriodicGreenDelayReuseExact.agda`: actual `scalarGreen` convolution from the canonical side-4 periodic torus; delayed readback and genuine `siteGreenLaplacianIdentity` transfer with the mandatory `−(1/256)Σf` constant-mode correction. This is an exact inverse response with stipulated time delay, NOT a hyperbolic causal source Green.

**Independent arithmetic:** 327/327 exact Fraction time-delay / nonzero-launch / inverse / coercive-bound checks PASS for positive diagonal finite 2×2 operator. New test suite included in existing consolidated Python runner; both Agda sources added to pinned checker. **No Agda kernel or exact-head full CI receipt**, physical source Green and real original devices still OPEN.

**Next cut:** D1 pinned compiler; physical F02 causal Maxwell dyadic Green and true support; F13 layered soil–air–ionosphere, full nonlinear/material constitutive interface and source-to-collector calibrated `V,I` including displacement current; F10 spacetime signed indexed face work; F15 restored independently replenished net after all control/plasma/thermal cost; F16 weather causality separate. Green reuse is a mathematical advance, not a claim of original power gain.


## 17 November five requested gates: evidence acceptance and pinned kernel route

The user requested completion of F10 physical Maxwell-to-original terminal calibration, original measurements/error certificates, F15 sustained natural-source replenishment, F16 atmospheric causality and D1 Agda kernel checking **all at once**. The exact source-first audit of the locally available original archive yielded **0/24 original raw evidence roles** across those five categories (F10 0/6, METER 0/3, F15 0/5, F16 0/6, D1 0/4). Therefore **no scientific physical gate can honestly be closed**. Do not infer impossibility from missing data, and do not invent source currents, electrical currents, controlled weather or calibrated certificate magnitudes.

New concrete accepted work, not another physical simulation:

1. **D1 focused CI route**: `.github/workflows/filsinger-agda29-acceptance.yml` adds a true Agda 2.9 Nix-pinned PR kernel check and failure-log artifacts, separate from the historical manual-only Agda 2.6.4.3 CI. It pins the exact upstream experimental stdlib source commit `008f12c2908479567a3ae3c873f9cf0b8fe5987e`, and the compiler comes from the repository's flake-locked `.#agda29-parallel`. `scripts/check_smith_filsinger_formal_weld_agda29.sh` was deduplicated (41→39 owners, 30→28 new-owner targets) while preserving all distinct proof modules. This is a **kernel acceptance route**, not a PASS: no exact-head workflow run or successful Agda elaboration exists at this writing.
2. **Original-evidence guard**: `scripts/check_smith_filsinger_original_gate_evidence.py` with 10 adversarial `scripts/test_smith_filsinger_original_gate_evidence.py` tests. Negative controls reject absent data, other apparatus IDs, model/proxy receipts, duplicate role claims, absent sampling clocks, path escape and raw-file hash mismatch. All 10 local tests PASS. The checker *never* declares a physical claim or kernel proof closed, even with complete hash-matched metadata, because raw bytes/metadata do not verify an SI calibration or causal treatment effect. New detailed role contract: `Docs/research/SmithFilsingerFiveGateEvidenceAcceptance20261117.md`.
3. **No fake scientific closure:** full-vector Poynting mathematics, rational signed port accounting and certified finite-sum interval consumers remain conditional formal work. **F10 physical** requires original pin geometry, material/ground/source-current, field flux and synchronous VI trace; **METER** requires independent calibration, clocked raw VI and signed residual bounds; **F15** requires actual net natural-source work and full repeated state restoration after controller and material losses; **F16** requires preregistered randomized intervention, sham/negative controls, meteorological covariates, replication. None is established by a symbolic Maxwell theorem, a modelled sphere/slab, filmed sound or GitHub mergeability.

Highest-alpha next action is to collect/verify the actual original instrument/current and calibration receipts and obtain an Agda CI/kernel PASS. There is no rigorous way to produce those five physical results from the present repository alone. Keep all five scientific gates OPEN; treat the evidence checker and CI workflow as infrastructure, not evidence.


## 17 Nov F13 / F15 / D1 user-directed SymPy max-cut

[Full source-first exact reduced layered Green / restored-cycle / SymPy limits](SmithFilsingerF13F15SymPyMaxCut20261117.md).

**F13 computational producer:** scripts/smith_filsinger_layered_green_sympy.py implements C e''+(P+H)e'+K e=J_env+J_control for three soil/air/ionosphere layers, two transverse polarizations each, positive Pedersen term and antisymmetric Hall term; k_parallel² exact Fourier dependence. G(s,k²)=[s² C+s(P+H)+K(k²)]^(-1). Exact 6x6 inverse, reverse-Hall transpose, positive symmetric part, nonzero model source-to-sensor response and exact implicit midpoint work law. New scripts/test_smith_filsinger_layered_green_sympy.py covers **25/25 source-equivalent independent exact SymPy cases PASS**, including four in-plane k² modes. This is *reduced transverse* finite model with rational fixture parameters, NOT calibrated full 3D dyadic Maxwell, actual physical distance/cone or historical environmental power.

**F15 formal consumer:** SmithFilsingerHundredfoldSourceFundingExact.agda imports restored-cycle law and derives that any stipulated 100x load and losses must be paid by natural+controller work; example 100 natural, 1 controller, 100 load, 1 loss with restored stores is a hypothetical algebraic witness only. SymPy exact work audit is fail-closed on missing independent measurements, storage depletion, double-counting, work mismatch. Interval lower-bound test rejects nominal 100x when load lower 100 and controller upper 1.1, requiring instead load_lower >=100 controller_upper.

**D1 independent verifier:** scripts/check_smith_filsinger_sympy_gate.py runs exact SymPy and scans relevant Agda source interfaces, but its status ALWAYS reports Agda kernel NOT_RUN and D1 OPEN. New F15 Agda source attached to actual scripts/check_smith_filsinger_formal_weld_agda29.sh; new SymPy test attached to scripts/check_smith_filsinger_dynamic_replenishment.sh. No pinned Agda/Nix in runtime, no actual kernel receipt; exact-head full Python suite not run. SymPy cannot establish Agda typing/coverage/termination. Do not claim otherwise.

**Remain OPEN** F13 full 3D retarded anisotropic Maxwell dyadic & source/receiver calibration; F15 independently metered replenished same-original natural work with all costs and full restoration; D1 pinned Agda 2.9 kernel; downstream F14/F16 empirical system and atmospheric causal claims. These are physical/verification prerequisites, not arbitrary additional finite symbolic lemmas.


## 17 November F13 addition: 4x4 tangential Maxwell layer transfer

[Full F13/F15 SymPy report](SmithFilsingerF13F15SymPyMaxCut20261117.md). Added exact planar Fourier Maxwell 4x4 tangential [E_x,E_y,H_x,H_y] generator with Hall off-diagonal dielectric terms, normal H_z/E_z elimination, and a three-layer Cayley spatial transfer product. Verified **7/7** independent exact SymPy tests including real Maxwell curl ODE identities, layer transfer inverse and determinant at 3 wave numbers, three-layer tangential continuity and cross-polarization. Combined local source-equivalent mathematical suite **32/32 PASS** (25 finite six-state layer + 7 four-component Maxwell transfer).

**Still OPEN:** continuum exp(M d) and correct outgoing eigenmode/radiation termination; full 3D dyadic and the physical k_perp integral; anisotropic Hall/Pedersen/parallel conductivity with geomagnetic tilt; finite-speed retarded causal Green under nonstationary nonlinear plasma; actual electrode/return source-to-terminal V,I; independent solar source replenishment. 4x4 transfer here is the rational Cayley approximation, not an actual measured field propagator. D1 pinned Agda kernel still OPEN; exact SymPy math is not an Agda proof.


## Continuation: F10/F15 signed raw VI interval transport and independent receipt guard

**Implemented original-data reader, not numerical simulation:** `scripts/check_smith_filsinger_signed_vi_intervals.py` consumes five actual source/return/receiver V/I ports on the SAME original ID, identical rational time grid and sampling clock, checks SHA256 and explicit signed orientation, and integrates conservative exact-Fraction V·I intervals under the explicitly DECLARED piecewise-linear POWER/trapezoidal sampling assumption. It returns natural incident-minus-outgoing, net controller, useful load and unassigned losses/storage-change interval, retaining sign and two-sided voltage/current error radii. It has no permission to claim independent natural-source replenishment, original Maxwell field calibration, all storage restoration, or final physical truth; positivity is at most a **conditional arithmetic interval**.

New `scripts/test_smith_filsinger_signed_vi_intervals.py` contains 13 source-authored exact arithmetic/negative-control tests: signed V/I products and differences, exact half trapezoid, five-port conservation arithmetic, wrong clock, duplicate port bytes, bad hashes, misaligned sample grids, negative uncertainty radii, unknown port orientation, incomplete port roles, non-string floating-point inputs, repeated timestamps. Wired into focused PR CI. **Do not claim a local test PASS until actually executed.**

The prior original evidence role checker now rejects reusing the same file or identical SHA256 content for multiple independent roles. `scripts/test_smith_filsinger_original_gate_evidence.py` gains two adversarial controls (12 test methods total) and a role-distinct test fixture. Exact raw file identity, origin, sampling and calibration remain separate from physically demonstrated independent environmental work. One valid file cannot automatically satisfy all F10/METER/F15/F16/D1 receipts by being relabelled.

All five physical/kernel science gates still OPEN. In particular a positive conditional V/I integral is NOT a proof that the source was natural, independently replenished, or atmospheric; and a source-authored Agda theorem is NOT D1 kernel acceptance until the pinned compiler actually checks it. F16 requires randomized meteorological intervention, not simply an electric field / rain association.


## 17 November — outgoing planar Maxwell source-sheet Green and F15 negative controls

[Detailed exact source/boundary derivation and limits](SmithFilsingerOutgoingRadiationGreenMaxCut20261117.md).

**New F13 consumer:** `scripts/smith_filsinger_radiation_green_sympy.py` reuses the existing 4×4 tangential Maxwell three-layer transfer. Explicit outgoing homogeneous halfspace admittances impose an upper and lower open-wave boundary. A specified tangential current sheet at the upper boundary enforces the correct `R(H_inside-H_outside)=J_sheet` jump. The resulting finite-scheme source-to-bottom/upper electric Green map is an exact 2×2 Schur/boundary inverse with separately returned magnetic field traces; no fictitious source. The lossless Hermitian Hall fixture satisfies exact conserved tangential Poynting `T† F T=F`, including Hall-induced cross polarization. The sheet-source work is exactly outward Poynting plus slab absorption; for lossless tested slabs absorption is zero.

**Evanescent extension:** distinct mathematically exact lossless decaying branch `q_z=+i sqrt(k²-ω²με)` for strict `k²>ω²με`; reactive evanescent field is nonzero but has *zero real outward power* and cannot be sold as F15 energy. Propagating and evanescent branch cutoffs fail closed.

**Verification:** previous 32 exact reduced-layer and tangential Maxwell SymPy tests plus 11 outgoing radiation/source/evanescent and source-free tests: **43/43 local exact pytest PASS**, committed test suite integrated with existing `check_smith_filsinger_dynamic_replenishment.sh` and `check_smith_filsinger_sympy_gate.py`. No pinned Agda kernel run or exact-GitHub-head combined suite. Existing dedicated Agda CI workflow was found; the queried latest-commit workflow/status API returned no kernel receipt.

**Remaining** F13 full 3D *retarded dyadic* including 2D transverse Fourier inversion, absorbing/complex spectral radiation branch, actual geomagnetic conductivity tensor, source backaction and original electrode/ground V,I; F15 measured independent solar-attributed replenished work and fully restored cyclic losses; D1 actual pinned Agda typecheck of source module graph. Do not promote passive slab Green source response to actual solar harvesting, and do not infer a Maxwell light-cone theorem from a finite Cayley spatial transfer.


## 17 November continuation — 51/51 source-equivalent SymPy checks for oblique F13 Maxwell Green

[Full implementation report](SmithFilsingerOutgoingRadiationGreenMaxCut20261117.md). The mathematical F13 producer now includes both the exact restricted planar outward source-sheet Green (propagating and separately guarded evanescent lossless branches) AND an arbitrary `k_x,k_y` spectral Maxwell **4×4** tangential generator with full 3×3 complex permittivity and tilted Hall gyrotropy, maintaining E_z/H_z longitudinal constraints. The source-to-sensor response is derived from the actual Maxwell current-sheet interface jump and outgoing halfspace conditions; lossless Hermitian Hall slab flux is conserved under the finite Cayley transfer, and no-source/no-exterior-work cannot fund a 100x load. Finite source-by-boundary work `W_sheet=Φ_out+Q_slab` is tested for nontrivial cases.

Combined independent exact SymPy/Python suite **51/51 local PASS** (32 previous + 11 outgoing/evanescent/F15 controls + 8 fully oblique/tilted Hall). All four owner tests included in the consolidated Python runner and explicit SymPy gate. The existing real Agda CI workflow is present but latest-head kernel PASS has not been observed; D1 remains OPEN. Green and finite source sheet results are strict **mathematical fixture** results, not measured Filsinger apparatus or independently replenished solar power.

**Next highest-alpha original physical blockers:** calibrated frequency-dependent *absorbing* soil/air/ionosphere `σ_parallel,σ_P,σ_H`, correct complex spectral radiation/branch and entire 2D Fourier inversion to a causally supported physical 3D retarded dyadic; terminal/gap E/H plus conductor+displacement current return identification; source-backaction/replenishment and signed meter intervals; kernel typecheck of existing Agda proof graph (not SymPy substitution). Physical F13/F15 and D1 remain OPEN.


## 17 Nov continuation — conditional same-original Maxwell-to-meter bound weld and alias-error admission

**Source-first proof weld (NOT another Maxwell simulation):** `DASHI/Physics/Motors/SmithFilsingerOriginalMaxwellMeterIntervalWeldExact.agda` directly consumes the EXISTING `SmithFilsingerSelectedSpaceTimePortWeldExact`, `SmithFilsingerCertifiedSignedMeterTwoSidedExact`, the canonical `ProofCarryingFiniteSumEnclosureExact`, original `KSW668FullVectorMaxwellJetExact` and 4D space-time Poynting owners. Its `OriginalMaxwellMeterIntervalWeld jet b f` record demands a two-sided proof-carrying meter certificate indexed by the **same selected Maxwell `physicalTrace.window`**, preventing a separately chosen meter interval from masquerading as this original apparatus. It authors `originalMaxwellReceiverUpperFromSignedMeter`, `originalMaxwellReceiverLowerFromSignedMeter` and `originalCalibratedPortUpperFromSignedMeter` via equality transport, with no independent aggregate conservation assumption.

**Critical numerical acceptance correction:** the earlier exact-Fraction V/I integrator bounded only pointwise sampled meter calibration and set intersample energy error to zero. Switching and pulsed waveforms make that unsafe. `scripts/check_smith_filsinger_signed_vi_intervals.py` now **requires** `integration_error_bound_J` (nonnegative exact rational string), `integration_error_certificate` (different file from all port CSVs and other certificates), and `integration_error_certificate_sha256` for **each** of the five ports; it changes the trapezoid work interval `[L,U]` to `[L−ε,U+ε]`. This is a conditional data check, not a derivation or scientific validation of ε. An asserted ε=0 is admissible to the parser ONLY with an independently archived certificate, and is not automatically physically justified. Five regression test methods now exercise this gap; V/I suite contains 18 authored tests, evidence-inventory suite contains 12 authored tests.

**D1:** new Agda consumer added to both `owners` and `new_owners` of `scripts/check_smith_filsinger_formal_weld_agda29.sh`. No Agda 2.9 kernel check was executed successfully in this session, and the tests are source-authored rather than observed passing runs. The 2.9 pinned CI route exists in the PR, and should be run before this new module is treated as a theorem. Original Maxwell terminal field calibration F10, actually measured and independently bounded SI work, repeated-source replenishment F15, controlled weather intervention F16 and D1 kernel PASS remain OPEN.

**Pareto next cut:** obtain original clock-synchronous, signed, calibrated instrument traces and validated intersample/phase error certificates; apply the new meter-weld to that selected original `jet/b/f` only; do not infer atmospheric output or unmetered natural supply from a symbolic electromagnetic identity. ESD surfaces unchanged.


## 17 Nov F13 max-cut — passive complex exterior, finite Fourier/Parseval, 68 exact checks

[Implementation, derivation and gate boundary](SmithFilsingerPassiveFourierGreenMaxCut20261117.md).

**F13 source reuse extended**, without another Green ontology:
- `scripts/smith_filsinger_passive_radiation_sympy.py`: positive-frequency passive complex exterior with selected outgoing/decaying `q=sqrt(ω²με−kx²−ky²)`, explicit sign/branch admissibility checks. Exact Maxwell 4×4 **Cayley passivity matrix identity** `T†FT−F=d (I−dM/2)^−†(M†F+FM)(I−dM/2)^−1`; absorbing layer fixture proves `M†F+FM=diag(−1,−1,0,0)`, so no artificial field-work creation. Nonzero sheet-source work is separated into positive outgoing flux plus strictly positive slab absorption. Active, uncertified and branch-point cases fail closed.
- `scripts/smith_filsinger_periodic_fourier_green_sympy.py`: **actual finite 2D inverse Fourier** across four 2×2 periodic source modes using the existing oblique Maxwell sheet Green at each k. Exact mode orthogonality, source-to-position field reconstruction, and **Parseval-correct power** `(1/4)Σ_x Re(E*J)/2 = Σ_k Re(Ehat*Jhat)/2`. Deliberately omitting the finite transform normalization falsely multiplies work by 4 and fails. This is NOT the infinite-plane 2D spectral integral or a physical length-calibrated/causal dyadic.

**Acceptance:** 10 new exact passivity/absorption/negative tests + 7 exact finite Fourier/Parseval tests = 17 new; **68/68 independent exact local SymPy pytest PASS** including the previous 51. Both added to the existing consolidated Python and standalone SymPy gate. Added separate `.github/workflows/filsinger-sympy-exact.yml` with pinned Python 3.12, SymPy 1.14 and pytest 9.0.2 and a fail-closed `Agda NOT_RUN/D1 OPEN` check. Existing true pinned Agda 2.9 CI is preserved, **kernel success still unobserved**. Do not count SymPy CI as an Agda proof.

**Open physical gates:** F13 true full 3D retarded, dispersive, causal soil–air–ionosphere dyadic (actual complex conductivity, spectral analytic branch, inverse Fourier/time support), calibrated physical collector/return and source backaction; F15 real independently replenished natural work across *restored* cycles with calibrated signed meters and robust uncertainty; D1 pinned Agda kernel result; F14/F16 original physical/atmospheric causal endpoints. These cannot be certified by a finite source-sheet fixture. No ESD edits, user-origin solar-source hypothesis attribution preserved.


## 17 Nov continuation — causal passive Lorentz ADE/material Maxwell and restored-cycle 112 exact checks

[New source-first F13/F15 implementation report](SmithFilsingerLorentzADEMaxwellGreenMaxCut20261117.md). This reuses the pre-existing dispersive material, KSW668 Poynting, Green, oblique Maxwell spectral and same-original restored-cycle owners.

**F13:** Exact rational n-cell Maxwell E/H + auxiliary material polarization P/V with real damping, finite curl/transposed-curl and separately paid useful-load conductance. Implemented actual implicit midpoint source-driven state and established exact total `delta U + W_useful + Q_ohmic + Q_Lorentz = W_natural + W_controller`, including material kinetic and potential storage, without a free material parameter pump. Exact underdamped Lorentz impulse is zero for pre-source time, has stable left-half-plane poles, solves the ODE and matches its Laplace susceptibility `alpha/(s²+gamma*s+omega0²)`. This is *material temporal causality*, not a 3D Maxwell front theorem.

**Same-owner frequency weld:** `epsilon_eff(s)=epsilon_inf+sigma/s+chi(s)` feeds the EXISTING oblique Maxwell generator and passive complex outgoing branch. For positive phasor frequency, `omega Im epsilon_eff=sigma+(gamma/alpha)omega²|chi|²` equals precisely the time-domain Ohmic plus relaxation terms; no second spurious conductivity loss.

**F15:** A consecutive-history synthetic cycle audit checks restoration of all E/H/P/V components; an exact nontrivial five-step closed field/material cycle delivers positive receiver load with its hypothetical source current paying all positive losses. It explicitly returns `original_source_meter_present=False` and `physically_replenished_source_certified=False`. A zero-source transient donor, omitted receiver branch and nonconsecutive history fail the corresponding tests.

**Verification:** prior 68/68 exact Green suite + 44 new material/time/frequency/restored-cycle checks = **112/112 exact local pytest PASS**, SymPy 1.14.0 / pytest 9.0.2. New tests wired to the existing consolidated Python runner and independent SymPy CI/gate. No exact-head Agda kernel success observed and no original VI/source measurements provided. **Physical F13, measured F15, Agda D1 all remain OPEN.**

**Next:** physical layered spatial retarded Maxwell dyadic and causal front; same-original measured source/environment + collector/return displacement current; environmental source backaction and full-state restoration after controller/material expense; pinned Agda 2.9 acceptance. Standard source-first attribution and no ESD edits.
